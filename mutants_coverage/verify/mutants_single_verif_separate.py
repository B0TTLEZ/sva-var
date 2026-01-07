import argparse
import json
import logging
import os
import re
import shutil
import signal
import subprocess
import sys
import traceback
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Tuple, Optional
from tqdm import tqdm

# ============================ 全局配置与日志设置 ============================
def setup_logging(output_dir: Path):
    """设置日志配置，同时输出到文件和控制台"""
    log_dir = output_dir / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"mutants_assertion_verif_{timestamp}.log"

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(log_file, encoding="utf-8"),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return log_file

# ============================ 解析sv_files.txt ============================
def parse_sv_files_txt(sv_files_loc: Path) -> List[Path]:
    """
    解析sv_files.txt，返回按顺序排列的文件路径列表（过滤注释/空行）
    :param sv_files_loc: sv_files.txt路径
    :return: 绝对路径列表
    """
    if not sv_files_loc.exists():
        logging.error(f"sv_files.txt不存在: {sv_files_loc}")
        sys.exit(1)
    
    sv_files = []
    with open(sv_files_loc, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            # 过滤注释（//）和空行
            line = line.strip()
            if not line or line.startswith("//"):
                continue
            # 转换为绝对路径
            file_path = Path(line).resolve()
            if not file_path.exists():
                logging.warning(f"sv_files.txt第{line_num}行文件不存在: {file_path}")
            sv_files.append(file_path)
    
    if not sv_files:
        logging.error(f"sv_files.txt中未找到有效文件路径")
        sys.exit(1)
    
    logging.info(f"解析sv_files.txt完成，共{len(sv_files)}个文件")
    return sv_files

# ============================ 找到变异模块对应的原始文件 ============================
def find_original_module_file(sv_files: List[Path], mutant_module: str) -> Optional[Path]:
    """
    在sv_files列表中找到变异模块对应的原始文件（匹配模块名+后缀sv/v）
    :param sv_files: 原始文件列表
    :param mutant_module: 变异模块名（如i2c_master_bit_ctrl）
    :return: 匹配的文件路径，未找到返回None
    """
    # 匹配规则：文件名包含模块名，且后缀是.sv/.v
    pattern = re.compile(rf"{re.escape(mutant_module)}\.(sv|v)$", re.IGNORECASE)
    for file_path in sv_files:
        if pattern.search(file_path.name):
            return file_path
    # 宽松匹配：路径中包含模块名且后缀是.sv/.v
    for file_path in sv_files:
        if mutant_module in file_path.name and file_path.suffix in ['.sv', '.v']:
            return file_path
    logging.warning(f"未找到模块{mutant_module}对应的原始文件")
    return None

# ============================ 【新增】在FT目录中查找顶层模块文件（含变异体版本） ============================
def find_top_module_file_in_ft(ft_dir: Path, top_module: str) -> Optional[Path]:
    """
    专门在ft目录下查找顶层模块文件，优先匹配变异体版本（如i2c_master_top_mutant.sv）
    :param ft_dir: ft目录路径
    :param top_module: 顶层模块名（如i2c_master_top）
    :return: 匹配的文件路径，未找到返回None
    """
    if not ft_dir.exists():
        logging.error(f"FT目录不存在: {ft_dir}")
        return None
    
    # 规则1：优先匹配 顶层模块名 + _mutant + .sv/.v（变异体版本）
    mutant_pattern = re.compile(
        rf"{re.escape(top_module)}_mutant\.(sv|v)$", 
        re.IGNORECASE
    )
    for file_path in ft_dir.iterdir():
        if file_path.is_file() and mutant_pattern.search(file_path.name):
            logging.info(f"在FT目录找到顶层模块变异体文件: {file_path.name}")
            return file_path
    
    # 规则2：匹配 顶层模块名 + .sv/.v（原始版本）
    original_pattern = re.compile(
        rf"{re.escape(top_module)}\.(sv|v)$", 
        re.IGNORECASE
    )
    for file_path in ft_dir.iterdir():
        if file_path.is_file() and original_pattern.search(file_path.name):
            logging.info(f"在FT目录找到顶层模块原始文件: {file_path.name}")
            return file_path
    
    # 规则3：宽松匹配 - 文件名包含顶层模块名且后缀是.sv/.v
    for file_path in ft_dir.iterdir():
        if (file_path.is_file() and 
            top_module in file_path.name and 
            file_path.suffix in ['.sv', '.v']):
            logging.warning(f"FT目录未找到精准匹配的顶层文件，使用宽松匹配: {file_path.name}")
            return file_path
    
    logging.error(f"FT目录{ft_dir}下未找到任何与顶层模块{top_module}相关的.sv/.v文件")
    return None

# ============================ 复制文件到ft目录并替换变异体 ============================
def copy_files_to_ft(
    ft_dir: Path,
    sv_files: List[Path],
    mutant_module: str,
    mutant_file_path: Path
) -> List[Path]:
    """
    复制所有需要的文件到ft目录（与rpt/tcl同级）：
    1. 复制sv_files中的正常文件到ft_dir（保留原文件名）
    2. 复制变异体文件到ft_dir（保留原文件名）
    3. 替换列表中原始模块文件路径为变异体路径
    :param ft_dir: ft目录路径（输出目录/模块/变异体/Rank_X/ft）
    :param sv_files: 原始文件列表
    :param mutant_module: 变异模块名
    :param mutant_file_path: 变异体文件路径
    :return: ft目录下的文件路径列表（保持原顺序）
    """
    # 创建ft目录
    ft_dir.mkdir(parents=True, exist_ok=True)
    logging.info(f"创建ft目录: {ft_dir} (与rpt/tcl同级)")

    # 复制所有正常文件（保留原文件名）
    ft_files = []
    for file_path in sv_files:
        ft_file_path = ft_dir / file_path.name
        if file_path.exists():
            shutil.copy2(file_path, ft_file_path)
            logging.info(f"复制正常文件: {file_path} -> {ft_file_path}")
        else:
            logging.warning(f"文件不存在，跳过复制: {file_path}")
        ft_files.append(ft_file_path)
    
    # 单独复制变异体文件（保留原文件名，比如i2c_master_bit_ctrl_mutant.v）
    mutant_ft_path = ft_dir / mutant_file_path.name
    shutil.copy2(mutant_file_path, mutant_ft_path)
    logging.info(f"复制变异体文件: {mutant_file_path} -> {mutant_ft_path}")
    
    # 替换ft_files里的原始模块文件路径为变异体路径（保持列表顺序）
    original_file = find_original_module_file(sv_files, mutant_module)
    if original_file:
        for i, ft_file in enumerate(ft_files):
            if ft_file.name == original_file.name:
                ft_files[i] = mutant_ft_path
                logging.info(f"替换列表中原始文件路径为变异体路径: {original_file.name} -> {mutant_ft_path.name}")
    
    return ft_files

# ============================ 插入SVA到顶层模块文件 ============================
def insert_sva_into_module(
    module_content: str,
    module_name: str,
    sva_string: str,
    indent: str = "  "
) -> str:
    """
    将单个SVA字符串插入到指定模块的endmodule之前
    """
    try:
        # 匹配模块的完整内容（包括module定义到endmodule）
        module_pattern = re.compile(
            rf"^\s*module\s+{re.escape(module_name)}\b.*?^endmodule",
            re.MULTILINE | re.DOTALL
        )
        match = module_pattern.search(module_content)
        if not match:
            logging.error(f"模块 '{module_name}' 未在文件中找到")
            return module_content  # 未找到模块，返回原内容

        module_str = match.group(0)
        # 处理单个SVA，添加缩进
        sva_content = ""
        if sva_string.strip():
            # 对SVA的每一行添加缩进
            indented_sva = '\n'.join([indent + line for line in sva_string.strip().split('\n')])
            sva_content = f"{indented_sva}\n"

        # 在endmodule前插入SVA
        modified_module = module_str.replace(
            "endmodule",
            f"{sva_content}endmodule"
        )
        # 替换原模块内容
        modified_content = module_content[:match.start()] + modified_module + module_content[match.end():]
        return modified_content
    except Exception as e:
        logging.error(f"插入单个SVA到模块 {module_name} 失败: {e}", exc_info=True)
        return module_content

def insert_sva_to_top_module_in_ft(
    ft_dir: Path,
    top_module: str,  # 【修改】移除sv_files参数（不再需要）
    sva_string: str
) -> bool:
    """
    【核心修改】在ft目录下的顶层模块文件中插入SVA断言（优先变异体版本）
    :param ft_dir: ft目录路径
    :param top_module: 顶层模块名
    :param sva_string: 要插入的SVA字符串
    :return: 成功返回True，失败返回False
    """
    try:
        # 【关键修改】使用新增的函数查找FT目录中的顶层文件（含变异体）
        ft_top_file = find_top_module_file_in_ft(ft_dir, top_module)
        if not ft_top_file:
            logging.error(f"无法在FT目录找到顶层模块{top_module}的文件")
            return False
        
        # 读取文件内容
        with open(ft_top_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 插入SVA
        modified_content = insert_sva_into_module(content, top_module, sva_string)
        
        # 写回文件
        with open(ft_top_file, 'w', encoding='utf-8') as f:
            f.write(modified_content)
        
        logging.info(f"SVA断言已插入到FT目录的顶层模块文件: {ft_top_file}")
        return True
    except Exception as e:
        logging.error(f"插入SVA到顶层模块失败: {e}", exc_info=True)
        return False

# ============================ 生成TCL脚本 ============================
def generate_tcl_script(
    output_tcl_path: Path,
    top_module: str,
    clock_signal: str,
    reset_signal: str,
    analyze_files: List[Path]
) -> bool:
    """
    生成参数化的TCL脚本（按sv_files.txt顺序分析ft目录文件）
    """
    try:
        # 构建analyze命令行（使用ft目录文件，保持顺序）
        analyze_lines = []
        analyze_lines.append("# 按sv_files.txt顺序分析ft目录中的文件（含变异体+断言）")
        analyze_lines.append("analyze -sv12 \\")
        for i, file_path in enumerate(analyze_files):
            if i == len(analyze_files) - 1:
                # 最后一个文件，无反斜杠
                analyze_lines.append(f"    {file_path.resolve()}")
            else:
                analyze_lines.append(f"    {file_path.resolve()} \\")
        
        # TCL模板
        tcl_template = """# Auto-generated TCL script for assertion mutant verification (separate mode)
# Top module: {top_module}
# Clock: {clock_signal}
# Reset: {reset_signal}

# Set working directory
cd {work_dir}

{analyze_block}

# Elaborate top module
elaborate -top {top_module}

# Set clock and reset
clock {clock_signal}
reset {reset_signal}

# Prove all properties
prove -all

# Exit
exit -force
"""
        # 填充模板
        tcl_content = tcl_template.format(
            top_module=top_module,
            clock_signal=clock_signal,
            reset_signal=reset_signal,
            work_dir=output_tcl_path.parent,
            analyze_block="\n".join(analyze_lines)
        )

        # 写入TCL文件
        output_tcl_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_tcl_path, 'w', encoding='utf-8') as f:
            f.write(tcl_content)

        logging.info(f"TCL脚本生成完成: {output_tcl_path}")
        return True
    except Exception as e:
        logging.error(f"生成TCL脚本失败 {output_tcl_path}: {e}", exc_info=True)
        return False

# ============================ 运行JG验证 ============================
def run_jg_verification(
    tcl_path: Path,
    jg_proj_dir: Path,
    report_path: Path
) -> bool:
    """
    运行JasperGold验证，保存报告（超时60分钟）
    """
    try:
        # 清理旧项目目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)
        jg_proj_dir.mkdir(parents=True, exist_ok=True)

        # 构建JG命令（添加-allow_unsupported_OS抑制Ubuntu版本警告）
        jasper_command = f"jg -allow_unsupported_OS -batch -proj {jg_proj_dir} -tcl {tcl_path}"
        logging.info(f"运行JG命令: {jasper_command}")

        # 执行命令（设置超时，60分钟）
        process = None
        report_content = ""
        try:
            process = subprocess.Popen(
                jasper_command,
                shell=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                preexec_fn=os.setsid  # 设置进程组，便于后续杀死
            )
            stdout, _ = process.communicate(timeout=3600)  # 60分钟超时
            report_content = stdout
        except subprocess.TimeoutExpired:
            logging.warning(f"JG验证超时: {tcl_path.stem}")
            if process:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)  # 杀死进程组
            report_content = "ERROR: Timeout after 3600 seconds"
        except Exception as e:
            logging.error(f"执行JG命令失败: {e}")
            report_content = f"ERROR: {str(e)}"
        finally:
            # 清理进程
            if process and process.poll() is None:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except Exception:
                    pass

        # 保存报告
        report_path.parent.mkdir(parents=True, exist_ok=True)
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report_content)

        # 清理JG项目目录（节省空间）
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)

        logging.info(f"JG报告保存完成: {report_path}")
        return True
    except Exception as e:
        logging.error(f"运行JG验证失败 {tcl_path}: {e}", exc_info=True)
        return False

# ============================ 解析JG验证结果 ============================
def extract_detailed_proof_status(report_content: str) -> Dict[str, Any]:
    """
    从JG报告中提取详细的验证状态
    """
    result = {
        "overall_status": "inconclusive",
        "total_assertions": 0,
        "proven_count": 0,
        "cex_count": 0,
        "inconclusive_count": 0,
        "timeout_count": 0,
        "error_messages": []
    }

    # 提取错误信息
    error_pattern = re.compile(r"^\s*(?:ERROR|FATAL|CRITICAL).*", re.MULTILINE)
    errors = error_pattern.findall(report_content)
    if errors:
        result["overall_status"] = "error"
        result["error_messages"] = sorted(list(set([e.strip() for e in errors])))
        return result

    # 提取SUMMARY部分
    summary_patterns = [
        r"SUMMARY\s*\n=+\s*\n(.*?)(?:\n=+|\n\s*$|\Z)",
        r"SUMMARY\s*\n-+\s*\n(.*?)(?:\n-+|\n\s*$|\Z)",
        r"SUMMARY\s*\n(.*?)(?:\n={2,}|\n-{2,}|\n\s*$|\Z)",
    ]
    summary_content = None
    for pattern in summary_patterns:
        summary_match = re.search(pattern, report_content, re.DOTALL | re.IGNORECASE)
        if summary_match:
            summary_content = summary_match.group(1).strip()
            break
    if not summary_content:
        summary_content = report_content
        result["error_messages"].append("未找到SUMMARY部分，使用完整报告分析")

    # 提取断言数量
    total_match = re.search(r"assertions\s*:\s*(\d+)", summary_content)
    if total_match:
        result["total_assertions"] = int(total_match.group(1))

    # 提取各状态数量
    status_patterns = {
        "proven": r"-\s*proven\s*:\s*(\d+)",
        "cex": r"-\s*cex\s*:\s*(\d+)",
        "ar_cex": r"-\s*ar_cex\s*:\s*(\d+)",
        "undetermined": r"-\s*undetermined\s*:\s*(\d+)",
        "unknown": r"-\s*unknown\s*:\s*(\d+)",
        "timeout": r"-\s*timeout\s*:\s*(\d+)"
    }
    for status, pattern in status_patterns.items():
        match = re.search(pattern, summary_content)
        if match:
            count = int(match.group(1))
            if status == "proven":
                result["proven_count"] += count
            elif status in ["cex", "ar_cex"]:
                result["cex_count"] += count
            elif status in ["undetermined", "unknown"]:
                result["inconclusive_count"] += count
            elif status == "timeout":
                result["timeout_count"] += count

    # 确定整体状态
    if result["total_assertions"] > 0:
        if result["proven_count"] == result["total_assertions"]:
            result["overall_status"] = "proven"
        elif result["cex_count"] > 0:
            result["overall_status"] = "cex"
        elif result["timeout_count"] > 0:
            result["overall_status"] = "timeout"
        elif result["inconclusive_count"] > 0:
            result["overall_status"] = "inconclusive"
        elif result["proven_count"] > 0:
            result["overall_status"] = "partial_proven"
    else:
        result["overall_status"] = "no_assertions"

    return result

def is_mutant_killed(proof_status: Dict[str, Any]) -> bool:
    """
    判断变异体是否被杀死
    杀死条件：编译错误 / proven数量与总断言数不相等 / 验证状态不是proven
    """
    total = proof_status["total_assertions"]
    proven = proof_status["proven_count"]
    overall = proof_status["overall_status"]

    # 杀死条件
    if (overall == "error" or  # 编译/执行错误
        (total > 0 and proven != total) or  # proven数量不匹配
        overall not in ["proven"]):  # 验证状态不是proven
        return True
    return False

# ============================ 处理单个（断言+模块+变异体）对 ============================
def process_assertion_mutant_pair(
    args_tuple: Tuple
) -> Dict[str, Any]:
    """
    处理单个断言+模块+变异体对的包装函数（仅支持分离模式）
    参数元组：(module_name, mutant_dir_name, mutants_src_dir, output_root, 
              assertion_rank, assertion_sva, top_module, clock_signal, reset_signal, 
              skip_existing, sv_files)
    """
    # 解析参数
    (
        module_name, mutant_dir_name, mutants_src_dir, output_root, 
        assertion_rank, assertion_sva, top_module, clock_signal, reset_signal, 
        skip_existing, sv_files
    ) = args_tuple

    # 初始化结果
    result = {
        "module_name": module_name,
        "mutant_id": mutant_dir_name,
        "assertion_rank": assertion_rank,
        "status": "failed",
        "killed": False,
        "proof_status": {},
        "error_message": "",
        "paths": {}
    }

    try:
        # 1. 定义路径
        # 变异体源路径
        module_src_dir = mutants_src_dir / module_name
        mutant_src_dir = module_src_dir / mutant_dir_name
        # 找变异体文件（优先sv，再v）
        mutant_file_sv = mutant_src_dir / f"{module_name}_mutant.sv"
        mutant_file_v = mutant_src_dir / f"{module_name}_mutant.v"
        if mutant_file_sv.exists():
            mutant_file_path = mutant_file_sv
        elif mutant_file_v.exists():
            mutant_file_path = mutant_file_v
        else:
            result["error_message"] = f"变异体文件不存在: {mutant_file_sv} 或 {mutant_file_v}"
            logging.error(result["error_message"])
            return result

        # 输出路径：output_root / 模块名 / 变异体名 / Rank_排名
        module_output_dir = output_root / module_name
        mutant_output_dir = module_output_dir / mutant_dir_name
        rank_dir = mutant_output_dir / f"Rank_{assertion_rank}"
        ft_dir = rank_dir / "ft"  # ft目录与rpt/tcl同级
        tcl_path = rank_dir / "tcl" / "mutation.tcl"
        report_path = rank_dir / "rpt" / "mutation.txt"
        jg_proj_dir = rank_dir / "jg_proj"
        result_file = rank_dir / "result.json"

        result["paths"] = {
            "module_name": module_name,
            "mutant_file": str(mutant_file_path),
            "ft_dir": str(ft_dir),
            "tcl": str(tcl_path),
            "report": str(report_path),
            "result": str(result_file)
        }

        # 跳过已处理的（断言+模块+变异体）对
        if skip_existing and result_file.exists():
            with open(result_file, 'r', encoding='utf-8') as f:
                existing_result = json.load(f)
            logging.info(f"跳过已处理的（断言Rank-{assertion_rank} + 模块{module_name} + 变异体{mutant_dir_name}）")
            return existing_result

        # 2. 复制文件到ft目录并替换变异体
        ft_files = copy_files_to_ft(ft_dir, sv_files, module_name, mutant_file_path)
        if not ft_files:
            result["error_message"] = "复制文件到ft目录失败"
            logging.error(result["error_message"])
            return result

        # 3. 在ft目录的顶层模块文件中插入SVA
        # 【修改】调用时移除sv_files参数，使用新的查找逻辑
        if not insert_sva_to_top_module_in_ft(ft_dir, top_module, assertion_sva):
            result["error_message"] = "SVA插入到顶层模块失败"
            logging.error(result["error_message"])
            return result

        # 4. 生成TCL脚本（多文件分析）
        if not generate_tcl_script(tcl_path, top_module, clock_signal, reset_signal, ft_files):
            result["error_message"] = "TCL脚本生成失败"
            logging.error(result["error_message"])
            return result

        # 5. 运行JG验证
        if not run_jg_verification(tcl_path, jg_proj_dir, report_path):
            result["error_message"] = "JG验证运行失败"
            logging.error(result["error_message"])
            return result

        # 6. 分析报告
        report_content = report_path.read_text(encoding="utf-8")
        proof_status = extract_detailed_proof_status(report_content)
        result["proof_status"] = proof_status

        # 7. 判断变异体是否被杀死
        result["killed"] = is_mutant_killed(proof_status)
        result["status"] = "success"

        # 保存单个结果
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)

        logging.info(f"处理完成（断言Rank-{assertion_rank} + 模块{module_name} + 变异体{mutant_dir_name}）: {'KILLED' if result['killed'] else 'SURVIVED'}")

    except Exception as e:
        error_msg = f"处理（断言Rank-{assertion_rank} + 模块{module_name} + 变异体{mutant_dir_name}）时发生异常: {str(e)}"
        result["error_message"] = error_msg
        result["status"] = "exception"
        logging.error(error_msg, exc_info=True)

    return result

# ============================ 主函数 ============================
def main():
    # 解析命令行参数（仅支持分离模式）
    parser = argparse.ArgumentParser(description="单个断言对变异体的验证（仅支持分离模块模式）")
    parser.add_argument("--top-proven-loc", required=True, type=Path,
                        help="已证明并排序的Assertion文件路径（如assertion_scores.json）")
    parser.add_argument("--mutants-src-dir", required=True, type=Path,
                        help="变异体源目录（下为模块名子目录，模块目录下为数字命名的变异体目录）")
    parser.add_argument("--output-root", default="mutants_assertion_verif_separate", type=Path,
                        help="输出根目录（默认: mutants_assertion_verif_separate）")
    parser.add_argument("--top-module", required=True, type=str,
                        help="顶层模块名（如i2c_master_top）")
    parser.add_argument("--clock", required=True, type=str,
                        help="时钟信号名（如clk_i、wb_clk_i）")
    parser.add_argument("--reset", required=True, type=str,
                        help="复位信号名（如~rst_ni、!nReset）")
    parser.add_argument("--svfiles-loc", required=True, type=Path,
                        help="sv_files.txt路径（含所有正常模块文件路径，按分析顺序排列）")
    parser.add_argument("--workers", type=int, default=10,
                        help="并行处理的工作进程数（默认: 10）")
    parser.add_argument("--skip-existing", action="store_true",
                        help="跳过已处理的（断言+模块+变异体）对")

    args = parser.parse_args()

    # 验证输入路径
    if not args.top_proven_loc.exists():
        logging.error(f"Assertion文件不存在: {args.top_proven_loc}")
        sys.exit(1)
    if not args.mutants_src_dir.exists():
        logging.error(f"变异体源目录不存在: {args.mutants_src_dir}")
        sys.exit(1)
    if not args.svfiles_loc.exists():
        logging.error(f"sv_files.txt不存在: {args.svfiles_loc}")
        sys.exit(1)

    # 设置日志
    args.output_root.mkdir(parents=True, exist_ok=True)
    setup_logging(args.output_root)
    logging.info("="*80)
    logging.info("开始执行单个断言对变异体的验证流程（分离模块模式）")
    logging.info(f"Assertion文件: {args.top_proven_loc.resolve()}")
    logging.info(f"变异体源目录: {args.mutants_src_dir.resolve()}")
    logging.info(f"输出根目录: {args.output_root.resolve()}")
    logging.info(f"顶层模块: {args.top_module}")
    logging.info(f"时钟信号: {args.clock}")
    logging.info(f"复位信号: {args.reset}")
    logging.info(f"sv_files.txt路径: {args.svfiles_loc.resolve()}")
    logging.info("="*80)

    # 1. 读取并解析Assertion文件（按Rank排序）
    try:
        with open(args.top_proven_loc, 'r', encoding='utf-8') as f:
            assertion_data = json.load(f)
        # 提取顶层模块的断言
        module_name = args.top_module
        if module_name not in assertion_data:
            logging.error(f"Assertion文件中未找到模块{module_name}的断言")
            sys.exit(1)
        assertions = assertion_data[module_name]
        # 按Rank升序排序
        assertions_sorted = sorted(assertions, key=lambda x: x["Rank"])
        logging.info(f"成功读取{len(assertions_sorted)}个按Rank排序的断言")
    except Exception as e:
        logging.error(f"读取Assertion文件失败: {e}", exc_info=True)
        sys.exit(1)

    # 2. 解析sv_files.txt
    sv_files = parse_sv_files_txt(args.svfiles_loc)

    # 3. 获取所有模块目录和变异体目录
    # 获取所有模块目录（mutants-src-dir下的子目录，非数字命名）
    module_dirs = sorted([d for d in args.mutants_src_dir.iterdir() if d.is_dir() and not d.name.isdigit()])
    if not module_dirs:
        logging.error(f"未找到模块目录: {args.mutants_src_dir}")
        sys.exit(1)
    logging.info(f"找到{len(module_dirs)}个模块目录: {[d.name for d in module_dirs]}")

    # 4. 准备并行处理的参数列表
    args_list = []
    for module_dir in module_dirs:
        module_name = module_dir.name
        # 获取该模块下的所有变异体目录（数字命名）
        mutant_dirs = sorted([d for d in module_dir.iterdir() if d.is_dir() and d.name.isdigit()])
        if not mutant_dirs:
            logging.warning(f"模块{module_name}下未找到变异体目录，跳过")
            continue
        logging.info(f"模块{module_name}下找到{len(mutant_dirs)}个变异体目录")
        
        # 遍历每个断言
        for assertion in assertions_sorted:
            rank = assertion["Rank"]
            sva_string = assertion["sva_string"]
            # 遍历每个变异体
            for mutant_dir in mutant_dirs:
                mutant_dir_name = mutant_dir.name
                args_list.append((
                    module_name, mutant_dir_name, args.mutants_src_dir, args.output_root,
                    rank, sva_string, args.top_module, args.clock, args.reset,
                    args.skip_existing, sv_files
                ))

    if not args_list:
        logging.error("未找到任何需要处理的（断言+模块+变异体）对")
        sys.exit(1)
    logging.info(f"共生成{len(args_list)}个处理任务")

    # 5. 并行处理
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        future_to_pair = {
            executor.submit(process_assertion_mutant_pair, pair_args): 
            (pair_args[0], pair_args[1], pair_args[4])  # module + mutant + rank
            for pair_args in args_list
        }
        
        with tqdm(total=len(args_list), desc="处理（断言+模块+变异体）对") as pbar:
            for future in as_completed(future_to_pair):
                key = future_to_pair[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    err_msg = f"获取（模块{key[0]} + 变异体{key[1]} + 断言Rank-{key[2]}）结果时异常: {e}"
                    logging.error(err_msg, exc_info=True)
                    results.append({
                        "module_name": key[0],
                        "mutant_id": key[1],
                        "assertion_rank": key[2],
                        "status": "future_exception",
                        "error_message": str(e),
                        "killed": False
                    })
                pbar.update(1)

    # 6. 统计结果（按断言Rank+模块）
    # 初始化统计结构
    rank_summary = {}
    module_names = [d.name for d in module_dirs]
    for assertion in assertions_sorted:
        rank = assertion["Rank"]
        rank_summary[rank] = {
            "rank": rank,
            "sva_string": assertion["sva_string"],
            "total_mutants": 0,
            "processed_mutants": 0,
            "killed_count": 0,
            "survived_count": 0,
            "failed_count": 0,
            "killed_mutants": [],
            "survived_mutants": [],
            "failed_mutants": [],
            "by_module": {mod: {"total":0, "killed":0, "survived":0, "failed":0} for mod in module_names}
        }
    
    # 统计总变异体数
    total_mutants = 0
    for module_dir in module_dirs:
        mutant_dirs = [d for d in module_dir.iterdir() if d.is_dir() and d.name.isdigit()]
        total_mutants += len(mutant_dirs)
    for rank in rank_summary:
        rank_summary[rank]["total_mutants"] = total_mutants

    # 遍历结果更新统计
    for result in results:
        rank = result["assertion_rank"]
        module_name = result["module_name"]
        mutant_id = result["mutant_id"]
        status = result["status"]
        killed = result.get("killed", False)

        if rank not in rank_summary or module_name not in rank_summary[rank]["by_module"]:
            continue

        summary = rank_summary[rank]
        module_summary = summary["by_module"][module_name]
        
        summary["processed_mutants"] += 1
        module_summary["total"] += 1

        mutant_key = f"{module_name}/{mutant_id}"
        if status == "success":
            if killed:
                summary["killed_count"] += 1
                summary["killed_mutants"].append(mutant_key)
                module_summary["killed"] += 1
            else:
                summary["survived_count"] += 1
                summary["survived_mutants"].append(mutant_key)
                module_summary["survived"] += 1
        else:
            summary["failed_count"] += 1
            summary["failed_mutants"].append(mutant_key)
            module_summary["failed"] += 1

    # 7. 生成最终汇总文件
    final_summary = {
        "timestamp": datetime.now().isoformat(),
        "total_assertions": len(assertions_sorted),
        "total_modules": len(module_dirs),
        "total_mutants": total_mutants,
        "assertion_rank_summary": list(rank_summary.values()),
        "detailed_results": results
    }
    summary_file = args.output_root / "assertion_kill_summary.json"
    with open(summary_file, 'w', encoding='utf-8') as f:
        json.dump(final_summary, f, indent=2, ensure_ascii=False)

    # 8. 打印汇总信息
    logging.info("\n" + "="*80)
    logging.info("验证结果汇总（分离模块模式）:")
    logging.info(f"总断言数: {final_summary['total_assertions']}")
    logging.info(f"总模块数: {final_summary['total_modules']}")
    logging.info(f"总变异体数: {final_summary['total_mutants']}")
    logging.info("-"*60)
    for rank in sorted(rank_summary.keys()):
        summary = rank_summary[rank]
        logging.info(f"\n断言Rank-{rank}:")
        logging.info(f"  总变异体数: {summary['total_mutants']}")
        logging.info(f"  已处理数: {summary['processed_mutants']}")
        logging.info(f"  杀死数: {summary['killed_count']} (编号: {','.join(summary['killed_mutants']) if summary['killed_mutants'] else '无'})")
        logging.info(f"  存活数: {summary['survived_count']} (编号: {','.join(summary['survived_mutants']) if summary['survived_mutants'] else '无'})")
        logging.info(f"  失败数: {summary['failed_count']} (编号: {','.join(summary['failed_mutants']) if summary['failed_mutants'] else '无'})")
        logging.info(f"  按模块细分:")
        for mod_name, mod_stats in summary["by_module"].items():
            logging.info(f"    模块{mod_name}: 总数={mod_stats['total']} | 杀死={mod_stats['killed']} | 存活={mod_stats['survived']} | 失败={mod_stats['failed']}")
    logging.info(f"\n汇总文件保存至: {summary_file}")
    logging.info("="*80)
    logging.info("所有（断言+模块+变异体）对处理完成！")

if __name__ == "__main__":
    main()