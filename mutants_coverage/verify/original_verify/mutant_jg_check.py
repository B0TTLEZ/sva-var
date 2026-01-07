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
    log_file = log_dir / f"mutant_syntax_check_{timestamp}.log"

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

# ============================ 复制文件到临时目录（保留变异体原文件名） ============================
def copy_files_to_temp(
    temp_dir: Path,
    sv_files: List[Path],
    mutant_module: str,
    mutant_file_path: Path
) -> List[Path]:
    """
    复制所有需要的文件到临时目录：
    1. 复制sv_files中的正常文件到temp_dir（保留原文件名）
    2. 复制变异体文件到temp_dir（保留原文件名，不替换原始文件名字）
    :param temp_dir: 临时目录（输出目录/ft，和rpt/tcl同级）
    :param sv_files: 原始文件列表
    :param mutant_module: 变异模块名
    :param mutant_file_path: 变异体文件路径
    :return: 临时目录下的文件路径列表（保持原顺序）
    """
    # 创建临时目录
    temp_dir.mkdir(parents=True, exist_ok=True)
    logging.info(f"创建临时目录: {temp_dir} (与rpt/tcl同级)")

    # 复制所有正常文件（保留原文件名）
    temp_files = []
    for file_path in sv_files:
        temp_file_path = temp_dir / file_path.name
        if file_path.exists():
            shutil.copy2(file_path, temp_file_path)
            logging.info(f"复制正常文件: {file_path} -> {temp_file_path}")
        else:
            logging.warning(f"文件不存在，跳过复制: {file_path}")
        temp_files.append(temp_file_path)
    
    # 单独复制变异体文件（保留原文件名，比如i2c_master_bit_ctrl_mutant.v）
    mutant_temp_path = temp_dir / mutant_file_path.name
    shutil.copy2(mutant_file_path, mutant_temp_path)
    logging.info(f"复制变异体文件（保留原文件名）: {mutant_file_path} -> {mutant_temp_path}")
    
    # 替换temp_files里的原始模块文件路径为变异体文件路径（保持列表顺序）
    original_file = find_original_module_file(sv_files, mutant_module)
    if original_file:
        for i, temp_file in enumerate(temp_files):
            if temp_file.name == original_file.name:
                temp_files[i] = mutant_temp_path
                logging.info(f"替换列表中原始文件路径为变异体路径: {original_file.name} -> {mutant_temp_path.name}")
    
    return temp_files

# ============================ 生成仅验证变异体的TCL脚本（适配临时目录） ============================
def generate_mutant_check_tcl(
    output_tcl_path: Path,
    top_module: str,
    analyze_files: List[Path]  # 临时目录下的文件列表
) -> bool:
    """
    生成仅分析/精化变异体的TCL脚本（使用临时目录文件）
    :param output_tcl_path: 输出TCL路径
    :param top_module: 顶层模块名
    :param analyze_files: 临时目录下的文件列表
    :return: 成功返回True，失败返回False
    """
    try:
        # 构建analyze命令行（使用临时目录文件，无路径问题）
        analyze_lines = []
        analyze_lines.append("# 按sv_files.txt顺序分析临时目录中的文件（含变异体）")
        analyze_lines.append("analyze -sv12 \\")
        for i, file_path in enumerate(analyze_files):
            if i == len(analyze_files) - 1:
                # 最后一个文件，无反斜杠
                analyze_lines.append(f"    {file_path.resolve()}")
            else:
                analyze_lines.append(f"    {file_path.resolve()} \\")
        
        tcl_template = """# Auto-generated TCL for mutant syntax/semantic check (no assertions)
# Top module: {top_module}
{analyze_block}

# 精化顶层模块（验证语义正确性）
elaborate -top {top_module}

# 无prove步骤（仅检查编译/精化）
report

# Exit
exit -force
"""
        # 填充模板
        tcl_content = tcl_template.format(
            top_module=top_module,
            analyze_block="\n".join(analyze_lines)
        )

        # 写入TCL文件
        output_tcl_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_tcl_path, 'w', encoding='utf-8') as f:
            f.write(tcl_content)

        logging.info(f"变异体检查TCL生成完成: {output_tcl_path}")
        return True
    except Exception as e:
        logging.error(f"生成TCL失败 {output_tcl_path}: {e}", exc_info=True)
        return False

# ============================ 运行JG验证（仅检查变异体） ============================
def run_jg_mutant_check(
    tcl_path: Path,
    jg_proj_dir: Path,
    report_path: Path
) -> bool:
    """
    运行JG验证（仅分析/精化变异体，无断言）
    :param tcl_path: TCL脚本路径
    :param jg_proj_dir: JG临时项目目录
    :param report_path: JG报告保存路径
    :return: 成功返回True，失败返回False
    """
    try:
        # 清理旧项目目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)
        jg_proj_dir.mkdir(parents=True, exist_ok=True)

        # 构建JG命令（添加-allow_unsupported_OS抑制Ubuntu版本警告）
        jasper_command = f"jg -allow_unsupported_OS -batch -proj {jg_proj_dir} -tcl {tcl_path}"
        logging.info(f"运行JG命令: {jasper_command}")

        # 执行命令（超时10分钟，仅编译/精化足够）
        process = None
        report_content = ""
        try:
            process = subprocess.Popen(
                jasper_command,
                shell=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                preexec_fn=os.setsid  # 绑定进程组，方便超时杀死
            )
            stdout, _ = process.communicate(timeout=600)  # 10分钟超时
            report_content = stdout
        except subprocess.TimeoutExpired:
            logging.warning(f"JG验证超时: {tcl_path.stem}")
            if process:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            report_content = "ERROR: Timeout after 600 seconds (mutant check)"
        except Exception as e:
            logging.error(f"执行JG命令失败: {e}")
            report_content = f"ERROR: {str(e)}"
        finally:
            # 清理残留进程
            if process and process.poll() is None:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except Exception:
                    pass

        # 保存报告
        report_path.parent.mkdir(parents=True, exist_ok=True)
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report_content)

        # 清理JG临时目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)

        logging.info(f"JG报告保存完成: {report_path}")
        return True
    except Exception as e:
        logging.error(f"运行JG验证失败 {tcl_path}: {e}", exc_info=True)
        return False

# ============================ 解析JG报告，判断变异体是否合法 ============================
def parse_mutant_jg_report(report_content: str) -> Dict[str, Any]:
    """
    解析JG报告，判断变异体是否存在语法/语义错误
    :param report_content: JG报告内容
    :return: 解析结果字典
    """
    result = {
        "is_valid": True,          # 变异体是否合法（无语法/语义错误）
        "error_type": None,        # 错误类型：syntax_error/semantic_error/timeout/other
        "error_messages": [],      # 关键错误信息列表
        "has_analyze_error": False,# 是否有analyze阶段错误（语法）
        "has_elaborate_error": False # 是否有elaborate阶段错误（语义）
    }

    # 1. 提取所有错误信息
    error_pattern = re.compile(r"^\s*(?:ERROR|FATAL|CRITICAL).*", re.MULTILINE)
    all_errors = [e.strip() for e in error_pattern.findall(report_content)]
    if not all_errors:
        return result

    # 2. 区分错误类型
    # 语法错误（analyze阶段）：关键词如 "syntax error", "parse error", "SV12"
    syntax_keywords = ["syntax error", "parse error", "invalid token", "SV12", "analyze failed"]
    # 语义错误（elaborate阶段）：关键词如 "elaborate failed", "undefined symbol", "module not found", "duplicate declaration"
    semantic_keywords = ["elaborate failed", "undefined symbol", "module not found", "duplicate declaration", 
                         "unknown identifier", "type mismatch", "port mismatch"]
    # 超时关键词
    timeout_keywords = ["Timeout after", "time limit exceeded"]

    # 筛选关键错误信息
    key_errors = []
    for err in all_errors:
        # 忽略无关警告（如JG版本信息、路径提示）
        if any(ignore in err.lower() for ignore in ["jasper gold version", "info:", "note:"]):
            continue
        key_errors.append(err)

    result["error_messages"] = key_errors

    # 判断错误类型
    if any(kw in err.lower() for kw in syntax_keywords for err in key_errors):
        result["is_valid"] = False
        result["error_type"] = "syntax_error"
        result["has_analyze_error"] = True
    elif any(kw in err.lower() for kw in semantic_keywords for err in key_errors):
        result["is_valid"] = False
        result["error_type"] = "semantic_error"
        result["has_elaborate_error"] = True
    elif any(kw in err.lower() for kw in timeout_keywords for err in key_errors):
        result["is_valid"] = False
        result["error_type"] = "timeout"
    elif key_errors:
        result["is_valid"] = False
        result["error_type"] = "other_error"

    return result

# ============================ 处理单个变异体（兼容两种模式） ============================
def process_single_mutant(args_tuple: Tuple) -> Dict[str, Any]:
    """
    处理单个变异体的检查（并行执行）
    非separate模式参数：(mutant_dir_name, mutants_src_dir, output_root, top_module, skip_existing, None, None)
    separate模式参数：(module_name, mutant_dir_name, mutants_src_dir, output_root, top_module, skip_existing, sv_files)
    :param args_tuple: 入参元组
    :return: 处理结果字典
    """
    # 解析参数
    if len(args_tuple) == 7:
        # separate模式
        module_name, mutant_dir_name, mutants_src_dir, output_root, top_module, skip_existing, sv_files = args_tuple
        is_separate = True
    else:
        # 非separate模式
        mutant_dir_name, mutants_src_dir, output_root, top_module, skip_existing, _, _ = args_tuple
        module_name = None
        sv_files = None
        is_separate = False

    # 初始化结果
    result = {
        "mutant_id": mutant_dir_name,
        "module_name": module_name if is_separate else "combined",
        "status": "failed",          # success/exception/skipped
        "is_valid": False,           # 变异体是否合法
        "error_type": None,
        "error_messages": [],
        "paths": {},
        "temp_dir": "",              # 临时目录路径（和rpt/tcl同级）
        "error_message": ""
    }

    try:
        # ===================== 非separate模式（原有逻辑） =====================
        if not is_separate:
            # 1. 定义路径
            mutant_src_dir = mutants_src_dir / mutant_dir_name
            # 变异体SV文件（兼容两种命名）
            mutant_sv_path = mutant_src_dir / "_combined_rtl_no_comments.sv"
            if not mutant_sv_path.exists():
                mutant_sv_path = mutant_src_dir / "combined_rtl_no_comments.sv"
            if not mutant_sv_path.exists():
                result["error_message"] = f"变异体SV文件不存在: {mutant_sv_path}"
                logging.error(result["error_message"])
                return result

            # 输出路径
            mutant_output_dir = output_root / mutant_dir_name
            tcl_path = mutant_output_dir / "tcl" / "mutant_check.tcl"
            report_path = mutant_output_dir / "rpt" / "mutant_check.txt"
            jg_proj_dir = mutant_output_dir / "jg_proj"
            result_file = mutant_output_dir / "mutant_check_result.json"
            # 临时目录：和rpt/tcl同级的ft目录
            temp_dir = mutant_output_dir / "ft"
            result["temp_dir"] = str(temp_dir)

            result["paths"] = {
                "mutant_sv": str(mutant_sv_path),
                "tcl": str(tcl_path),
                "report": str(report_path),
                "result": str(result_file),
                "temp_dir": str(temp_dir)
            }

            # 跳过已处理的变异体
            if skip_existing and result_file.exists():
                with open(result_file, 'r', encoding='utf-8') as f:
                    existing_result = json.load(f)
                logging.info(f"跳过已处理的变异体: {mutant_dir_name}")
                existing_result["status"] = "skipped"
                return existing_result

            # 2. 生成TCL脚本（单文件）
            if not generate_mutant_check_tcl(tcl_path, top_module, [mutant_sv_path]):
                result["error_message"] = "生成TCL脚本失败"
                logging.error(result["error_message"])
                return result

        # ===================== separate模式（核心修改：保留变异体原文件名） =====================
        else:
            # 1. 定义路径
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

            # 输出路径（按模块+变异体ID组织）
            mutant_output_dir = output_root / module_name / mutant_dir_name
            tcl_path = mutant_output_dir / "tcl" / "mutant_check.tcl"
            report_path = mutant_output_dir / "rpt" / "mutant_check.txt"
            jg_proj_dir = mutant_output_dir / "jg_proj"
            result_file = mutant_output_dir / "mutant_check_result.json"
            # 核心修改：临时目录改为变异体输出目录下的ft（和rpt/tcl同级）
            temp_dir = mutant_output_dir / "ft"
            result["temp_dir"] = str(temp_dir)

            result["paths"] = {
                "module_name": module_name,
                "mutant_file": str(mutant_file_path),
                "tcl": str(tcl_path),
                "report": str(report_path),
                "result": str(result_file),
                "temp_dir": str(temp_dir)
            }

            # 跳过已处理的变异体
            if skip_existing and result_file.exists():
                with open(result_file, 'r', encoding='utf-8') as f:
                    existing_result = json.load(f)
                logging.info(f"跳过已处理的变异体: {module_name}/{mutant_dir_name}")
                existing_result["status"] = "skipped"
                return existing_result

            # 2. 复制所有文件到临时目录（保留变异体原文件名）
            temp_files = copy_files_to_temp(temp_dir, sv_files, module_name, mutant_file_path)
            if not temp_files:
                result["error_message"] = "复制文件到临时目录失败"
                logging.error(result["error_message"])
                return result

            # 3. 生成TCL脚本（使用临时目录文件）
            if not generate_mutant_check_tcl(tcl_path, top_module, temp_files):
                result["error_message"] = "生成TCL脚本失败"
                logging.error(result["error_message"])
                return result

        # ===================== 通用JG执行逻辑 =====================
        # 运行JG验证
        if not run_jg_mutant_check(tcl_path, jg_proj_dir, report_path):
            result["error_message"] = "运行JG验证失败"
            logging.error(result["error_message"])
            return result

        # 解析报告
        report_content = report_path.read_text(encoding="utf-8")
        parse_result = parse_mutant_jg_report(report_content)
        result["is_valid"] = parse_result["is_valid"]
        result["error_type"] = parse_result["error_type"]
        result["error_messages"] = parse_result["error_messages"]

        # 标记处理成功
        result["status"] = "success"
        result["error_message"] = ""

        # 保存单个结果
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)

        # 日志提示
        if is_separate:
            status_text = "VALID" if result['is_valid'] else f"INVALID ({result['error_type']})"
            logging.info(f"变异体{module_name}/{mutant_dir_name}检查完成: {status_text} (临时目录: {temp_dir})")
        else:
            status_text = "VALID" if result['is_valid'] else f"INVALID ({result['error_type']})"
            logging.info(f"变异体{mutant_dir_name}检查完成: {status_text}")

    except Exception as e:
        error_msg = f"处理变异体{module_name}/{mutant_dir_name if is_separate else mutant_dir_name}时异常: {str(e)}"
        result["error_message"] = error_msg
        result["status"] = "exception"
        logging.error(error_msg, exc_info=True)

    return result

# ============================ 主函数 ============================
def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description="变异体JG语法/语义检查（无断言）：筛选合法变异体")
    parser.add_argument("--mutants-src-dir", required=True, type=Path,
                        help="变异体源目录（非separate：直接是0001等；separate：模块名子目录）")
    parser.add_argument("--output-root", default="mutant_jg_check", type=Path,
                        help="输出根目录（默认: mutant_jg_check）")
    parser.add_argument("--top-module", required=True, type=str,
                        help="顶层模块名（如i2c_master_top）")
    parser.add_argument("--workers", type=int, default=10,
                        help="并行处理的工作进程数（默认: 10）")
    parser.add_argument("--skip-existing", action="store_true",
                        help="跳过已处理的变异体")
    # 新增参数
    parser.add_argument("--separate", action="store_true",
                        help="启用分离模块模式（mutants-src-dir下是模块名子目录）")
    parser.add_argument("--svfiles-loc", type=Path,
                        help="separate模式下必填：sv_files.txt路径（含所有正常文件路径）")
    parser.add_argument("--clean-temp", action="store_true",
                        help="执行完成后清理每个变异体目录下的ft临时目录（默认保留）")

    # 解析参数（主函数的args是Namespace对象）
    main_args = parser.parse_args()

    # 验证separate模式参数
    if main_args.separate and not main_args.svfiles_loc:
        parser.error("--separate模式必须指定--svfiles-loc参数")

    # 验证输入
    if not main_args.mutants_src_dir.exists():
        logging.error(f"变异体源目录不存在: {main_args.mutants_src_dir}")
        sys.exit(1)

    # 设置日志
    main_args.output_root.mkdir(parents=True, exist_ok=True)
    setup_logging(main_args.output_root)
    logging.info("="*80)
    logging.info("开始执行变异体JG语法/语义检查（无任何断言）")
    logging.info(f"变异体源目录: {main_args.mutants_src_dir.resolve()}")
    logging.info(f"输出根目录: {main_args.output_root.resolve()}")
    logging.info(f"顶层模块: {main_args.top_module}")
    logging.info(f"分离模块模式: {main_args.separate}")
    logging.info(f"执行后清理临时目录: {main_args.clean_temp}")
    if main_args.separate:
        logging.info(f"sv_files.txt路径: {main_args.svfiles_loc.resolve()}")
    logging.info("="*80)

    # ===================== 非separate模式（原有逻辑） =====================
    if not main_args.separate:
        # 1. 获取所有变异体目录（数字命名）
        mutant_dirs = sorted([d for d in main_args.mutants_src_dir.iterdir() if d.is_dir() and d.name.isdigit()])
        if not mutant_dirs:
            logging.error(f"未找到数字命名的变异体目录: {main_args.mutants_src_dir}")
            sys.exit(1)
        logging.info(f"找到{len(mutant_dirs)}个变异体目录")

        # 2. 准备并行参数
        args_list = []
        for mutant_dir in mutant_dirs:
            args_list.append((
                mutant_dir.name,
                main_args.mutants_src_dir,
                main_args.output_root,
                main_args.top_module,
                main_args.skip_existing,
                None,  # sv_files占位
                None   # module_name占位
            ))

    # ===================== separate模式（新逻辑） =====================
    else:
        # 1. 解析sv_files.txt
        sv_files = parse_sv_files_txt(main_args.svfiles_loc)

        # 2. 获取所有模块目录（mutants-src-dir下的子目录）
        module_dirs = sorted([d for d in main_args.mutants_src_dir.iterdir() if d.is_dir() and not d.name.isdigit()])
        if not module_dirs:
            logging.error(f"separate模式下未找到模块目录: {main_args.mutants_src_dir}")
            sys.exit(1)
        logging.info(f"找到{len(module_dirs)}个模块目录: {[d.name for d in module_dirs]}")

        # 3. 准备并行参数（模块名 + 变异体ID）
        args_list = []
        for module_dir in module_dirs:
            module_name = module_dir.name
            # 获取该模块下的所有变异体目录（数字命名）
            mutant_dirs = sorted([d for d in module_dir.iterdir() if d.is_dir() and d.name.isdigit()])
            if not mutant_dirs:
                logging.warning(f"模块{module_name}下未找到变异体目录，跳过")
                continue
            logging.info(f"模块{module_name}下找到{len(mutant_dirs)}个变异体目录")
            # 构建参数
            for mutant_dir in mutant_dirs:
                args_list.append((
                    module_name,
                    mutant_dir.name,
                    main_args.mutants_src_dir,
                    main_args.output_root,
                    main_args.top_module,
                    main_args.skip_existing,
                    sv_files
                ))

        if not args_list:
            logging.error("separate模式下未找到任何变异体")
            sys.exit(1)

    # ===================== 并行处理变异体 =====================
    results = []
    with ProcessPoolExecutor(max_workers=main_args.workers) as executor:
        future_to_mutant = {executor.submit(process_single_mutant, mutant_args): mutant_args for mutant_args in args_list}
        with tqdm(total=len(args_list), desc="检查变异体合法性") as pbar:
            for future in as_completed(future_to_mutant):
                mutant_args = future_to_mutant[future]
                if main_args.separate:
                    mutant_id = f"{mutant_args[0]}/{mutant_args[1]}"
                else:
                    mutant_id = mutant_args[0]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    logging.error(f"获取变异体{mutant_id}结果异常: {e}", exc_info=True)
                    results.append({
                        "mutant_id": mutant_args[1] if main_args.separate else mutant_args[0],
                        "module_name": mutant_args[0] if main_args.separate else "combined",
                        "status": "future_exception",
                        "error_message": str(e),
                        "is_valid": False
                    })
                pbar.update(1)

    # ===================== 清理临时目录（可选） =====================
    if main_args.clean_temp:
        logging.info("开始清理每个变异体目录下的ft临时目录...")
        for result in results:
            if result.get("temp_dir") and Path(result["temp_dir"]).exists():
                try:
                    shutil.rmtree(result["temp_dir"])
                    logging.info(f"清理临时目录: {result['temp_dir']}")
                except Exception as e:
                    logging.warning(f"清理临时目录失败 {result['temp_dir']}: {e}")

    # ===================== 统计结果（兼容两种模式） =====================
    stats = {
        "total_mutants": len(args_list),
        "valid_mutants": 0,
        "invalid_mutants": 0,
        "failed_mutants": 0,
        "skipped_mutants": 0,
        "invalid_by_type": {
            "syntax_error": [],
            "semantic_error": [],
            "timeout": [],
            "other_error": []
        },
        "by_module": {}  # separate模式下按模块统计
    }

    valid_mutant_ids = []
    invalid_mutant_ids = []
    for result in results:
        mutant_id = result["mutant_id"]
        module_name = result.get("module_name", "combined")
        status = result["status"]

        # 初始化模块统计
        if module_name not in stats["by_module"]:
            stats["by_module"][module_name] = {
                "total": 0,
                "valid": 0,
                "invalid": 0,
                "failed": 0,
                "skipped": 0
            }
        stats["by_module"][module_name]["total"] += 1

        if status == "skipped":
            stats["skipped_mutants"] += 1
            stats["by_module"][module_name]["skipped"] += 1
        elif status == "success":
            if result["is_valid"]:
                stats["valid_mutants"] += 1
                valid_mutant_ids.append(f"{module_name}/{mutant_id}" if main_args.separate else mutant_id)
                stats["by_module"][module_name]["valid"] += 1
            else:
                stats["invalid_mutants"] += 1
                invalid_mutant_ids.append(f"{module_name}/{mutant_id}" if main_args.separate else mutant_id)
                stats["by_module"][module_name]["invalid"] += 1
                err_type = result["error_type"]
                if err_type in stats["invalid_by_type"]:
                    stats["invalid_by_type"][err_type].append(f"{module_name}/{mutant_id}" if main_args.separate else mutant_id)
        else:
            stats["failed_mutants"] += 1
            invalid_mutant_ids.append(f"{module_name}/{mutant_id}" if main_args.separate else mutant_id)
            stats["by_module"][module_name]["failed"] += 1

    # ===================== 生成汇总文件 =====================
    final_summary = {
        "timestamp": datetime.now().isoformat(),
        "is_separate_mode": main_args.separate,
        "clean_temp_dir": main_args.clean_temp,
        "stats": stats,
        "valid_mutant_ids": valid_mutant_ids,
        "invalid_mutant_ids": invalid_mutant_ids,
        "detailed_results": results
    }
    summary_file = main_args.output_root / "mutant_jg_check_summary.json"
    with open(summary_file, 'w', encoding='utf-8') as f:
        json.dump(final_summary, f, indent=2, ensure_ascii=False)

    # ===================== 打印汇总信息 =====================
    logging.info("\n" + "="*80)
    logging.info("变异体JG检查汇总:")
    logging.info(f"总变异体数: {stats['total_mutants']}")
    logging.info(f"合法变异体数: {stats['valid_mutants']} (编号: {','.join(valid_mutant_ids)})")
    logging.info(f"无效变异体数: {stats['invalid_mutants']} (编号: {','.join(invalid_mutant_ids)})")
    logging.info(f"处理失败数: {stats['failed_mutants']}")
    logging.info(f"跳过数: {stats['skipped_mutants']}")
    logging.info("-"*60)
    logging.info("无效变异体分类:")
    for err_type, mutant_ids in stats["invalid_by_type"].items():
        if mutant_ids:
            logging.info(f"  {err_type}: {len(mutant_ids)}个 (编号: {','.join(mutant_ids)})")
    # separate模式下打印模块统计
    if main_args.separate:
        logging.info("-"*60)
        logging.info("按模块统计:")
        for module_name, module_stats in stats["by_module"].items():
            logging.info(f"  模块{module_name}:")
            logging.info(f"    总数: {module_stats['total']} | 合法: {module_stats['valid']} | 无效: {module_stats['invalid']} | 失败: {module_stats['failed']} | 跳过: {module_stats['skipped']}")
    logging.info(f"\n汇总文件保存至: {summary_file}")
    logging.info("="*80)
    logging.info("所有变异体检查完成！")

if __name__ == "__main__":
    main()