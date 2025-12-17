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
from typing import Dict, List, Any, Tuple
from tqdm import tqdm

# ============================ 全局配置与日志设置 ============================
def setup_logging(output_dir: Path):
    """设置日志配置，同时输出到文件和控制台"""
    log_dir = output_dir / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"mutants_irank_verif_{timestamp}.log"

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(log_file, encoding="utf-8"),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return log_file

# ============================ 核心功能函数（复用并修改原代码） ============================
def insert_svas_into_module(
    module_content: str,
    module_name: str,
    sva_strings: List[str],
    indent: str = "  "
) -> str:
    """
    将多个SVA字符串插入到指定模块的endmodule之前
    :param module_content: 原始SV文件内容
    :param module_name: 目标模块名
    :param sva_strings: 要插入的SVA字符串列表
    :param indent: 缩进字符
    :return: 插入SVA后的模块内容，失败返回None
    """
    try:
        # 匹配模块的完整内容（包括module定义到endmodule）
        module_pattern = re.compile(
            rf"^\s*module\s+{re.escape(module_name)}\b.*?^endmodule",
            re.MULTILINE | re.DOTALL
        )
        match = module_pattern.search(module_content)
        if not match:
            logging.error(f"模块 '{module_name}' 未在SV文件中找到")
            return module_content  # 未找到模块，返回原内容

        module_str = match.group(0)
        # 拼接所有SVA，添加缩进
        sva_content = ""
        for sva in sva_strings:
            if not sva.strip():
                continue
            # 对SVA的每一行添加缩进
            indented_sva = '\n'.join([indent + line for line in sva.strip().split('\n')])
            sva_content += f"{indented_sva}\n"

        # 在endmodule前插入SVA
        modified_module = module_str.replace(
            "endmodule",
            f"{sva_content}endmodule"
        )
        # 替换原模块内容
        modified_content = module_content[:match.start()] + modified_module + module_content[match.end():]
        return modified_content
    except Exception as e:
        logging.error(f"插入SVA到模块 {module_name} 失败: {e}", exc_info=True)
        return module_content

def insert_svas_into_sv_file(
    input_sv_path: Path,
    output_sv_path: Path,
    module_sva_map: Dict[str, List[str]]
) -> bool:
    """
    将多个模块的SVA插入到SV文件中，生成新文件
    :param input_sv_path: 输入SV文件路径（变异体的SV文件）
    :param output_sv_path: 输出SV文件路径（植入SVA后的文件）
    :param module_sva_map: 模块名到SVA字符串列表的映射
    :return: 成功返回True，失败返回False
    """
    try:
        # 读取原始SV文件内容
        with open(input_sv_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # 遍历每个模块，插入对应的SVA
        modified_content = content
        for module_name, sva_strings in module_sva_map.items():
            if not sva_strings:
                continue
            modified_content = insert_svas_into_module(modified_content, module_name, sva_strings)

        # 写入输出文件
        output_sv_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_sv_path, 'w', encoding='utf-8') as f:
            f.write(modified_content)

        logging.info(f"SVA植入完成，输出文件: {output_sv_path}")
        return True
    except Exception as e:
        logging.error(f"插入SVA到SV文件失败 {input_sv_path}: {e}", exc_info=True)
        return False

def generate_tcl_script(
    output_tcl_path: Path,
    top_module: str,
    clock_signal: str,
    reset_signal: str,
    sv_file_path: Path,
    inc_dirs: List[Path] = None
) -> bool:
    """
    生成参数化的TCL脚本（适配顶层模块、时钟、复位信号）
    :param output_tcl_path: 输出TCL文件路径
    :param top_module: 顶层模块名
    :param clock_signal: 时钟信号名（如clk_i）
    :param reset_signal: 复位信号名（如~rst_ni）
    :param sv_file_path: 要分析的SV文件路径（植入SVA后的文件）
    :param inc_dirs: 包含目录列表（可选）
    :return: 成功返回True，失败返回False
    """
    try:
        # TCL模板（简化版，保留核心功能）
        tcl_template = """# Auto-generated TCL script for mutants IRank verification
# Top module: {top_module}
# Clock: {clock_signal}
# Reset: {reset_signal}

# Set working directory
cd {work_dir}

# Analyze SV file
analyze -sv12 \\
    {inc_dirs} \\
    {sv_file_path}

# Elaborate top module
elaborate -top {top_module}

# Set clock and reset
clock {clock_signal}
reset {reset_signal}

# Set max trace length
set_max_trace_length 100

# Prove all properties
prove -all

# Exit
exit -force
"""
        # 处理包含目录
        inc_dirs_str = ""
        if inc_dirs:
            inc_dirs_str = ' \\\n    '.join([f"+incdir+{dir_path}" for dir_path in inc_dirs])

        # 填充模板
        tcl_content = tcl_template.format(
            top_module=top_module,
            clock_signal=clock_signal,
            reset_signal=reset_signal,
            work_dir=output_tcl_path.parent,
            inc_dirs=inc_dirs_str,
            sv_file_path=sv_file_path.resolve()
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

def run_jg_verification(
    tcl_path: Path,
    jg_proj_dir: Path,
    report_path: Path
) -> bool:
    """
    运行JasperGold验证，保存报告
    :param tcl_path: TCL脚本路径
    :param jg_proj_dir: JG项目目录（临时）
    :param report_path: 报告输出路径
    :return: 成功返回True，失败返回False
    """
    try:
        # 清理旧项目目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)
        jg_proj_dir.mkdir(parents=True, exist_ok=True)

        # 构建JG命令
        jasper_command = f"jg -batch -proj {jg_proj_dir} -tcl {tcl_path}"
        logging.info(f"运行JG命令: {jasper_command}")

        # 执行命令（设置超时，5分钟）
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
            stdout, _ = process.communicate(timeout=300)  # 5分钟超时
            report_content = stdout
        except subprocess.TimeoutExpired:
            logging.warning(f"JG验证超时: {tcl_path.stem}")
            if process:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)  # 杀死进程组
            report_content = "ERROR: Timeout after 300 seconds"
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

def extract_detailed_proof_status(report_content: str) -> Dict[str, Any]:
    """
    从JG报告中提取详细的验证状态（复用原代码逻辑）
    :param report_content: 报告内容
    :return: 详细状态字典
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
    判断变异体是否被杀死（复用原代码逻辑）
    杀死条件：编译错误 / proven数量与总断言数不相等 / 验证状态不是proven
    :param proof_status: 详细的验证状态
    :return: 被杀死返回True，否则返回False
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

# ============================ 并行处理函数 ============================
def process_single_mutant(
    args_tuple: Tuple
) -> Dict[str, Any]:
    """
    处理单个变异体的包装函数（用于并行处理）
    :param args_tuple: 包含所有必要参数的元组
    :return: 处理结果字典
    """
    (
        mutant_dir_name,  # 变异体目录名（如001）
        mutants_src_dir,  # 变异体源目录
        top_k_output_dir,  # top_k的输出目录（如mutants_IRank/top_25）
        module_sva_map,    # 模块到SVA的映射
        top_module,        # 顶层模块名
        clock_signal,      # 时钟信号
        reset_signal,      # 复位信号
        inc_dirs           # 包含目录
    ) = args_tuple

    # 初始化结果
    result = {
        "mutant_id": mutant_dir_name,
        "status": "failed",
        "killed": False,
        "proof_status": {},
        "error_message": "",
        "paths": {}
    }

    try:
        # 1. 定义路径
        # 变异体源路径
        mutant_src_dir = mutants_src_dir / mutant_dir_name
        mutant_src_sv = mutant_src_dir / "_combined_rtl_no_comments.sv"  # 原变异体SV文件
        if not mutant_src_sv.exists():
            mutant_src_sv = mutant_src_dir / "combined_rtl_no_comments.sv"  # 兼容无下划线的情况
        if not mutant_src_sv.exists():
            result["error_message"] = f"变异体SV文件不存在: {mutant_src_sv}"
            logging.error(result["error_message"])
            return result

        # 输出路径
        mutant_output_dir = top_k_output_dir / mutant_dir_name
        ft_sv_path = mutant_output_dir / "ft" / "mutation.sv"
        tcl_path = mutant_output_dir / "tcl" / "mutation.tcl"
        report_path = mutant_output_dir / "rpt" / "mutation.txt"
        jg_proj_dir = mutant_output_dir / "jg_proj"  # 临时JG项目目录

        result["paths"] = {
            "mutant_src_sv": str(mutant_src_sv),
            "ft_sv": str(ft_sv_path),
            "tcl": str(tcl_path),
            "report": str(report_path)
        }

        # 2. 插入SVA到变异体SV文件
        if not insert_svas_into_sv_file(mutant_src_sv, ft_sv_path, module_sva_map):
            result["error_message"] = "SVA植入失败"
            logging.error(result["error_message"])
            return result

        # 3. 生成TCL脚本
        if not generate_tcl_script(tcl_path, top_module, clock_signal, reset_signal, ft_sv_path, inc_dirs):
            result["error_message"] = "TCL脚本生成失败"
            logging.error(result["error_message"])
            return result

        # 4. 运行JG验证
        if not run_jg_verification(tcl_path, jg_proj_dir, report_path):
            result["error_message"] = "JG验证运行失败"
            logging.error(result["error_message"])
            return result

        # 5. 分析报告
        report_content = report_path.read_text(encoding="utf-8")
        proof_status = extract_detailed_proof_status(report_content)
        result["proof_status"] = proof_status

        # 6. 判断变异体是否被杀死
        result["killed"] = is_mutant_killed(proof_status)
        result["status"] = "success"

        logging.info(f"变异体 {mutant_dir_name} 处理完成: {'KILLED' if result['killed'] else 'SURVIVED'}")
    except Exception as e:
        error_msg = f"处理变异体 {mutant_dir_name} 时发生异常: {str(e)}"
        result["error_message"] = error_msg
        result["status"] = "exception"
        logging.error(error_msg, exc_info=True)

    return result

# ============================ 主函数 ============================
def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description="Mutants IRank Verification: 基于top_k断言的变异体验证")
    parser.add_argument("--top-k-dir", required=True, type=Path,
                        help="top_k断言文件所在目录（如/data/.../top_k）")
    parser.add_argument("--mutants-src-dir", required=True, type=Path,
                        help="变异体源目录（如/data/.../mutants）")
    parser.add_argument("--output-root", default="mutants_IRank", type=Path,
                        help="输出根目录（默认: mutants_IRank）")
    parser.add_argument("--top-module", required=True, type=str,
                        help="顶层模块名（如i2c_master_top）")
    parser.add_argument("--clock", required=True, type=str,
                        help="时钟信号名（如clk_i、wb_clk_i）")
    parser.add_argument("--reset", required=True, type=str,
                        help="复位信号名（如~rst_ni、!nReset）")
    parser.add_argument("--inc-dirs", nargs="+", type=Path, default=[],
                        help="包含目录列表（可选，如/xxx/inc）")
    parser.add_argument("--workers", type=int, default=10,
                        help="并行处理的工作进程数（默认: 10）")
    parser.add_argument("--skip-existing", action="store_true",
                        help="跳过已处理的变异体（避免重复工作）")

    args = parser.parse_args()

    # 验证输入路径
    if not args.top_k_dir.exists():
        logging.error(f"top_k目录不存在: {args.top_k_dir}")
        sys.exit(1)
    if not args.mutants_src_dir.exists():
        logging.error(f"变异体源目录不存在: {args.mutants_src_dir}")
        sys.exit(1)

    # 设置日志
    args.output_root.mkdir(parents=True, exist_ok=True)
    setup_logging(args.output_root)
    logging.info("="*80)
    logging.info("开始执行Mutants IRank验证流程")
    logging.info(f"top_k目录: {args.top_k_dir.resolve()}")
    logging.info(f"变异体源目录: {args.mutants_src_dir.resolve()}")
    logging.info(f"输出根目录: {args.output_root.resolve()}")
    logging.info(f"顶层模块: {args.top_module}")
    logging.info(f"时钟信号: {args.clock}")
    logging.info(f"复位信号: {args.reset}")
    logging.info("="*80)

    # 1. 遍历top_k目录下的JSON文件（top_25.json、top_50.json等）
    top_k_files = sorted([f for f in args.top_k_dir.glob("top_*.json") if f.is_file()])
    if not top_k_files:
        logging.error(f"top_k目录下未找到top_*.json文件: {args.top_k_dir}")
        sys.exit(1)

    for top_k_file in top_k_files:
        # 提取top_k名称（如top_25）
        top_k_name = top_k_file.stem  # 如top_25
        logging.info(f"\n{'='*60}")
        logging.info(f"处理top_k文件: {top_k_file.name} ({top_k_name})")
        logging.info(f"{'='*60}")

        # 2. 读取top_k断言文件，构建模块到SVA的映射
        try:
            with open(top_k_file, 'r', encoding='utf-8') as f:
                top_k_data = json.load(f)
        except Exception as e:
            logging.error(f"读取top_k文件失败 {top_k_file}: {e}", exc_info=True)
            continue

        # 构建module_sva_map: {module_name: [sva_string1, sva_string2, ...]}
        module_sva_map = {}
        for module_name, assertions in top_k_data.items():
            if not isinstance(assertions, list):
                continue
            sva_strings = [assertion.get("sva_string", "") for assertion in assertions if assertion.get("sva_string")]
            module_sva_map[module_name] = sva_strings
            logging.info(f"模块 {module_name}: 提取到 {len(sva_strings)} 个SVA断言")

        total_svas = sum(len(svas) for svas in module_sva_map.values())
        logging.info(f"总计提取到 {total_svas} 个SVA断言")
        if total_svas == 0:
            logging.warning(f"top_k文件 {top_k_file} 中无有效SVA断言，跳过")
            continue

        # 3. 定义top_k的输出目录
        top_k_output_dir = args.output_root / top_k_name
        top_k_output_dir.mkdir(parents=True, exist_ok=True)

        # 4. 获取变异体目录列表（001、002等，按名称排序）
        mutant_dirs = sorted([d for d in args.mutants_src_dir.iterdir() if d.is_dir() and d.name.isdigit()])
        if not mutant_dirs:
            logging.error(f"变异体源目录下未找到数字命名的子目录: {args.mutants_src_dir}")
            continue
        logging.info(f"找到 {len(mutant_dirs)} 个变异体目录")

        # 5. 准备并行处理的参数
        args_list = []
        for mutant_dir in mutant_dirs:
            mutant_dir_name = mutant_dir.name
            # 跳过已处理的变异体（如果指定）
            if args.skip_existing:
                result_file = top_k_output_dir / f"result_{mutant_dir_name}.json"
                if result_file.exists():
                    logging.info(f"跳过已处理的变异体: {mutant_dir_name}")
                    continue
            args_list.append((
                mutant_dir_name,
                args.mutants_src_dir,
                top_k_output_dir,
                module_sva_map,
                args.top_module,
                args.clock,
                args.reset,
                args.inc_dirs
            ))

        # 6. 并行处理变异体
        results = []
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            # 提交任务
            future_to_mutant = {executor.submit(process_single_mutant, args): args[0] for args in args_list}
            # 进度条显示
            with tqdm(total=len(args_list), desc=f"处理 {top_k_name} 变异体") as pbar:
                for future in as_completed(future_to_mutant):
                    mutant_id = future_to_mutant[future]
                    try:
                        result = future.result()
                        results.append(result)
                        # 保存单个变异体的结果
                        result_file = top_k_output_dir / f"result_{mutant_id}.json"
                        with open(result_file, 'w', encoding='utf-8') as f:
                            json.dump(result, f, indent=2, ensure_ascii=False)
                    except Exception as e:
                        logging.error(f"获取变异体 {mutant_id} 结果时发生异常: {e}", exc_info=True)
                        results.append({
                            "mutant_id": mutant_id,
                            "status": "future_exception",
                            "error_message": str(e)
                        })
                    pbar.update(1)

        # 7. 生成top_k的汇总结果
        summary = {
            "top_k": top_k_name,
            "top_k_file": str(top_k_file.resolve()),
            "timestamp": datetime.now().isoformat(),
            "total_mutants": len(mutant_dirs),
            "processed_mutants": len(results),
            "killed_count": sum(1 for r in results if r.get("killed")),
            "survived_count": sum(1 for r in results if not r.get("killed") and r.get("status") == "success"),
            "failed_count": sum(1 for r in results if r.get("status") in ["failed", "exception", "future_exception"]),
            "mutant_results": results
        }

        summary_file = top_k_output_dir / "summary.json"
        with open(summary_file, 'w', encoding='utf-8') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)

        # 打印汇总信息
        logging.info(f"\n{top_k_name} 汇总结果:")
        logging.info(f"总变异体数: {summary['total_mutants']}")
        logging.info(f"已处理数: {summary['processed_mutants']}")
        logging.info(f"被杀死数: {summary['killed_count']}")
        logging.info(f"存活数: {summary['survived_count']}")
        logging.info(f"失败数: {summary['failed_count']}")
        logging.info(f"汇总文件保存至: {summary_file}")

    logging.info("\n" + "="*80)
    logging.info("所有top_k文件处理完成！")
    logging.info("="*80)

if __name__ == "__main__":
    main()