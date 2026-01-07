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
    log_file = log_dir / f"assertion_verification_{timestamp}.log"

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(log_file, encoding="utf-8"),
            logging.StreamHandler(sys.stdout)
        ]
    )
    return log_file

# ============================ 核心功能函数（适配单个断言验证正确SV） ============================
def insert_sva_into_module(
    module_content: str,
    module_name: str,
    sva_string: str,
    indent: str = "  "
) -> str:
    """
    将单个SVA字符串插入到指定模块的endmodule之前
    :param module_content: 原始SV文件内容
    :param module_name: 目标模块名
    :param sva_string: 要插入的单个SVA字符串
    :param indent: 缩进字符
    :return: 插入SVA后的模块内容，失败返回原内容
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

def insert_single_sva_into_sv_file(
    input_sv_path: Path,
    output_sv_path: Path,
    module_name: str,
    sva_string: str
) -> bool:
    """
    将单个SVA字符串插入到SV文件的指定模块中，生成新文件
    :param input_sv_path: 输入SV文件路径（正确的SV设计文件）
    :param output_sv_path: 输出SV文件路径（植入SVA后的文件）
    :param module_name: 目标模块名（顶层模块）
    :param sva_string: 要插入的单个SVA字符串
    :return: 成功返回True，失败返回False
    """
    try:
        # 读取原始SV文件内容
        with open(input_sv_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # 插入单个SVA到指定模块
        modified_content = insert_sva_into_module(content, module_name, sva_string)

        # 写入输出文件
        output_sv_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_sv_path, 'w', encoding='utf-8') as f:
            f.write(modified_content)

        logging.info(f"单个SVA植入完成，输出文件: {output_sv_path}")
        return True
    except Exception as e:
        logging.error(f"插入单个SVA到SV文件失败 {input_sv_path}: {e}", exc_info=True)
        return False

def generate_tcl_script(
    output_tcl_path: Path,
    top_module: str,
    clock_signal: str,
    reset_signal: str,
    sv_file_path: Path
) -> bool:
    """
    生成参数化的TCL脚本（适配单个断言验证）
    :param output_tcl_path: 输出TCL文件路径
    :param top_module: 顶层模块名
    :param clock_signal: 时钟信号名（如clk_i）
    :param reset_signal: 复位信号名（如~rst_ni）
    :param sv_file_path: 要分析的SV文件路径（植入SVA后的文件）
    :return: 成功返回True，失败返回False
    """
    try:
        # TCL模板：简化注释，移除inc_dirs相关逻辑
        tcl_template = """# Auto-generated TCL script for assertion verification (correct SV design)
# Top module: {top_module}
# Clock: {clock_signal}
# Reset: {reset_signal}

# Set working directory
cd {work_dir}

# Analyze SV file (single assertion inserted)
analyze -sv12 \\
    {sv_file_path}

# Elaborate top module
elaborate -top {top_module}

# Set clock and reset
clock {clock_signal}
reset {reset_signal}

# Prove all properties (single assertion)
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

def extract_detailed_proof_status(report_content: str) -> Dict[str, Any]:
    """
    从JG报告中提取详细的验证状态
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

def judge_assertion_correctness(proof_status: Dict[str, Any]) -> str:
    """
    判断断言是否正确（基于JG验证结果）
    :param proof_status: 详细的验证状态
    :return: 结果标签（correct/incorrect/unknown/error/timeout）
    """
    overall_status = proof_status["overall_status"]
    total = proof_status["total_assertions"]
    proven = proof_status["proven_count"]
    
    if overall_status == "error":
        return "error"  # 验证过程出错
    elif overall_status == "timeout":
        return "timeout"  # 验证超时
    elif total == 0:
        return "unknown"  # 无断言可验证
    elif overall_status == "proven" and proven == total:
        return "correct"  # 断言被证明，正确
    elif overall_status == "cex":
        return "incorrect"  # 找到反例，断言错误
    else:
        return "unknown"  # 其他情况（如inconclusive）

# ============================ 处理单个断言 ============================
def process_single_assertion(
    args_tuple: Tuple
) -> Dict[str, Any]:
    """
    处理单个断言的包装函数（用于并行处理）
    :param args_tuple: 包含所有必要参数的元组
    :return: 处理结果字典
    """
    (
        assertion_id,     # 断言ID（如1、2、3...）
        assertion_text,   # 断言的SVA字符串
        correct_sv_path,  # 正确的SV设计文件路径
        output_root,      # 输出根目录
        top_module,       # 顶层模块名
        clock_signal,     # 时钟信号
        reset_signal,     # 复位信号
    ) = args_tuple

    # 初始化结果
    result = {
        "assertion_id": assertion_id,
        "assertion_text": assertion_text.strip(),
        "status": "failed",
        "correctness": "unknown",
        "proof_status": {},
        "error_message": "",
        "paths": {}
    }

    try:
        # 1. 定义路径：每个断言生成独立目录
        assertion_dir = output_root / f"assertion_{assertion_id:03d}"
        ft_sv_path = assertion_dir / "ft" / "design_with_assertion.sv"
        tcl_path = assertion_dir / "tcl" / "verification.tcl"
        report_path = assertion_dir / "rpt" / "verification.txt"
        jg_proj_dir = assertion_dir / "jg_proj"
        result_file = assertion_dir / "result.json"

        # 跳过已处理的断言（通过环境变量传递--skip-existing参数）
        if os.environ.get("SKIP_EXISTING") == "True" and result_file.exists():
            # 读取已有的结果
            with open(result_file, 'r', encoding='utf-8') as f:
                existing_result = json.load(f)
            logging.info(f"跳过已处理的断言ID-{assertion_id}")
            return existing_result

        result["paths"] = {
            "correct_sv": str(correct_sv_path),
            "ft_sv": str(ft_sv_path),
            "tcl": str(tcl_path),
            "report": str(report_path),
            "result": str(result_file)
        }

        # 2. 插入单个SVA到正确的SV设计文件
        if not insert_single_sva_into_sv_file(correct_sv_path, ft_sv_path, top_module, assertion_text):
            result["error_message"] = "单个SVA植入失败"
            logging.error(result["error_message"])
            return result

        # 3. 生成TCL脚本
        if not generate_tcl_script(tcl_path, top_module, clock_signal, reset_signal, ft_sv_path):
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

        # 6. 判断断言是否正确
        result["correctness"] = judge_assertion_correctness(proof_status)
        result["status"] = "success"

        # 保存单个结果
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)

        logging.info(f"处理完成断言ID-{assertion_id}: {result['correctness']}")
    except Exception as e:
        error_msg = f"处理断言ID-{assertion_id}时发生异常: {str(e)}"
        result["error_message"] = error_msg
        result["status"] = "exception"
        logging.error(error_msg, exc_info=True)

    return result

# ============================ 主函数 ============================
def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description="验证断言正确性：针对正确的SV设计文件验证每个断言是否正确")
    parser.add_argument("--top-sv-loc", required=True, type=Path,
                        help="正确的SV设计文件路径（如i2c_master_top.sv）")
    parser.add_argument("--assertions-txt-loc", required=True, type=Path,
                        help="断言txt文件路径（每行一个断言，如assertions.txt）")
    parser.add_argument("--output-root", default="assertion_correctness_verif", type=Path,
                        help="输出根目录（默认: assertion_correctness_verif）")
    parser.add_argument("--top-module", required=True, type=str,
                        help="顶层模块名（如i2c_master_top）")
    parser.add_argument("--clock", required=True, type=str,
                        help="时钟信号名（如clk_i、wb_clk_i）")
    parser.add_argument("--reset", required=True, type=str,
                        help="复位信号名（如~rst_ni、!nReset）")
    parser.add_argument("--workers", type=int, default=10,
                        help="并行处理的工作进程数（默认: 10）")
    parser.add_argument("--skip-existing", action="store_true",
                        help="跳过已处理的断言")

    args = parser.parse_args()

    # 验证输入路径
    if not args.top_sv_loc.exists():
        logging.error(f"正确的SV设计文件不存在: {args.top_sv_loc}")
        sys.exit(1)
    if not args.assertions_txt_loc.exists():
        logging.error(f"断言txt文件不存在: {args.assertions_txt_loc}")
        sys.exit(1)

    # 设置日志
    args.output_root.mkdir(parents=True, exist_ok=True)
    setup_logging(args.output_root)
    logging.info("="*80)
    logging.info("开始执行断言正确性验证流程")
    logging.info(f"正确的SV设计文件: {args.top_sv_loc.resolve()}")
    logging.info(f"断言txt文件: {args.assertions_txt_loc.resolve()}")
    logging.info(f"输出根目录: {args.output_root.resolve()}")
    logging.info(f"顶层模块: {args.top_module}")
    logging.info(f"时钟信号: {args.clock}")
    logging.info(f"复位信号: {args.reset}")
    logging.info("="*80)

    # 1. 读取断言txt文件（每行一个断言，过滤空行）
    try:
        with open(args.assertions_txt_loc, 'r', encoding='utf-8') as f:
            assertions = [line.strip() for line in f.readlines() if line.strip()]
        if not assertions:
            logging.error("断言txt文件中无有效断言（空行或全注释）")
            sys.exit(1)
        logging.info(f"成功读取{len(assertions)}个有效断言")
    except Exception as e:
        logging.error(f"读取断言txt文件失败: {e}", exc_info=True)
        sys.exit(1)

    # 2. 准备并行处理的参数列表（每个断言为一个任务）
    args_list = []
    for idx, assertion_text in enumerate(assertions, 1):
        args_list.append((
            idx,                  # 断言ID（从1开始）
            assertion_text,       # 断言字符串
            args.top_sv_loc,      # 正确的SV文件路径
            args.output_root,     # 输出根目录
            args.top_module,      # 顶层模块名
            args.clock,           # 时钟信号
            args.reset,           # 复位信号
        ))
    # 设置环境变量用于跳过已处理（子进程读取）
    os.environ["SKIP_EXISTING"] = "True" if args.skip_existing else "False"

    # 3. 并行处理所有断言
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        future_to_assert = {executor.submit(process_single_assertion, args): args[0] for args in args_list}
        with tqdm(total=len(args_list), desc="验证断言正确性") as pbar:
            for future in as_completed(future_to_assert):
                assert_id = future_to_assert[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    logging.error(f"获取断言ID-{assert_id}结果时发生异常: {e}", exc_info=True)
                    results.append({
                        "assertion_id": assert_id,
                        "assertion_text": "",
                        "status": "future_exception",
                        "error_message": str(e)
                    })
                pbar.update(1)

    # 4. 统计结果
    summary = {
        "timestamp": datetime.now().isoformat(),
        "total_assertions": len(assertions),
        "processed_assertions": 0,
        "correct_assertions": [],    # 正确的断言ID
        "incorrect_assertions": [],  # 错误的断言ID
        "timeout_assertions": [],    # 超时的断言ID
        "error_assertions": [],      # 验证出错的断言ID
        "unknown_assertions": [],    # 无法判断的断言ID
        "exception_assertions": [],  # 处理异常的断言ID
        "detailed_results": results
    }

    for result in results:
        assert_id = result["assertion_id"]
        status = result["status"]
        correctness = result.get("correctness", "unknown")

        summary["processed_assertions"] += 1

        if status == "success":
            if correctness == "correct":
                summary["correct_assertions"].append(assert_id)
            elif correctness == "incorrect":
                summary["incorrect_assertions"].append(assert_id)
            elif correctness == "timeout":
                summary["timeout_assertions"].append(assert_id)
            elif correctness == "error":
                summary["error_assertions"].append(assert_id)
            else:
                summary["unknown_assertions"].append(assert_id)
        elif status == "exception":
            summary["exception_assertions"].append(assert_id)
        else:
            summary["unknown_assertions"].append(assert_id)

    # 5. 生成最终汇总文件
    summary_file = args.output_root / "assertion_correctness_summary.json"
    with open(summary_file, 'w', encoding='utf-8') as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)

    # 打印汇总信息
    logging.info("\n" + "="*80)
    logging.info("断言正确性验证汇总结果:")
    logging.info(f"总断言数: {summary['total_assertions']}")
    logging.info(f"已处理断言数: {summary['processed_assertions']}")
    logging.info("-"*60)
    logging.info(f"正确的断言数: {len(summary['correct_assertions'])} (ID: {','.join(map(str, summary['correct_assertions'])) if summary['correct_assertions'] else '无'})")
    logging.info(f"错误的断言数: {len(summary['incorrect_assertions'])} (ID: {','.join(map(str, summary['incorrect_assertions'])) if summary['incorrect_assertions'] else '无'})")
    logging.info(f"验证超时的断言数: {len(summary['timeout_assertions'])} (ID: {','.join(map(str, summary['timeout_assertions'])) if summary['timeout_assertions'] else '无'})")
    logging.info(f"验证出错的断言数: {len(summary['error_assertions'])} (ID: {','.join(map(str, summary['error_assertions'])) if summary['error_assertions'] else '无'})")
    logging.info(f"无法判断的断言数: {len(summary['unknown_assertions'])} (ID: {','.join(map(str, summary['unknown_assertions'])) if summary['unknown_assertions'] else '无'})")
    logging.info(f"处理异常的断言数: {len(summary['exception_assertions'])} (ID: {','.join(map(str, summary['exception_assertions'])) if summary['exception_assertions'] else '无'})")
    logging.info(f"\n汇总文件保存至: {summary_file}")
    logging.info("="*80)
    logging.info("所有断言验证完成！")

if __name__ == "__main__":
    main()