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

# ============================ 生成property_mutation.sva ============================
def generate_property_mutation_sva(
    input_property_path: Path,
    output_property_path: Path,
    sva_strings: List[str],
    indent: str = "  "
) -> bool:
    """
    从原始property.sva读取内容，将SVA断言插入到endmodule前，生成property_mutation.sva
    :param input_property_path: 原始property.sva路径（VERIF_DIR下）
    :param output_property_path: 输出property_mutation.sva路径（ft目录下）
    :param sva_strings: 要插入的SVA断言列表（单个断言）
    :param indent: 缩进字符
    :return: 成功返回True，失败返回False
    """
    try:
        if not input_property_path.exists():
            logging.error(f"原始property.sva文件不存在: {input_property_path}")
            return False
        with open(input_property_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # 拼接SVA，添加缩进（单个断言）
        sva_content = ""
        for sva in sva_strings:
            if not sva.strip():
                continue
            indented_sva = '\n'.join([indent + line for line in sva.strip().split('\n')])
            sva_content += f"{indented_sva}\n"

        # 处理endmodule：从后往前找第一个endmodule，插入SVA
        lines = content.split('\n')
        endmodule_index = -1
        for i in range(len(lines)-1, -1, -1):
            if lines[i].strip() == "endmodule":
                endmodule_index = i
                break
        if endmodule_index == -1:
            content = f"{content.strip()}\n{sva_content}endmodule"
        else:
            lines.insert(endmodule_index, sva_content)
            content = '\n'.join(lines)

        # 写入输出文件
        output_property_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_property_path, 'w', encoding='utf-8') as f:
            f.write(content)

        logging.info(f"Property mutation SVA生成完成: {output_property_path}")
        return True
    except Exception as e:
        logging.error(f"生成property_mutation.sva失败 {output_property_path}: {e}", exc_info=True)
        return False

# ============================ 生成TCL脚本 ============================
def generate_tcl_script(
    output_tcl_path: Path,
    top_module: str,
    clock_signal: str,
    reset_signal: str,
    verif_dir: Path,
    ft_path: Path,
    mutant_sv_path: Path,
) -> bool:
    """
    生成适配binding和property的TCL脚本
    """
    try:
        tcl_template = """# Auto-generated TCL script for assertion mutant verification (binding mode)
# Top module: {top_module}
# Clock: {clock_signal}
# Reset: {reset_signal}

set VERIF_DIR {verif_dir}
set FT_PATH {ft_path}
set TOP {top_module}

set CLOCK {clock_signal}
set RESET {reset_signal}

# 分析变异体的SV文件
analyze -sv12 \\
    {mutant_sv_path}

# 分析SVA文件（binding.sva + property_mutation.sva）
analyze -sva \\
  ${{VERIF_DIR}}/binding.sva \\
  ${{FT_PATH}}/property_mutation.sva

# --- Elaborate ---
elaborate -top ${{TOP}}

# --- Environment Setup ---
clock ${{CLOCK}}
reset ${{RESET}}

# 设置每个属性的验证超时时间为5分钟
# set_prove_per_property_time_limit 5m

# Prove all properties
prove -all

# --- Report ---
report

# Exit
exit -force
"""
        # 填充模板（路径使用绝对路径）
        tcl_content = tcl_template.format(
            top_module=top_module,
            clock_signal=clock_signal,
            reset_signal=reset_signal,
            verif_dir=verif_dir.resolve(),
            ft_path=ft_path.resolve(),
            mutant_sv_path=mutant_sv_path.resolve()
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
    运行JasperGold验证，保存报告
    """
    try:
        # 清理旧项目目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)
        jg_proj_dir.mkdir(parents=True, exist_ok=True)

        # 构建JG命令
        jasper_command = f"jg -batch -proj {jg_proj_dir} -tcl {tcl_path}"
        logging.info(f"运行JG命令: {jasper_command}")

        # 执行命令（设置超时，120分钟）
        process = None
        report_content = ""
        try:
            process = subprocess.Popen(
                jasper_command,
                shell=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                preexec_fn=os.setsid
            )
            stdout, _ = process.communicate(timeout=7200)  # 120分钟超时
            report_content = stdout
        except subprocess.TimeoutExpired:
            logging.warning(f"JG验证超时: {tcl_path.stem}")
            if process:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            report_content = "ERROR: Timeout after 7200 seconds"
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

        # 清理JG项目目录
        if jg_proj_dir.exists():
            shutil.rmtree(jg_proj_dir)

        logging.info(f"JG报告保存完成: {report_path}")
        return True
    except Exception as e:
        logging.error(f"运行JG验证失败 {tcl_path}: {e}", exc_info=True)
        return False

# ============================ 提取验证状态 ============================
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

# ============================ 判断变异体是否被杀死 ============================
def is_mutant_killed(proof_status: Dict[str, Any]) -> bool:
    """
    判断变异体是否被杀死
    杀死条件：编译错误 / proven数量与总断言数不相等 / 验证状态不是proven
    """
    total = proof_status["total_assertions"]
    proven = proof_status["proven_count"]
    overall = proof_status["overall_status"]

    if (overall == "error" or
        (total > 0 and proven != total) or
        overall not in ["proven"]):
        return True
    return False

# ============================ 处理单个（断言+变异体）对 ============================
def process_assertion_mutant_pair(
    args_tuple: Tuple
) -> Dict[str, Any]:
    """
    处理单个断言+变异体对的包装函数（用于并行处理）
    :param args_tuple: 包含所有必要参数的元组
    :return: 处理结果字典
    """
    (
        mutant_dir_name,  # 变异体目录名（如001）
        mutants_src_dir,  # 变异体源目录
        output_root,      # 输出根目录
        assertion_rank,   # 断言排名（整数，如1、2）
        assertion_sva,    # 断言的SVA字符串
        top_module,       # 顶层模块名
        clock_signal,     # 时钟信号
        reset_signal,     # 复位信号
        verif_dir,        # VERIF_DIR路径
    ) = args_tuple

    # 初始化结果
    result = {
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
        mutant_src_dir = mutants_src_dir / mutant_dir_name
        mutant_src_sv = mutant_src_dir / "_combined_rtl_no_comments.sv"
        if not mutant_src_sv.exists():
            mutant_src_sv = mutant_src_dir / "combined_rtl_no_comments.sv"
        if not mutant_src_sv.exists():
            result["error_message"] = f"变异体SV文件不存在: {mutant_src_sv}"
            logging.error(result["error_message"])
            return result

        # 输出路径：output_root / 变异体名 / Rank_排名
        mutant_output_dir = output_root / mutant_dir_name
        rank_dir = mutant_output_dir / f"Rank_{assertion_rank}"
        ft_path = rank_dir / "ft"
        property_mutation_sva_path = ft_path / "property_mutation.sva"
        tcl_path = rank_dir / "tcl" / "mutation.tcl"
        report_path = rank_dir / "rpt" / "mutation.txt"
        jg_proj_dir = rank_dir / "jg_proj"
        result_file = rank_dir / "result.json"

        # 跳过已处理的变异体（如果指定）
        if os.environ.get("SKIP_EXISTING") == "True" and result_file.exists():
            # 读取已有的结果
            with open(result_file, 'r', encoding='utf-8') as f:
                existing_result = json.load(f)
            logging.info(f"跳过已处理的（断言Rank-{assertion_rank} + 变异体{mutant_dir_name}）")
            return existing_result

        result["paths"] = {
            "mutant_src_sv": str(mutant_src_sv),
            "property_mutation_sva": str(property_mutation_sva_path),
            "tcl": str(tcl_path),
            "report": str(report_path),
            "result": str(result_file)
        }

        # 2. 生成property_mutation.sva（单个断言）
        input_property_path = verif_dir / "property.sva"
        if not generate_property_mutation_sva(input_property_path, property_mutation_sva_path, [assertion_sva]):
            result["error_message"] = "生成property_mutation.sva失败"
            logging.error(result["error_message"])
            return result

        # 3. 生成TCL脚本
        if not generate_tcl_script(
            tcl_path,
            top_module,
            clock_signal,
            reset_signal,
            verif_dir,
            ft_path,
            mutant_src_sv,
        ):
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

        # 保存单个结果
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, ensure_ascii=False)

        logging.info(f"处理完成（断言Rank-{assertion_rank} + 变异体{mutant_dir_name}）: {'KILLED' if result['killed'] else 'SURVIVED'}")
    except Exception as e:
        error_msg = f"处理（断言Rank-{assertion_rank} + 变异体{mutant_dir_name}）时发生异常: {str(e)}"
        result["error_message"] = error_msg
        result["status"] = "exception"
        logging.error(error_msg, exc_info=True)

    return result

# ============================ 主函数 ============================
def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description="单个断言对变异体的验证：按Rank统计杀死情况")
    parser.add_argument("--top-proven-loc", required=True, type=Path,
                        help="已证明并排序的Assertion文件路径（如assertion_scores.json）")
    parser.add_argument("--mutants-src-dir", required=True, type=Path,
                        help="变异体源目录（如/data/.../mutants）")
    parser.add_argument("--output-root", default="mutants_assertion_verif", type=Path,
                        help="输出根目录（默认: mutants_assertion_verif）")
    parser.add_argument("--top-module", required=True, type=str,
                        help="顶层模块名（如uart2bus_top）")
    parser.add_argument("--clock", required=True, type=str,
                        help="时钟信号名（如clock）")
    parser.add_argument("--reset", required=True, type=str,
                        help="复位信号名（如reset）")
    parser.add_argument("--verif-dir", required=True, type=Path,
                        help="验证目录（包含binding.sva和property.sva）")
    parser.add_argument("--workers", type=int, default=10,
                        help="并行处理的工作进程数（默认: 10）")
    parser.add_argument("--skip-existing", action="store_true",
                        help="跳过已处理的（断言+变异体）对")

    args = parser.parse_args()

    # 验证输入路径
    if not args.top_proven_loc.exists():
        logging.error(f"Assertion文件不存在: {args.top_proven_loc}")
        sys.exit(1)
    if not args.mutants_src_dir.exists():
        logging.error(f"变异体源目录不存在: {args.mutants_src_dir}")
        sys.exit(1)
    if not args.verif_dir.exists():
        logging.error(f"验证目录不存在: {args.verif_dir}")
        sys.exit(1)
    if not (args.verif_dir / "binding.sva").exists():
        logging.error(f"binding.sva文件不存在: {args.verif_dir / 'binding.sva'}")
        sys.exit(1)
    if not (args.verif_dir / "property.sva").exists():
        logging.error(f"property.sva文件不存在: {args.verif_dir / 'property.sva'}")
        sys.exit(1)

    # 设置日志
    args.output_root.mkdir(parents=True, exist_ok=True)
    setup_logging(args.output_root)
    logging.info("="*80)
    logging.info("开始执行单个断言对变异体的验证流程")
    logging.info(f"Assertion文件: {args.top_proven_loc.resolve()}")
    logging.info(f"变异体源目录: {args.mutants_src_dir.resolve()}")
    logging.info(f"输出根目录: {args.output_root.resolve()}")
    logging.info(f"顶层模块: {args.top_module}")
    logging.info(f"时钟信号: {args.clock}")
    logging.info(f"复位信号: {args.reset}")
    logging.info("="*80)

    # 1. 读取并解析Assertion文件（按Rank排序）
    try:
        with open(args.top_proven_loc, 'r', encoding='utf-8') as f:
            assertion_data = json.load(f)
        # 提取顶层模块的断言（假设是uart2bus_top）
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

    # 2. 获取变异体目录列表
    mutant_dirs = sorted([d for d in args.mutants_src_dir.iterdir() if d.is_dir() and d.name.isdigit()])
    if not mutant_dirs:
        logging.error(f"变异体源目录下未找到数字命名的子目录: {args.mutants_src_dir}")
        sys.exit(1)
    logging.info(f"找到{len(mutant_dirs)}个变异体目录")

    # 3. 准备并行处理的参数列表（每个断言+变异体对为一个任务）
    args_list = []
    for assertion in assertions_sorted:
        rank = assertion["Rank"]
        sva_string = assertion["sva_string"]
        for mutant_dir in mutant_dirs:
            mutant_dir_name = mutant_dir.name
            args_list.append((
                mutant_dir_name,
                args.mutants_src_dir,
                args.output_root,
                rank,
                sva_string,
                args.top_module,
                args.clock,
                args.reset,
                args.verif_dir,
            ))
    # 设置环境变量用于跳过已处理（子进程读取）
    os.environ["SKIP_EXISTING"] = "True" if args.skip_existing else "False"

    # 4. 并行处理（断言+变异体）对
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        future_to_pair = {executor.submit(process_assertion_mutant_pair, args): (args[3], args[0]) for args in args_list}
        with tqdm(total=len(args_list), desc="处理（断言+变异体）对") as pbar:
            for future in as_completed(future_to_pair):
                rank, mutant_id = future_to_pair[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    logging.error(f"获取（断言Rank-{rank} + 变异体{mutant_id}）结果时发生异常: {e}", exc_info=True)
                    results.append({
                        "mutant_id": mutant_id,
                        "assertion_rank": rank,
                        "status": "future_exception",
                        "error_message": str(e)
                    })
                pbar.update(1)

    # 5. 按断言Rank统计结果
    rank_summary = {}
    # 初始化每个Rank的统计
    for assertion in assertions_sorted:
        rank = assertion["Rank"]
        rank_summary[rank] = {
            "rank": rank,
            "sva_string": assertion["sva_string"],
            "total_mutants": len(mutant_dirs),
            "processed_mutants": 0,
            "killed_mutants": [],
            "survived_mutants": [],
            "failed_mutants": [],
            "killed_count": 0,
            "survived_count": 0,
            "failed_count": 0
        }
    # 遍历结果更新统计
    for result in results:
        rank = result["assertion_rank"]
        mutant_id = result["mutant_id"]
        status = result["status"]
        killed = result.get("killed", False)

        if rank not in rank_summary:
            continue  # 忽略无效的rank

        summary = rank_summary[rank]
        summary["processed_mutants"] += 1

        if status == "success":
            if killed:
                summary["killed_mutants"].append(mutant_id)
                summary["killed_count"] += 1
            else:
                summary["survived_mutants"].append(mutant_id)
                summary["survived_count"] += 1
        else:
            summary["failed_mutants"].append(mutant_id)
            summary["failed_count"] += 1

    # 6. 生成最终汇总文件
    final_summary = {
        "timestamp": datetime.now().isoformat(),
        "total_assertions": len(assertions_sorted),
        "total_mutants": len(mutant_dirs),
        "assertion_rank_summary": list(rank_summary.values()),
        "detailed_results": results
    }
    summary_file = args.output_root / "assertion_kill_summary.json"
    with open(summary_file, 'w', encoding='utf-8') as f:
        json.dump(final_summary, f, indent=2, ensure_ascii=False)

    # 打印汇总信息
    logging.info("\n" + "="*80)
    logging.info("按断言Rank统计结果:")
    logging.info(f"总断言数: {final_summary['total_assertions']}")
    logging.info(f"总变异体数: {final_summary['total_mutants']}")
    logging.info("-"*60)
    for rank in sorted(rank_summary.keys()):
        summary = rank_summary[rank]
        logging.info(f"\n断言Rank-{rank}:")
        logging.info(f"  杀死变异体数: {summary['killed_count']} (编号: {','.join(summary['killed_mutants'])})")
        logging.info(f"  存活变异体数: {summary['survived_count']} (编号: {','.join(summary['survived_mutants'])})")
        logging.info(f"  失败变异体数: {summary['failed_count']} (编号: {','.join(summary['failed_mutants'])})")
    logging.info("\n汇总文件保存至: {summary_file}")
    logging.info("="*80)
    logging.info("所有（断言+变异体）对处理完成！")

if __name__ == "__main__":
    main()