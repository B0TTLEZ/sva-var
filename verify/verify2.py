import argparse
from collections import OrderedDict
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import logging
import os
import re
import shutil
import signal
import subprocess
import sys
import time
import traceback
import copy

from datetime import datetime
from typing import Any, Dict, List, Tuple
from tqdm import tqdm
from pathlib import Path

current_file = Path(__file__).resolve()
project_root = current_file.parent.parent
sys.path.insert(0, str(project_root))

import re
import json
from pathlib import Path
from typing import Any, Dict, List

def parse_sva_from_json_files_structured(
    sva_files: List[Path], default_module_name: str = "ibex_if_stage"
) -> Dict[str, Dict[str, List[Dict[str, Any]]]]:
    """
    从多个JSON格式的SVA文件中解析所有断言，支持大模型回复的非标准格式。
    处理被 ```json ``` 包围的JSON内容。

    Args:
        sva_files (List[Path]): SVA文件的路径列表。
        default_module_name (str): 目标模块名称，默认为 "ibex_if_stage"。

    Returns:
        Dict[str, Dict[str, List[Dict[str, Any]]]]:
        一个嵌套字典，结构为: {module_name: {variable_name: [sva_dicts]}}
        每个 sva_dict 包含 'sva_string', 'status', 和 'sva_id'。
    """
    structured_svas = {}

    if default_module_name not in structured_svas:
        structured_svas[default_module_name] = {}

    for sva_file in sva_files:
        variable_name = sva_file.stem  # e.g., "boot_addr_i"
        
        if variable_name not in structured_svas[default_module_name]:
            structured_svas[default_module_name][variable_name] = []
        
        try:
            # 读取文件内容
            with open(sva_file, 'r', encoding='utf-8') as f:
                content = f.read().strip()
            
            # 处理大模型回复的非标准格式
            json_content = extract_json_from_llm_response(content)
            
            if not json_content:
                logging.warning(f"No valid JSON content found in {sva_file}")
                continue
                
            # 解析JSON
            data = json.loads(json_content)
            
            # 处理不同的JSON结构
            if isinstance(data, list):
                # 如果是列表格式，直接处理
                sva_list = data
            elif isinstance(data, dict) and "assertions" in data:
                # 如果是字典格式，包含assertions字段
                sva_list = data["assertions"]
            elif isinstance(data, dict) and "svas" in data:
                # 如果是字典格式，包含svas字段
                sva_list = data["svas"]
            else:
                # 其他格式，尝试作为列表处理
                sva_list = [data] if isinstance(data, dict) else []
            
            # 处理每条断言
            for i, item in enumerate(sva_list):
                sva_string = extract_sva_string(item)
                if sva_string:
                    # 创建唯一的、可预测的ID
                    sva_id = f"{default_module_name}_{variable_name}_{i}"
                    
                    sva_dict = {
                        "sva_id": sva_id,
                        "sva_string": sva_string,
                        "status": "unknown",
                        "variable_name": variable_name,
                        "index": i
                    }
                    structured_svas[default_module_name][variable_name].append(sva_dict)
                    
        except (json.JSONDecodeError, KeyError, Exception) as e:
            logging.error(f"Failed to parse {sva_file}: {e}")
            logging.debug(f"Problematic content: {content[:200]}...")
            
    return structured_svas

def extract_json_from_llm_response(content: str) -> str:
    """
    从大模型回复中提取JSON内容。
    处理以下格式：
    1. ```json ... ```
    2. ``` ... ``` (无语言标记)
    3. 纯JSON
    4. 包含解释文本的回复
    """
    # 移除前后的空白字符
    content = content.strip()
    
    # 情况1: 被 ```json ``` 包围
    json_match = re.search(r'```json\s*(.*?)\s*```', content, re.DOTALL)
    if json_match:
        return json_match.group(1).strip()
    
    # 情况2: 被 ``` ``` 包围 (无语言标记)
    code_match = re.search(r'```\s*(.*?)\s*```', content, re.DOTALL)
    if code_match:
        return code_match.group(1).strip()
    
    # 情况3: 尝试直接查找JSON数组或对象
    # 查找以 [ 开头 ] 结尾的内容
    array_match = re.search(r'(\[.*\])', content, re.DOTALL)
    if array_match:
        return array_match.group(1).strip()
    
    # 查找以 { 开头 } 结尾的内容
    object_match = re.search(r'(\{.*\})', content, re.DOTALL)
    if object_match:
        return object_match.group(1).strip()
    
    # 情况4: 如果以上都不匹配，返回原始内容（可能是纯JSON）
    return content

def extract_sva_string(item: Any) -> str:
    """
    从JSON项中提取SVA字符串。
    支持多种可能的字段名。
    """
    if isinstance(item, str):
        return item.strip()
    
    if isinstance(item, dict):
        # 尝试不同的字段名
        possible_fields = [
            "assertion", "sva", "property", "assert", 
            "sva_string", "property_string", "assertion_string"
        ]
        
        for field in possible_fields:
            if field in item and isinstance(item[field], str):
                return item[field].strip()
        
        # 如果没有找到标准字段，尝试第一个字符串值
        for value in item.values():
            if isinstance(value, str) and value.strip():
                return value.strip()
    
    return ""

def insert_single_sva_into_module(
    original_rtl_file: Path,
    target_module_name: str,
    sva_to_insert: str,
    output_rtl_file: Path,
    indent: str = "  ",
) -> bool:
    """
    在Verilog文件的指定模块的endmodule之前插入单个SVA。
    专门用于 ibex_if_stage.sv 文件。

    Args:
        original_rtl_file (Path): 原始RTL文件的路径。
        target_module_name (str): 目标模块的名称。
        sva_to_insert (str): 要插入的SystemVerilog断言字符串。
        output_rtl_file (Path): 输出文件的路径。
        indent (str): 插入SVA时使用的缩进字符串。

    Returns:
        bool: 如果成功插入SVA则返回True，否则返回False。
    """
    try:
        with open(original_rtl_file, "r", encoding="utf-8") as f:
            content = f.read()

        # 查找模块的结束位置
        module_pattern = re.compile(
            rf"^\s*module\s+{re.escape(target_module_name)}\b.*?^endmodule",
            re.MULTILINE | re.DOTALL
        )
        
        match = module_pattern.search(content)
        if not match:
            logging.error(f"Module '{target_module_name}' not found in {original_rtl_file}")
            return False

        module_content = match.group(0)
        
        # 在 endmodule 前插入 SVA
        sva_indented = '\n'.join([indent + line for line in sva_to_insert.strip().split('\n')])
        modified_module = module_content.replace(
            "endmodule",
            f"{sva_indented}\nendmodule"
        )
        
        # 替换整个模块内容
        modified_content = content[:match.start()] + modified_module + content[match.end():]
        
        # 写入输出文件
        with open(output_rtl_file, "w", encoding="utf-8") as f:
            f.write(modified_content)

        logging.info(f"Successfully inserted SVA into {output_rtl_file}")
        return True

    except Exception as e:
        logging.error(f"Error inserting SVA into {original_rtl_file}: {e}")
        return False

def create_ibex_file_list(ibex_rtl_dir: Path) -> List[Path]:
    """
    创建 Ibex 设计所需的文件列表。
    """
    file_list = [
        ibex_rtl_dir/ "ibex_pkg.sv",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_assert_dummy_macros.svh",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_assert_yosys_macros.svh",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_assert_standard_macros.svh",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_assert_sec_cm.svh",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_flop_macros.sv",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv",
        ibex_rtl_dir.parent / "vendor/lowrisc_ip/dv/sv/dv_utils/dv_fcov_macros.svh",
        ibex_rtl_dir / "ibex_alu.sv",
        ibex_rtl_dir / "ibex_compressed_decoder.sv",
        ibex_rtl_dir / "ibex_controller.sv",
        ibex_rtl_dir / "ibex_counter.sv",
        ibex_rtl_dir / "ibex_cs_registers.sv",
        ibex_rtl_dir / "ibex_decoder.sv",
        ibex_rtl_dir / "ibex_ex_block.sv",
        ibex_rtl_dir / "ibex_id_stage.sv",
        ibex_rtl_dir / "ibex_if_stage.sv",  # 主要目标文件
        ibex_rtl_dir / "ibex_prefetch_buffer.sv",
        ibex_rtl_dir / "ibex_fetch_fifo.sv",
        ibex_rtl_dir / "ibex_register_file_ff.sv",
        ibex_rtl_dir / "ibex_core.sv",
    ]
    
    # 检查文件是否存在
    existing_files = [f for f in file_list if f.exists()]
    missing_files = [f for f in file_list if not f.exists()]
    
    if missing_files:
        logging.warning(f"Missing files: {missing_files}")
    
    return existing_files

def create_fpv_tcl_template():
    """
    创建 FPV TCL 模板。
    """
    return """# FPV TCL script for Ibex if_stage verification



# Analyze all required files
analyze -sv12 \\
    +incdir+{prim_assert_dir} \\
    +incdir+{dv_utils_dir} \\
    +incdir+{rtl_dir} \\
    -f {file_list_path}

# Elaborate the top module
elaborate -top {top_module}

# Set clock and reset
clock {clock_signal}
reset {reset_signal}


set_max_trace_length 100

# Prove all properties
prove -all

# Exit
exit -force
"""

def generate_fpv_tcl(
    output_path: Path,
    prim_assert_dir: Path,
    dv_utils_dir: Path,
    rtl_dir: Path,
    file_list_path: Path,
    top_module: str = "ibex_if_stage",
    clock_signal: str = "clk_i",
    reset_signal: str = "~rst_ni"
) -> bool:
    """
    生成 FPV TCL 脚本。
    """
    try:
        template = create_fpv_tcl_template()
        tcl_content = template.format(
            prim_assert_dir=prim_assert_dir,
            dv_utils_dir=dv_utils_dir,
            rtl_dir=rtl_dir,
            file_list_path=file_list_path,
            top_module=top_module,
            clock_signal=clock_signal,
            reset_signal=reset_signal
        )
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(tcl_content)
        
        logging.info(f"Generated FPV TCL script: {output_path}")
        return True
    except Exception as e:
        logging.error(f"Error generating FPV TCL script: {e}")
        return False

def extract_proof_status(report_content: str) -> str:
    """
    从 JasperGold 报告中提取断言证明状态（简化版）。
    """
    if "ERROR" in report_content:
        return "error"
    
    # 查找断言总数和证明数
    total_match = re.search(r"assertions\s*:\s*(\d+)", report_content)
    proven_match = re.search(r"- proven\s*:\s*(\d+)", report_content)
    
    if total_match and proven_match:
        total_assertions = int(total_match.group(1))
        proven_assertions = int(proven_match.group(1))
        
        if proven_assertions == total_assertions and total_assertions > 0:
            return "proven"
        elif proven_assertions > 0:
            return "partial_proven"
    
    # 检查其他状态
    if re.search(r"- cex\s*:\s*(\d+)", report_content) or re.search(r"- ar_cex\s*:\s*(\d+)", report_content):
        return "cex"
    elif re.search(r"- timeout\s*:\s*(\d+)", report_content):
        return "timeout"
    elif re.search(r"- undetermined\s*:\s*(\d+)", report_content) or re.search(r"- unknown\s*:\s*(\d+)", report_content):
        return "inconclusive"
    
    return "inconclusive"



def run_single_jg_verification(args_tuple):
    """
    运行单个 JasperGold 验证的包装函数，用于并行处理。
    
    Args:
        args_tuple: (tcl_file_path, jg_dir, rpt_dir, sva_id)
    
    Returns:
        tuple: (sva_id, report_file_path, success, error_message)
    """
    tcl_file_path, jg_dir, rpt_dir, sva_id = args_tuple
    
    try:
        project_dir = jg_dir / sva_id
        
        if project_dir.exists():
            shutil.rmtree(project_dir)
        project_dir.mkdir(parents=True, exist_ok=True)

        jasper_command = f"jg -batch -proj {project_dir} -tcl {tcl_file_path}"
        
        process = None
        report = ""

        try:
            process = subprocess.Popen(
                jasper_command,
                shell=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                preexec_fn=os.setsid,
            )
            
            stdout, _ = process.communicate(timeout=300)  # 5分钟超时
            report = stdout

        except subprocess.TimeoutExpired:
            logging.warning(f"JasperGold timeout for {sva_id}")
            if process:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except:
                    pass
            report = "ERROR: Timeout after 300 seconds"
            
        except Exception as e:
            logging.error(f"Error running JasperGold for {sva_id}: {str(e)}")
            report = f"Error: {str(e)}\n"

        finally:
            if process and process.poll() is None:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except Exception:
                    pass

        report_file_path = rpt_dir / f"{sva_id}.txt"
        report_file_path.write_text(report, encoding="utf-8")
        
        return (sva_id, report_file_path, True, "")

    except Exception as e:
        logging.error(f"Unexpected error for {sva_id}: {str(e)}")
        return (sva_id, None, False, str(e))

def run_jg_parallel(tcl_paths: List[Path], jg_dir: Path, rpt_dir: Path, max_workers: int = None) -> Dict[str, Path]:
    """
    并行运行多个 JasperGold 验证（改进版本，支持中断）。
    """
    if max_workers is None:
        max_workers = min(max(1, int(multiprocessing.cpu_count() * 0.75)), 16)
    
    logging.info(f"Starting parallel JasperGold runs with {max_workers} workers")
    
    # 准备参数
    args_list = []
    for tcl_path in tcl_paths:
        sva_id = tcl_path.stem
        args_list.append((tcl_path, jg_dir, rpt_dir, sva_id))
    
    results = {}
    completed_count = 0
    total_count = len(args_list)
    
    try:
        # 使用进程池并行执行
        with ProcessPoolExecutor(max_workers=max_workers) as executor:
            # 提交所有任务
            future_to_sva = {
                executor.submit(run_single_jg_verification, args): args[3]
                for args in args_list
            }
            
            # 使用tqdm显示进度
            with tqdm(total=total_count, desc="Running JasperGold") as pbar:
                for future in as_completed(future_to_sva):
                    sva_id = future_to_sva[future]
                    try:
                        # 添加超时
                        sva_id, report_path, success, error_msg = future.result(timeout=600)  # 10分钟超时
                        if success and report_path:
                            results[sva_id] = report_path
                        else:
                            logging.error(f"Failed to run {sva_id}: {error_msg}")
                            error_report = rpt_dir / f"{sva_id}.txt"
                            error_report.write_text(f"ERROR: {error_msg}", encoding="utf-8")
                            results[sva_id] = error_report
                        
                        completed_count += 1
                        pbar.update(1)
                        pbar.set_postfix_str(f"{completed_count}/{total_count}")
                        
                    except TimeoutError:
                        logging.error(f"Timeout for {sva_id}")
                        error_report = rpt_dir / f"{sva_id}.txt"
                        error_report.write_text("ERROR: Timeout after 600 seconds", encoding="utf-8")
                        results[sva_id] = error_report
                        completed_count += 1
                        pbar.update(1)
                        
                    except Exception as e:
                        logging.error(f"Exception in {sva_id}: {str(e)}")
                        error_report = rpt_dir / f"{sva_id}.txt"
                        error_report.write_text(f"EXCEPTION: {str(e)}", encoding="utf-8")
                        results[sva_id] = error_report
                        completed_count += 1
                        pbar.update(1)
    
    except KeyboardInterrupt:
        logging.info("Received interrupt signal, shutting down...")
        # 尝试优雅关闭执行器
        executor.shutdown(wait=False)
        raise
    
    logging.info(f"Completed {completed_count}/{total_count} JasperGold runs")
    return results

def run_ibex_verification(
    design_name: str,
    ibex_rtl_dir: Path,
    sva_dir: Path,
    output_dir: Path,
    max_workers: int = None
) -> Dict[str, Any]:
    """
    运行 Ibex if_stage 模块的验证（并行版本）。
    """
    verif_dir = output_dir / "verif"
    if verif_dir.exists():
        shutil.rmtree(verif_dir)
    verif_dir.mkdir(parents=True, exist_ok=True)

    try:
        # 1. 解析 SVA 文件
        logging.info(f"Parsing SVA files from {sva_dir}")
        sva_files = [f for f in sva_dir.glob("*.sv") if f.is_file()]  # 修正：应该是.json文件
        all_svas = parse_sva_from_json_files_structured(sva_files, "ibex_if_stage")
        
        total_sva_count = sum(len(v) for v in all_svas["ibex_if_stage"].values())
        logging.info(f"Found {total_sva_count} assertions for '{design_name}'.")
        
        # # ========== 添加这行代码来限制断言数量 ==========
        # # 只取前5个变量，每个变量只取前2条断言进行测试
        # test_svas = {}
        # test_count = 0
        # max_per_variable = 2
        # max_variables = 3
        
        # for i, (variable_name, assertions) in enumerate(all_svas["ibex_if_stage"].items()):
        #     if i >= max_variables:
        #         break
        #     test_svas[variable_name] = assertions[:max_per_variable]
        #     test_count += len(assertions[:max_per_variable])
        
        # all_svas["ibex_if_stage"] = test_svas
        # total_sva_count = test_count
        # logging.info(f"TEST MODE: Using {total_sva_count} assertions for testing")
        # # ========== 添加结束 ==========

        if total_sva_count == 0:
            return {
                "task_status": "no_assertions",
                "assertion_status_counts": {"total": 0},
                "sva_details": {}
            }

        # 2. 创建文件列表
        file_list_dir= verif_dir / "filelist"
        file_list_dir.mkdir(parents=True, exist_ok=True)
        file_list_path = verif_dir / "filelist" /"ibex_files.f"
        ibex_files = create_ibex_file_list(ibex_rtl_dir)
        
        with open(file_list_path, 'w', encoding='utf-8') as f:
            for file_path in ibex_files:
                f.write(f"{file_path}\n")
        
        logging.info(f"Created file list with {len(ibex_files)} files")

        # 3. 为每个断言创建验证环境
        ft_dir = verif_dir / "ft_rtl"
        tcl_dir = verif_dir / "tcl"
        jg_dir = verif_dir / "jg"
        rpt_dir = verif_dir / "rpt"
        
        for dir_path in [ft_dir, tcl_dir, jg_dir, rpt_dir]:
            dir_path.mkdir(parents=True, exist_ok=True)

        # 获取目录路径
        prim_assert_dir = ibex_rtl_dir.parent / "vendor/lowrisc_ip/ip/prim/rtl"
        dv_utils_dir = ibex_rtl_dir.parent / "vendor/lowrisc_ip/dv/sv/dv_utils"
        rtl_dir = ibex_rtl_dir

        tcl_paths = []
        sva_mapping = {}

        # 为每个断言创建单独的验证
        logging.info("Creating verification environments for each assertion...")
        for variable_name, assertions in tqdm(all_svas["ibex_if_stage"].items(), desc="Creating environments"):
            for sva_dict in assertions:
                sva_id = sva_dict["sva_id"]
                
                # 创建包含该断言的 RTL 文件
                ft_rtl_file = ft_dir / f"{sva_id}.sv"
                original_if_stage = ibex_rtl_dir / "ibex_if_stage.sv"
                
                if not insert_single_sva_into_module(
                    original_if_stage,
                    "ibex_if_stage",
                    sva_dict["sva_string"],
                    ft_rtl_file
                ):
                    logging.error(f"Failed to insert SVA {sva_id}")
                    continue

                # 创建文件列表（包含修改后的 if_stage）
                sva_file_list = file_list_dir / f"{sva_id}.f"
                with open(sva_file_list, 'w', encoding='utf-8') as f:
                    for file_path in ibex_files:
                        if file_path.name == "ibex_if_stage.sv":
                            f.write(f"{ft_rtl_file}\n")  # 使用修改后的文件
                        else:
                            f.write(f"{file_path}\n")

                # 生成 TCL 脚本
                tcl_path = tcl_dir / f"{sva_id}.tcl"
                if generate_fpv_tcl(
                    tcl_path,
                    prim_assert_dir,
                    dv_utils_dir,
                    rtl_dir,
                    sva_file_list,
                    top_module="ibex_if_stage",
                    clock_signal="clk_i",
                    reset_signal="~rst_ni"
                ):
                    tcl_paths.append(tcl_path)
                    sva_mapping[tcl_path.stem] = sva_dict

        logging.info(f"Created {len(tcl_paths)} verification setups")

        # 4. 并行运行验证
        logging.info(f"Starting parallel JasperGold runs for {len(tcl_paths)} assertions...")
        rpt_paths_dict = run_jg_parallel(tcl_paths, jg_dir, rpt_dir, max_workers)

        # 5. 分析结果
        logging.info("Analyzing verification results...")
        status_counts = {
            "proven": 0,
            "cex": 0, 
            "inconclusive": 0,
            "error": 0,
            "timeout": 0,
            "unknown": 0,
            "total": total_sva_count
        }

        # 更新每个断言的状态
        for sva_id, rpt_path in rpt_paths_dict.items():
            if sva_id in sva_mapping:
                try:
                    report_content = rpt_path.read_text(encoding="utf-8")
                    status = extract_proof_status(report_content)
                    sva_mapping[sva_id]["status"] = status
                    status_counts[status] = status_counts.get(status, 0) + 1
                except Exception as e:
                    logging.error(f"Error reading report {rpt_path}: {e}")
                    sva_mapping[sva_id]["status"] = "error"
                    status_counts["error"] += 1

        # 6. 保存结果
        sva_status_file = verif_dir / "sva_status.json"
        with open(sva_status_file, 'w', encoding='utf-8') as f:
            json.dump(all_svas, f, indent=2, ensure_ascii=False)

        # 按变量统计结果
        variable_stats = {}
        for variable_name, assertions in all_svas["ibex_if_stage"].items():
            variable_stats[variable_name] = {
                "total": len(assertions),
                "proven": sum(1 for a in assertions if a.get("status") == "proven"),
                "cex": sum(1 for a in assertions if a.get("status") == "cex"),
                "inconclusive": sum(1 for a in assertions if a.get("status") == "inconclusive"),
                "error": sum(1 for a in assertions if a.get("status") == "error"),
            }

        # 确定总体状态
        if status_counts["proven"] == total_sva_count:
            task_status = "passed"
        elif status_counts["error"] == total_sva_count:
            task_status = "failed" 
        elif status_counts["proven"] > 0:
            task_status = "partial_pass"
        else:
            task_status = "inconclusive"

        result = {
            "task_status": task_status,
            "assertion_status_counts": status_counts,
            "variable_statistics": variable_stats,
            "sva_details": all_svas,
            "verification_directory": str(verif_dir),
            "parallel_config": {
                "max_workers": max_workers,
                "total_assertions": total_sva_count
            }
        }

        logging.info(f"Verification completed. Task status: {task_status}")
        return result

    except Exception as e:
        logging.error(f"Error during verification: {e}", exc_info=True)
        return {
            "task_status": "failed",
            "error_message": str(e)
        }

def extract_json_from_mutant_file(content: str) -> str:
    """
    从突变文件中提取JSON内容。
    处理大模型回复的非标准格式。
    """
    # 移除前后的空白字符
    content = content.strip()
    
    # 情况1: 被 ```json ``` 包围
    json_match = re.search(r'```json\s*(.*?)\s*```', content, re.DOTALL)
    if json_match:
        return json_match.group(1).strip()
    
    # 情况2: 被 ``` ``` 包围 (无语言标记)
    code_match = re.search(r'```\s*(.*?)\s*```', content, re.DOTALL)
    if code_match:
        return code_match.group(1).strip()
    
    # 情况3: 尝试直接查找JSON数组或对象
    # 查找以 [ 开头 ] 结尾的内容
    array_match = re.search(r'(\[.*\])', content, re.DOTALL)
    if array_match:
        return array_match.group(1).strip()
    
    # 查找以 { 开头 } 结尾的内容
    object_match = re.search(r'(\{.*\})', content, re.DOTALL)
    if object_match:
        return object_match.group(1).strip()
    
    # 情况4: 如果以上都不匹配，返回原始内容（可能是纯JSON）
    return content

def load_mutations_from_file(mutant_file: Path) -> List[Dict]:
    """
    从突变文件中加载突变体，处理大模型回复格式。
    """
    try:
        with open(mutant_file, 'r', encoding='utf-8') as f:
            content = f.read().strip()
        
        # 处理大模型回复的非标准格式
        json_content = extract_json_from_mutant_file(content)
        
        if not json_content:
            logging.warning(f"No valid JSON content found in {mutant_file}")
            return []
            
        # 解析JSON
        data = json.loads(json_content)
        
        # 确保返回的是列表
        if isinstance(data, list):
            return data
        elif isinstance(data, dict):
            return [data]  # 如果是字典，包装成列表
        else:
            logging.warning(f"Unexpected data format in {mutant_file}: {type(data)}")
            return []
            
    except (json.JSONDecodeError, Exception) as e:
        logging.error(f"Failed to parse mutation file {mutant_file}: {e}")
        logging.debug(f"Problematic content: {content[:200]}...")
        return []

def apply_single_mutation(original_rtl_content: str, mutation: Dict) -> str:
    """
    在原始RTL内容中应用单个突变。
    """
    original_code = mutation["original_code_slice"]
    mutation_code = mutation["mutation_code_slice"]
    
    # 确保代码片段有正确的换行符
    original_code = original_code.replace('\\n', '\n')
    mutation_code = mutation_code.replace('\\n', '\n')
    
    if original_code in original_rtl_content:
        mutated_content = original_rtl_content.replace(original_code, mutation_code)
        return mutated_content
    else:
        # 尝试处理可能的格式差异（如多余的空格、换行符等）
        # 将代码片段标准化（移除多余空格和换行符）
        normalized_original = re.sub(r'\s+', ' ', original_code).strip()
        normalized_rtl = re.sub(r'\s+', ' ', original_rtl_content).strip()
        
        if normalized_original in normalized_rtl:
            # 如果标准化后能找到，使用正则表达式进行精确替换
            pattern = re.escape(original_code).replace(r'\ ', r'\s+')
            mutated_content = re.sub(pattern, mutation_code, original_rtl_content)
            return mutated_content
        else:
            logging.warning(f"Original code not found for mutation. Searching for: {original_code[:50]}...")
            # 尝试部分匹配
            lines = original_code.split('\n')
            if len(lines) > 1:
                # 尝试匹配第一行
                first_line = lines[0].strip()
                if first_line in original_rtl_content:
                    logging.info(f"Found partial match for first line, applying mutation to first line only")
                    mutated_content = original_rtl_content.replace(first_line, mutation_code.split('\n')[0].strip())
                    return mutated_content
            
            return original_rtl_content

def run_jg_single(tcl_file_path: Path, jg_dir: Path, rpt_dir: Path) -> Path:
    """
    运行单个 JasperGold 验证。
    """
    sva_name = tcl_file_path.stem
    project_dir = jg_dir / sva_name
    
    if project_dir.exists():
        shutil.rmtree(project_dir)
    project_dir.mkdir(parents=True, exist_ok=True)

    jasper_command = f"jg -batch -proj {project_dir} -tcl {tcl_file_path}"
    logging.info(f"Running: {jasper_command}")
    
    process = None
    report = ""

    try:
        process = subprocess.Popen(
            jasper_command,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            preexec_fn=os.setsid,
        )
        
        stdout, _ = process.communicate()
        report = stdout
        logging.info(f"JasperGold for {sva_name} exited with code: {process.returncode}")

    except Exception as e:
        logging.error(f"Error running JasperGold for {sva_name}: {str(e)}")
        report = f"Error: {str(e)}\n"

    finally:
        if process and process.poll() is None:
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                logging.info(f"Terminated running process for {sva_name}")
            except Exception as e:
                logging.error(f"Failed to terminate process for {sva_name}: {str(e)}")

    report_file_path = rpt_dir / f"{sva_name}.txt"
    report_file_path.write_text(report, encoding="utf-8")
    logging.info(f"Saved report to: {report_file_path}")
    return report_file_path

def insert_sva_into_module_content(
    module_content: str,
    target_module_name: str,
    sva_to_insert: str,
    indent: str = "  "
) -> str:
    """
    在模块内容字符串中的endmodule之前插入SVA。
    
    Args:
        module_content: 模块内容字符串
        target_module_name: 目标模块名称
        sva_to_insert: 要插入的SVA字符串
        indent: 缩进字符串
        
    Returns:
        str: 插入SVA后的模块内容，如果失败返回None
    """
    try:
        # 查找模块的结束位置
        module_pattern = re.compile(
            rf"^\s*module\s+{re.escape(target_module_name)}\b.*?^endmodule",
            re.MULTILINE | re.DOTALL
        )
        
        match = module_pattern.search(module_content)
        if not match:
            logging.error(f"Module '{target_module_name}' not found in content")
            return None

        module_content_str = match.group(0)
        
        # 在 endmodule 前插入 SVA
        sva_indented = '\n'.join([indent + line for line in sva_to_insert.strip().split('\n')])
        modified_module = module_content_str.replace(
            "endmodule",
            f"{sva_indented}\nendmodule"
        )
        
        # 替换整个模块内容
        modified_content = module_content[:match.start()] + modified_module + module_content[match.end():]
        
        return modified_content

    except Exception as e:
        logging.error(f"Error inserting SVA into module content: {e}")
        return None

def run_mutation_test_for_single_assertion(args_tuple):
    """
    对单个断言运行突变测试的包装函数，用于并行处理。
    """
    (assertion, original_rtl_file, mutants_dir, mutation_output_dir, 
     ibex_files, prim_assert_dir, dv_utils_dir, rtl_dir) = args_tuple
    
    sva_id = assertion["sva_id"]
    sva_string = assertion["sva_string"]
    
    try:
        # 读取原始RTL内容
        with open(original_rtl_file, 'r', encoding='utf-8') as f:
            original_rtl_content = f.read()
        
        mutation_results = {}
        total_mutations = 0
        killed_mutations = 0
        
        # 获取所有突变文件
        mutant_files = list(mutants_dir.glob("*.sv"))
        # # ========== 添加突变体测试限制代码 ==========
        # # 只取前2个突变文件，每个文件只取前3个突变体进行测试
        # max_mutant_files = 5
        # max_mutations_per_file = 5
        # mutant_files = mutant_files[:max_mutant_files]
        # logging.info(f"TEST MODE: Using {len(mutant_files)} mutant files for testing")
        # # ========== 添加结束 ==========
        for mutant_file in mutant_files:
            # 加载突变文件中的所有突变体
            mutations = load_mutations_from_file(mutant_file)
            
            if not mutations:
                logging.warning(f"No valid mutations found in {mutant_file}")
                continue
            # # ========== 添加突变体数量限制 ==========
            # # 每个文件只取前几个突变体
            # mutations = mutations[:max_mutations_per_file]
            # logging.info(f"  File {mutant_file.name}: using {len(mutations)} mutations")
            # # ========== 添加结束 ==========
            # 对文件中的每个突变体单独测试
            for i, mutation in enumerate(mutations):
                mutation_id = f"{mutant_file.stem}_{i}"
                total_mutations += 1
                
                try:
                    # 1. 应用单个突变
                    mutated_content = apply_single_mutation(original_rtl_content, mutation)
                    
                    # 如果突变失败（内容没有变化），跳过这个突变
                    if mutated_content == original_rtl_content:
                        logging.warning(f"Mutation {mutation_id} failed to apply, skipping")
                        mutation_results[mutation_id] = {
                            "killed": False,
                            "verification_status": "skipped",
                            "error": "Mutation failed to apply",
                            "original_code": mutation.get("original_code_slice", "N/A"),
                            "mutation_code": mutation.get("mutation_code_slice", "N/A")
                        }
                        continue
                    
                    # 2. 将当前测试的断言插入到突变后的RTL中
                    mutated_with_sva = insert_sva_into_module_content(
                        mutated_content, "ibex_if_stage", sva_string
                    )
                    
                    if not mutated_with_sva:
                        logging.warning(f"Failed to insert SVA into mutated RTL for {mutation_id}")
                        mutation_results[mutation_id] = {
                            "killed": False,
                            "verification_status": "skipped", 
                            "error": "Failed to insert SVA into mutated RTL",
                            "original_code": mutation.get("original_code_slice", "N/A"),
                            "mutation_code": mutation.get("mutation_code_slice", "N/A")
                        }
                        continue
                    
                    # 3. 创建突变后的RTL文件（包含断言）
                    mutant_rtl_dir = mutation_output_dir / "mutant_rtl" / sva_id
                    mutant_rtl_dir.mkdir(parents=True, exist_ok=True)
                    mutant_rtl_file = mutant_rtl_dir / f"{mutation_id}.sv"
                    
                    with open(mutant_rtl_file, 'w', encoding='utf-8') as f:
                        f.write(mutated_with_sva)
                    
                    # 4. 创建文件列表（使用突变后的RTL）
                    file_list_dir = mutation_output_dir / "mutant_filelists" / sva_id
                    file_list_dir.mkdir(parents=True, exist_ok=True)
                    file_list_path = file_list_dir / f"{mutation_id}.f"
                    
                    with open(file_list_path, 'w', encoding='utf-8') as f:
                        for file_path in ibex_files:
                            if file_path.name == "ibex_if_stage.sv":
                                f.write(f"{mutant_rtl_file}\n")  # 使用突变后的文件
                            else:
                                f.write(f"{file_path}\n")
                    
                    # 5. 生成TCL脚本
                    tcl_dir = mutation_output_dir / "mutant_tcl" / sva_id
                    tcl_dir.mkdir(parents=True, exist_ok=True)
                    tcl_path = tcl_dir / f"{mutation_id}.tcl"
                    
                    if generate_fpv_tcl(
                        tcl_path,
                        prim_assert_dir,
                        dv_utils_dir,
                        rtl_dir,
                        file_list_path,
                        top_module="ibex_if_stage",
                        clock_signal="clk_i",
                        reset_signal="~rst_ni"
                    ):
                        # 6. 运行JasperGold验证
                        jg_dir = mutation_output_dir / "mutant_jg" / sva_id / mutation_id
                        rpt_dir = mutation_output_dir / "mutant_reports" / sva_id
                        rpt_dir.mkdir(parents=True, exist_ok=True)
                        
                        rpt_path = run_jg_single(tcl_path, jg_dir, rpt_dir)
                        
                        # 7. 分析结果
                        report_content = rpt_path.read_text(encoding='utf-8')
                        status = extract_proof_status(report_content)
                        
                        # 如果断言在突变体上失败（返回cex），说明突变被杀死
                        killed = (status != "proven")
                        if killed:
                            killed_mutations += 1
                        
                        mutation_results[mutation_id] = {
                            "killed": killed,
                            "verification_status": status,
                            "original_code": mutation.get("original_code_slice", "N/A"),
                            "mutation_code": mutation.get("mutation_code_slice", "N/A"),
                            "mutant_file": str(mutant_file),
                            "mutation_index": i
                        }
                        
                        logging.info(f"  {sva_id} - Mutation {mutation_id}: {'KILLED' if killed else 'SURVIVED'} ({status})")
                        
                    else:
                        mutation_results[mutation_id] = {
                            "killed": False,
                            "verification_status": "error",
                            "error": "Failed to generate TCL script",
                            "original_code": mutation.get("original_code_slice", "N/A"),
                            "mutation_code": mutation.get("mutation_code_slice", "N/A")
                        }
                        
                except Exception as e:
                    logging.error(f"  Error testing mutation {mutation_id} for {sva_id}: {str(e)}")
                    mutation_results[mutation_id] = {
                        "killed": False,
                        "verification_status": "error",
                        "error": str(e),
                        "original_code": mutation.get("original_code_slice", "N/A"),
                        "mutation_code": mutation.get("mutation_code_slice", "N/A")
                    }
        
        # 计算突变覆盖度
        mutation_score = killed_mutations / total_mutations if total_mutations > 0 else 0
        
        return {
            "sva_id": sva_id,
            "sva_string": sva_string,
            "total_mutations": total_mutations,
            "killed_mutations": killed_mutations,
            "mutation_score": mutation_score,
            "details": mutation_results
        }
        
    except Exception as e:
        logging.error(f"Error in mutation testing for {sva_id}: {str(e)}")
        return {
            "sva_id": sva_id,
            "sva_string": sva_string,
            "error": str(e),
            "total_mutations": 0,
            "killed_mutations": 0,
            "mutation_score": 0,
            "details": {}
        }

def run_mutation_testing_parallel(
    proven_svas: Dict[str, List[Dict]],
    original_rtl_file: Path,
    mutants_dir: Path,
    output_dir: Path,
    ibex_files: List[Path],
    max_workers: int = None
) -> Dict[str, Any]:
    """
    并行运行突变测试。
    """
    mutation_output_dir = output_dir / "mutation_testing"
    if mutation_output_dir.exists():
        shutil.rmtree(mutation_output_dir)
    mutation_output_dir.mkdir(parents=True, exist_ok=True)
    
    # 获取必要的目录路径
    prim_assert_dir = original_rtl_file.parent.parent / "vendor/lowrisc_ip/ip/prim/rtl"
    dv_utils_dir = original_rtl_file.parent.parent / "vendor/lowrisc_ip/dv/sv/dv_utils"
    rtl_dir = original_rtl_file.parent

    # # ========== 添加测试限制代码 ==========
    # # 只取前3个变量，每个变量只取前1条断言进行测试
    # test_svas = {}
    # test_count = 0
    # max_per_variable = 3
    # max_variables = 5
    
    # for i, (variable_name, assertions) in enumerate(proven_svas.items()):
    #     if i >= max_variables:
    #         break
    #     test_svas[variable_name] = assertions[:max_per_variable]
    #     test_count += len(assertions[:max_per_variable])
    
    # proven_svas = test_svas
    # logging.info(f"TEST MODE: Using {test_count} proven assertions for mutation testing")
    # # ========== 添加结束 ==========

    # 收集所有要测试的断言
    test_cases = []
    for variable_name, assertions in proven_svas.items():
        for assertion in assertions:
            if assertion.get("status") == "proven":
                test_cases.append(assertion)
    
    logging.info(f"Starting mutation testing for {len(test_cases)} proven assertions...")
    
    if max_workers is None:
        max_workers = min(max(1, int(multiprocessing.cpu_count() * 0.5)), 8)
    
    # 准备参数列表
    args_list = []
    for assertion in test_cases:
        args_list.append((
            assertion, original_rtl_file, mutants_dir, mutation_output_dir,
            ibex_files, prim_assert_dir, dv_utils_dir, rtl_dir
        ))
    
    all_results = {}
    
    # 并行执行
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        # 提交所有任务
        future_to_sva = {
            executor.submit(run_mutation_test_for_single_assertion, args): args[0]["sva_id"]
            for args in args_list
        }
        
        # 使用tqdm显示进度
        with tqdm(total=len(args_list), desc="Mutation Testing") as pbar:
            for future in as_completed(future_to_sva):
                sva_id = future_to_sva[future]
                try:
                    result = future.result()
                    all_results[sva_id] = result
                    pbar.update(1)
                    pbar.set_postfix_str(f"{len(all_results)}/{len(args_list)}")
                    
                except Exception as e:
                    logging.error(f"Exception in mutation testing for {sva_id}: {str(e)}")
                    all_results[sva_id] = {
                        "sva_id": sva_id,
                        "error": str(e),
                        "total_mutations": 0,
                        "killed_mutations": 0,
                        "mutation_score": 0,
                        "details": {}
                    }
                    pbar.update(1)
    
    # 计算总体统计
    total_mutations = sum(result.get("total_mutations", 0) for result in all_results.values())
    total_killed = sum(result.get("killed_mutations", 0) for result in all_results.values())
    overall_score = total_killed / total_mutations if total_mutations > 0 else 0
    
    # 保存总体结果
    overall_result = {
        "total_assertions": len(all_results),
        "total_mutations_tested": total_mutations,
        "total_killed_mutations": total_killed,
        "overall_mutation_score": overall_score,
        "mutation_testing_results": all_results
    }
    
    result_file = mutation_output_dir / "mutation_testing_results.json"
    with open(result_file, 'w', encoding='utf-8') as f:
        json.dump(overall_result, f, indent=2, ensure_ascii=False)
    
    logging.info(f"Mutation testing completed. Overall score: {overall_score:.2%}")
    logging.info(f"Results saved to: {result_file}")
    
    return overall_result

# ============================ 修改main函数 ============================

def main():
    """
    主函数。
    """
    parser = argparse.ArgumentParser(description="Run Ibex if_stage verification and mutation testing")
    parser.add_argument("--design", default="ibex_if_stage", help="Design name")
    parser.add_argument("--ibex-dir", default=Path("/data/fhj/sva-var/ibex/rtl"), type=Path, help="Path to Ibex RTL directory")
    parser.add_argument("--sva-dir", default=Path("/data/fhj/sva-var/verify/ibex_if_stage/data/assertions"), type=Path, help="Path to SVA JSON files directory")
    parser.add_argument("--output-dir", default=Path("/data/fhj/sva-var/verify/ibex_if_stage/output"), type=Path, help="Output directory")
    parser.add_argument("--mutants-dir", default=Path("/data/fhj/sva-var/verify/ibex_if_stage/data/mutants"), type=Path, help="Path to mutants directory")
    parser.add_argument("--workers", type=int, default=20, help="Number of parallel workers for verification")
    parser.add_argument("--mutation-workers", type=int, default=10, help="Number of parallel workers for mutation testing")
    parser.add_argument("--mut", action="store_true", help="Run mutation testing after verification")
    
    args = parser.parse_args()
    
    # 设置日志
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_dir = args.output_dir / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(log_dir / f"ibex_verif_{timestamp}.log"),
            logging.StreamHandler(sys.stdout)
        ]
    )
    
    logging.info(f"Starting parallel verification with {args.workers} workers")
    
    # 1. 运行主要验证
    # result = run_ibex_verification(
    #     design_name=args.design,
    #     ibex_rtl_dir=args.ibex_dir,
    #     sva_dir=args.sva_dir,
    #     output_dir=args.output_dir,
    #     max_workers=args.workers
    # )
    
    # # 保存验证结果
    # result_file = args.output_dir / "verification_result.json"
    # with open(result_file, 'w', encoding='utf-8') as f:
    #     json.dump(result, f, indent=2, ensure_ascii=False)
    
    # logging.info(f"Verification result saved to: {result_file}")
    
    # 2. 如果启用突变测试

    if args.mut:
        logging.info("\n" + "="*60)
        logging.info("Starting Mutation Testing")
        logging.info("="*60)
        
        # 从保存的验证结果文件中读取已证明的断言
        verification_result_file = args.output_dir / "verification_result.json"
        
        if not verification_result_file.exists():
            logging.error(f"Verification result file not found: {verification_result_file}")
            logging.info("Please run verification first without --run-mutation-test flag")
        else:
            try:
                with open(verification_result_file, 'r', encoding='utf-8') as f:
                    verification_result = json.load(f)
                
                # 检查验证任务状态
                task_status = verification_result.get("task_status")
                if task_status not in ["passed", "partial_pass"] and False:
                    logging.info(f"Verification task status is '{task_status}', skipping mutation testing")
                else:
                    # 获取已证明的断言 - 修正数据结构处理
                    proven_svas = {}
                    sva_details = verification_result.get("sva_details", {})
                    
                    for module_name, variables_dict in sva_details.items():
                        proven_assertions = []
                        
                        # variables_dict 是 {variable_name: [assertions_list]}
                        for variable_name, assertions_list in variables_dict.items():
                            if isinstance(assertions_list, list):
                                proven_for_variable = [
                                    assertion for assertion in assertions_list 
                                    if isinstance(assertion, dict) and assertion.get("status") == "proven"
                                ]
                                proven_assertions.extend(proven_for_variable)
                                if proven_for_variable:
                                    logging.info(f"  Variable {variable_name}: {len(proven_for_variable)} proven assertions")
                        
                        if proven_assertions:
                            proven_svas[module_name] = proven_assertions
                            logging.info(f"Module {module_name}: {len(proven_assertions)} proven assertions")
                    
                    total_proven = sum(len(v) for v in proven_svas.values())
                    logging.info(f"Total proven assertions found: {total_proven}")
                    
                    if proven_svas:
                        # 重新创建文件列表（用于突变测试）
                        ibex_files = create_ibex_file_list(args.ibex_dir)
                        
                        # 运行突变测试
                        mutation_result = run_mutation_testing_parallel(
                            proven_svas=proven_svas,
                            original_rtl_file=args.ibex_dir / "ibex_if_stage.sv",
                            mutants_dir=args.mutants_dir,
                            output_dir=args.output_dir,
                            ibex_files=ibex_files,
                            max_workers=args.mutation_workers
                        )
                        
                        logging.info(f"Mutation testing completed. Overall score: {mutation_result['overall_mutation_score']:.2%}")
                    else:
                        logging.info("No proven assertions found for mutation testing.")
                        
            except Exception as e:
                logging.error(f"Error loading verification results: {e}")
                import traceback
                logging.error(traceback.format_exc())
    
    logging.info("All tasks completed!")

if __name__ == "__main__":
    main()

