import os
import subprocess
import sys
import time

# ===================== 核心配置（根据实际路径确认，无需修改） =====================
# 1. 根目录：所有mx文件夹的父目录
ASSETSOLVER_ROOT = "/data/my_data/sva-out/deepseek_v3/AssertionBench/assertsolver"
# 2. 各个核心脚本的绝对路径（避免相对路径出错）
GENERATE_CHAINS_PY = "/data/sva-var/IRank/VDG_builder/generate_chains.py"
GENERATE_PAGERANK_PY = "/data/sva-var/IRank/weight_And_PageRank/generate_pagerank.py"
ASSERTION_SCORER_PY = "/data/sva-var/IRank/Ranker/assertion_scorer.py"
# 3. 日志文件路径：脚本当前目录下的 auto_run_irank.log
LOG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "auto_run_irank.log")

# ===================== 工具函数：日志打印（控制台 + 文件） =====================
def log_print(msg):
    """
    同时打印到控制台和日志文件，添加时间戳
    :param msg: 要打印的内容
    """
    # 时间戳格式：YYYY-MM-DD HH:MM:SS
    timestamp = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
    log_msg = f"[{timestamp}] {msg}"
    
    # 打印到控制台
    print(log_msg)
    # 写入日志文件（追加模式）
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(log_msg + "\n")

# ===================== 工具函数：执行shell命令并返回结果（带日志保存） =====================
def run_command(cmd, desc):
    """
    执行shell命令，打印日志（控制台+文件），返回是否执行成功
    :param cmd: 要执行的命令列表（subprocess推荐格式）
    :param desc: 命令描述（用于日志）
    :return: bool，True=成功，False=失败
    """
    log_print(f"\n{'='*50}")
    log_print(f"执行命令：{desc}")
    log_print(f"命令详情：{' '.join(cmd)}")
    log_print(f"{'='*50}")
    
    try:
        # 执行命令，捕获输出和错误
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
            timeout=300  # 超时时间5分钟，可根据实际调整
        )
        
        # 打印并保存输出日志
        if result.stdout:
            log_print(f"标准输出：\n{result.stdout}")
        if result.stderr:
            log_print(f"标准错误：\n{result.stderr}")
        
        # 检查返回码
        if result.returncode == 0:
            log_print(f"✅ {desc} 执行成功")
            return True
        else:
            log_print(f"❌ {desc} 执行失败（返回码：{result.returncode}）")
            return False
    except subprocess.TimeoutExpired:
        log_print(f"❌ {desc} 执行超时（5分钟）")
        return False
    except Exception as e:
        log_print(f"❌ {desc} 执行异常：{str(e)}")
        return False

# ===================== 主逻辑：遍历所有mx文件夹并执行流程 =====================
def main():
    # 初始化日志文件（清空原有内容，或追加：将 'w' 改为 'a' 即可）
    with open(LOG_FILE, "w", encoding="utf-8") as f:
        f.write(f"===== 批量执行脚本启动 - {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())} =====\n\n")
    
    # 1. 检查核心脚本是否存在
    for script_path in [GENERATE_CHAINS_PY, GENERATE_PAGERANK_PY, ASSERTION_SCORER_PY]:
        if not os.path.exists(script_path):
            log_print(f"❌ 核心脚本不存在：{script_path}，请检查路径！")
            sys.exit(1)
    
    # 2. 遍历assertsolver下的所有mx文件夹
    mx_dirs = [d for d in os.listdir(ASSETSOLVER_ROOT) 
               if d.startswith("m") and os.path.isdir(os.path.join(ASSETSOLVER_ROOT, d))]
    
    if not mx_dirs:
        log_print(f"❌ 未找到任何以m开头的文件夹，根目录：{ASSETSOLVER_ROOT}")
        sys.exit(1)
    
    log_print(f"✅ 找到 {len(mx_dirs)} 个mx文件夹：{mx_dirs}")
    
    # 3. 逐个处理mx文件夹
    success_count = 0
    fail_count = 0
    for mx_name in mx_dirs:
        mx_dir = os.path.join(ASSETSOLVER_ROOT, mx_name)
        log_print(f"\n\n{'='*60}")
        log_print(f"开始处理文件夹：{mx_dir}")
        log_print(f"{'='*60}")
        
        # -------------------------- 步骤1：定义各文件路径 --------------------------
        # 基础目录
        tmp_out_dir = os.path.join(mx_dir, "IRank", "tmp_out")
        irank_dir = os.path.join(mx_dir, "IRank")
        
        # 输入文件
        analyzer_results = os.path.join(tmp_out_dir, "analyzer_results.json")
        sva_status = os.path.join(mx_dir, "verif", "sva_status.json")
        
        # 步骤2输出文件（generate_chains.py）
        var_define_chain = os.path.join(tmp_out_dir, "var_define_chain.json")
        var_use_chain = os.path.join(tmp_out_dir, "var_use_chain.json")
        
        # 步骤3输出文件（generate_pagerank.py）
        weight_map = os.path.join(tmp_out_dir, "weight_map.json")
        complete_pagerank = os.path.join(tmp_out_dir, "complete_PageRank.json")
        
        # 步骤4输出文件（assertion_scorer.py）
        assertion_scores = os.path.join(irank_dir, "assertion_scores.json")
        coi_cache = os.path.join(tmp_out_dir, "coi_cache.json")
        
        # -------------------------- 路径校验 --------------------------
        # 检查analyzer_results是否存在（前提）
        if not os.path.exists(analyzer_results):
            log_print(f"❌ {mx_dir}：缺少 analyzer_results.json（路径：{analyzer_results}），跳过")
            fail_count += 1
            continue
        
        # 检查sva_status是否存在（步骤4需要）
        if not os.path.exists(sva_status):
            log_print(f"❌ {mx_dir}：缺少 sva_status.json（路径：{sva_status}），跳过")
            fail_count += 1
            continue
        
        # 确保输出目录存在
        os.makedirs(tmp_out_dir, exist_ok=True)
        os.makedirs(irank_dir, exist_ok=True)
        
        # -------------------------- 步骤2：执行generate_chains.py --------------------------
        cmd_chains = [
            "python3",  # 优先用python3，避免python2兼容问题
            GENERATE_CHAINS_PY,
            analyzer_results,
            var_define_chain,
            var_use_chain
        ]
        if not run_command(cmd_chains, f"{mx_name} - 生成var define/use chain"):
            fail_count += 1
            continue
        
        # 检查生成的文件是否存在
        if not (os.path.exists(var_define_chain) and os.path.exists(var_use_chain)):
            log_print(f"❌ {mx_name}：generate_chains.py 未生成目标文件，跳过后续步骤")
            fail_count += 1
            continue
        
        # -------------------------- 步骤3：执行generate_pagerank.py --------------------------
        cmd_pagerank = [
            "python3",
            GENERATE_PAGERANK_PY,
            var_define_chain,  # 输入：var_define_chain.json
            weight_map,        # 输出1：weight_map.json
            complete_pagerank  # 输出2：complete_PageRank.json
        ]
        if not run_command(cmd_pagerank, f"{mx_name} - 生成weight map和PageRank"):
            fail_count += 1
            continue
        
        # 检查生成的文件是否存在
        if not (os.path.exists(weight_map) and os.path.exists(complete_pagerank)):
            log_print(f"❌ {mx_name}：generate_pagerank.py 未生成目标文件，跳过后续步骤")
            fail_count += 1
            continue
        
        # -------------------------- 步骤4：执行assertion_scorer.py --------------------------
        cmd_scorer = [
            "python3",
            ASSERTION_SCORER_PY,
            sva_status,               # 输入1：sva_status.json
            var_define_chain,         # 输入2：var_define_chain.json
            var_use_chain,            # 输入3：var_use_chain.json
            complete_pagerank,        # 输入4：complete_PageRank.json
            weight_map,               # 输入5：weight_map.json
            assertion_scores,         # 输出1：assertion_scores.json
            "--coi-cache", coi_cache  # 选项+输出2：coi_cache.json
        ]
        if not run_command(cmd_scorer, f"{mx_name} - 生成Assertion Ranking和COI"):
            fail_count += 1
            continue
        
        # -------------------------- 单个mx处理完成 --------------------------
        log_print(f"\n🎉 {mx_name} 所有步骤执行完成！")
        success_count += 1
    
    # ===================== 最终统计 =====================
    log_print(f"\n\n{'='*60}")
    log_print(f"批量处理完成！")
    log_print(f"✅ 成功处理：{success_count} 个mx文件夹")
    log_print(f"❌ 失败/跳过：{fail_count} 个mx文件夹")
    log_print(f"{'='*60}")
    
    # 追加结束日志
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(f"\n===== 批量执行脚本结束 - {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())} =====\n")
    
    # 退出码：0=全部成功，1=有失败
    sys.exit(0 if fail_count == 0 else 1)

if __name__ == "__main__":
    main()