import argparse
import json
import logging
from pathlib import Path
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple, Optional, Set

# ============================ 全局配置 ============================
plt.rcParams["axes.unicode_minus"] = False

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler()]
)

# ============================ 功能1：搜索超时的变异体和Rank ============================
def search_timeout_cases(result_root: Path) -> List[Dict[str, str]]:
    """
    搜索所有超时的（变异体+Rank）对
    :param result_root: mutants_IRank_single根目录
    :return: 超时案例列表，每个元素包含mutant_id、rank、error_msg
    """
    timeout_cases = []
    timeout_flag = "ERROR: Timeout after "  # 匹配包含该子串的错误信息

    # 遍历所有变异体目录（数字命名）
    mutant_dirs = [d for d in result_root.iterdir() if d.is_dir() and d.name.isdigit()]
    if not mutant_dirs:
        logging.warning(f"未找到变异体目录: {result_root}")
        return timeout_cases

    logging.info(f"开始搜索超时案例，共扫描 {len(mutant_dirs)} 个变异体目录...")
    for mutant_dir in mutant_dirs:
        mutant_id = mutant_dir.name
        # 遍历该变异体下的所有Rank目录
        rank_dirs = [d for d in mutant_dir.iterdir() if d.is_dir() and d.name.startswith("Rank_")]
        for rank_dir in rank_dirs:
            rank = rank_dir.name.replace("Rank_", "")
            result_json = rank_dir / "result.json"
            if not result_json.exists():
                logging.debug(f"跳过不存在的result.json: {result_json}")
                continue

            # 读取result.json
            try:
                with open(result_json, "r", encoding="utf-8") as f:
                    data = json.load(f)
                # 检查是否超时：遍历错误信息，判断是否包含超时子串
                error_msgs = data.get("proof_status", {}).get("error_messages", [])
                is_timeout = False
                matched_msg = ""
                for msg in error_msgs:
                    if timeout_flag in msg:  # 核心修正：检查子串包含
                        is_timeout = True
                        matched_msg = msg
                        break
                if is_timeout:
                    timeout_cases.append({
                        "mutant_id": mutant_id,
                        "rank": rank,
                        "error_msg": matched_msg  # 保存完整的超时信息
                    })
                    logging.info(f"发现超时: 变异体{mutant_id} - Rank{rank}: {matched_msg}")
            except Exception as e:
                logging.error(f"读取 {result_json} 失败: {e}")
                continue

    # 输出汇总
    if timeout_cases:
        logging.info(f"\n=== 超时案例汇总（共 {len(timeout_cases)} 个）===")
        for case in timeout_cases:
            logging.info(f"变异体{case['mutant_id']} - Rank{case['rank']}: {case['error_msg']}")
    else:
        logging.info("\n未发现任何超时案例")
    return timeout_cases

# ============================ 功能2：计算累计杀死的唯一变异体数 + 新增：每个Rank原始杀死数 ============================
def calculate_cumulative_killed(result_root: Path) -> Tuple[List[int], List[int], List[int]]:
    """
    从汇总文件计算：
    1. 每个Rank的累计杀死**唯一**变异体数（去重）
    2. 每个Rank直接杀死的变异体数（不去重）
    适配JSON结构：killed_mutants字段为变异体ID列表
    :param result_root: mutants_IRank_single根目录
    :return: (rank_list, cumulative_unique_killed, per_rank_killed) 
             - Rank列表、累计唯一杀死数、每个Rank原始杀死数（不去重）
    """
    summary_file = result_root / "assertion_kill_summary.json"
    if not summary_file.exists():
        raise FileNotFoundError(f"汇总文件不存在: {summary_file}")

    # 读取汇总文件
    with open(summary_file, "r", encoding="utf-8") as f:
        summary_data = json.load(f)

    # 提取每个Rank对应的【杀死的变异体ID列表】
    rank_killed_mutants: Dict[int, List[str]] = {}
    for item in summary_data["assertion_rank_summary"]:
        rank = item["rank"]  # JSON中rank是数字类型
        killed_mutant_ids = item["killed_mutants"]  # 匹配实际字段名
        rank_killed_mutants[rank] = killed_mutant_ids

    # 按Rank升序排列
    sorted_ranks = sorted(rank_killed_mutants.keys())
    rank_list = sorted_ranks  # Rank列表（整数类型）
    
    # 维护全局唯一变异体ID集合（自动去重）
    unique_killed_mutants: Set[str] = set()
    cumulative_unique_killed = []
    # 新增：存储每个Rank的原始杀死数（不去重）
    per_rank_killed = []
    
    # 逐Rank计算
    for rank in sorted_ranks:
        current_killed_ids = rank_killed_mutants[rank]
        # 新增：记录当前Rank原始杀死数（不去重）
        current_killed_count = len(current_killed_ids)
        per_rank_killed.append(current_killed_count)
        
        # 原有逻辑：累计唯一数计算
        prev_count = len(unique_killed_mutants)
        unique_killed_mutants.update(current_killed_ids)
        current_count = len(unique_killed_mutants)
        new_killed = current_count - prev_count  # 本次新增的唯一变异体数
        
        # 记录累计数
        cumulative_unique_killed.append(current_count)
        
        # 日志输出（补充原始杀死数）
        logging.info(f"Rank {rank}: 原始杀死{current_killed_count}个（重复{current_killed_count-new_killed}个），新增{new_killed}个唯一变异体，累计{current_count}个")

    # 最终汇总日志
    logging.info(f"\n=== 累计唯一杀死数计算完成 ===")
    logging.info(f"Rank范围: {rank_list[0]} ~ {rank_list[-1]}")
    logging.info(f"总杀死唯一变异体数: {cumulative_unique_killed[-1]}")
    logging.info(f"各Rank原始杀死数汇总: {dict(zip(rank_list, per_rank_killed))}")
    return rank_list, cumulative_unique_killed, per_rank_killed  # 新增返回per_rank_killed

# ============================ 功能3：可视化折线图（优化X轴刻度重叠 + 新增原始杀死数散点） ============================
def get_last_non_zero_final_score_rank(score_file: Path, top_module: str) -> Optional[int]:
    """
    找到最后一个final_score不为0的Rank
    :param score_file: assertion_scores.json路径
    :param top_module: 顶层模块名（如uart2bus_top）
    :return: 最后一个非零Rank，无则返回None
    """
    if not score_file.exists():
        raise FileNotFoundError(f"断言分数文件不存在: {score_file}")

    with open(score_file, "r", encoding="utf-8") as f:
        score_data = json.load(f)

    # 提取顶层模块的断言
    if top_module not in score_data:
        logging.warning(f"分数文件中未找到模块 {top_module}")
        return None

    # 筛选final_score≠0的断言，按Rank升序排序
    valid_assertions = [
        a for a in score_data[top_module]
        if a.get("final_score", 0) != 0
    ]
    if not valid_assertions:
        logging.warning("未找到final_score非零的断言")
        return None

    # 按Rank升序排序，取最后一个
    valid_assertions_sorted = sorted(valid_assertions, key=lambda x: x["Rank"])
    last_rank = valid_assertions_sorted[-1]["Rank"]
    logging.info(f"最后一个final_score非零的Rank: {last_rank}")
    return last_rank

def plot_cumulative_killed(
    rank_list: List[int],
    cumulative_killed: List[int],
    per_rank_killed: List[int],  # 新增参数：每个Rank原始杀死数
    output_img: Path,
    last_non_zero_rank: Optional[int] = None
):
    """
    绘制可视化图：
    1. 原有：累计唯一杀死变异体数折线
    2. 新增：每个Rank原始杀死变异体数散点（无连线，弱化样式）
    :param rank_list: Rank列表
    :param cumulative_killed: 累计唯一杀死数列表
    :param per_rank_killed: 每个Rank原始杀死数列表（新增）
    :param output_img: 图片输出路径
    :param last_non_zero_rank: 最后一个final_score非零的Rank（可选）
    """
    # 创建画布
    fig, ax = plt.subplots(figsize=(12, 6))

    # 原有：绘制累计唯一杀死数折线（保持原有样式，优先显示）
    ax.plot(rank_list, cumulative_killed, marker="o", color="#2E86AB", linewidth=2, markersize=4, 
            label="Cumulative Unique Killed Mutants", zorder=2)  # zorder提高层级，确保在顶层
    
    # 新增：绘制每个Rank原始杀死数（仅散点，无连线，弱化样式）
    ax.scatter(rank_list, per_rank_killed, marker="s", color="#F77F00", s=20, alpha=0.7,
               label="Per Rank Killed Mutants (No Deduplication)", zorder=1)  # zorder降低层级，不遮盖原有折线
    
    # X轴标签
    ax.set_xlabel("Assertion Rank", fontsize=12)
    # Y轴标签（适配两个维度）
    ax.set_ylabel("Number of Killed Mutants", fontsize=12)
    # 标题（更新）
    ax.set_title("Assertion Rank vs Killed Mutants", fontsize=14, fontweight="bold")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=10)

    # ========== 优化Y轴：动态调整刻度间隔，解决密集问题 ==========
    # 适配两个折线的最大值
    y_max = max(max(cumulative_killed), max(per_rank_killed)) if (cumulative_killed and per_rank_killed) else 0
    # 分档设置Y轴刻度间隔（根据最大值动态调整）
    if y_max <= 20:
        y_tick_interval = 1  # 小数值：每1个显示一个
    elif 20 < y_max <= 100:
        y_tick_interval = 5  # 中数值：每5个显示一个
    elif 100 < y_max <= 200:
        y_tick_interval = 10 # 较大数值：每10个显示一个
    elif 200 < y_max <= 1000:
        y_tick_interval = 20 # 大数值：每20个显示一个
    else:
        y_tick_interval = 100# 超大数值：每100个显示一个
    
    # 生成间隔后的Y轴刻度（确保从0开始，到y_max结束）
    y_ticks = list(range(0, y_max + 1, y_tick_interval))
    # 兜底：如果最大值不在刻度列表中，补充上（避免刻度不到最大值）
    if y_max not in y_ticks:
        y_ticks.append(y_max)
    ax.set_yticks(y_ticks)
    ax.set_ylim(bottom=0)   # 确保Y轴从0开始

    # ========== 核心优化：解决X轴刻度密集重叠 ==========
    x_min = min(rank_list)
    x_max = max(rank_list)
    total_ranks = x_max - x_min + 1

    # 1. 动态计算X轴刻度间隔（根据Rank总数自动调整）
    if total_ranks <= 20:
        tick_interval = 2  # 少于20个Rank，每2个显示一个
    elif total_ranks <= 50:
        tick_interval = 5  # 20-50个Rank，每5个显示一个
    elif total_ranks <= 100:
        tick_interval = 10 # 50-100个Rank，每10个显示一个
    else:
        tick_interval = 20 # 超过100个Rank，每20个显示一个

    # 生成间隔后的X轴刻度
    x_ticks = list(range(x_min, x_max + 1, tick_interval))
    # 确保最后一个Rank一定显示
    if x_max not in x_ticks:
        x_ticks.append(x_max)
    ax.set_xticks(x_ticks)

    # 2. 旋转X轴刻度标签（关键：避免横向重叠）
    ax.tick_params(axis='x', rotation=45, labelsize=10)  # 旋转45度，缩小字体

    # 3. 调整画布边距（防止旋转后的标签被截断）
    plt.subplots_adjust(bottom=0.15)

    # 添加final_score非零Rank竖线
    if last_non_zero_rank is not None and last_non_zero_rank in rank_list:
        ax.axvline(x=last_non_zero_rank, color="#E63946", linestyle="--", linewidth=2, 
                   label=f"Last Rank with Non-zero final_score: {last_non_zero_rank}", zorder=3)
        ax.legend(fontsize=10)

    # 保存图片
    output_img.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(output_img, dpi=300, bbox_inches="tight")
    logging.info(f"可视化图片已保存: {output_img}")

# ============================ 主函数 ============================
def main():
    parser = argparse.ArgumentParser(description="变异体验证结果分析工具：超时搜索 + 累计唯一杀死数+原始杀死数可视化（去重+整数刻度+防重叠）")
    parser.add_argument("--result-root", required=True, type=Path,
                        help="mutants_IRank_single根目录（如/data/.../uart/mutants_IRank_single）")
    parser.add_argument("--output-img", required=True, type=Path,
                        help="可视化图片输出路径（如./cumulative_killed.png）")
    parser.add_argument("--score-file", type=Path,
                        help="可选：断言分数文件路径（用于画最后非零final_score Rank竖线）")
    parser.add_argument("--top-module", type=str,
                        help="可选：顶层模块名（配合score-file使用，如uart2bus_top）")

    args = parser.parse_args()

    # 步骤1：搜索超时案例
    timeout_cases = search_timeout_cases(args.result_root)
    # 保存超时案例到文件
    timeout_file = args.result_root / "timeout_cases.json"
    with open(timeout_file, "w", encoding="utf-8") as f:
        json.dump(timeout_cases, f, indent=2, ensure_ascii=False)
    logging.info(f"超时案例已保存至: {timeout_file}")

    # 步骤2：计算累计唯一杀死数 + 原始杀死数（修改接收参数）
    try:
        rank_list, cumulative_killed, per_rank_killed = calculate_cumulative_killed(args.result_root)  # 新增per_rank_killed
    except Exception as e:
        logging.error(f"计算杀死数失败: {e}")
        return

    # 步骤3：获取最后非零final_score的Rank（可选）
    last_non_zero_rank = None
    if args.score_file and args.top_module:
        try:
            last_non_zero_rank = get_last_non_zero_final_score_rank(args.score_file, args.top_module)
        except Exception as e:
            logging.error(f"读取分数文件失败: {e}")

    # 步骤4：绘制可视化图（传递新增的per_rank_killed参数）
    plot_cumulative_killed(rank_list, cumulative_killed, per_rank_killed, args.output_img, last_non_zero_rank)  # 新增参数

    logging.info("\n=== 所有任务完成 ===")

if __name__ == "__main__":
    main()