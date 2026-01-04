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

# ============================ 功能2：计算累计杀死的唯一变异体数 ============================
def calculate_cumulative_killed(result_root: Path) -> Tuple[List[int], List[int]]:
    """
    从汇总文件计算每个Rank的累计杀死**唯一**变异体数（去重）
    适配JSON结构：killed_mutants字段为变异体ID列表
    :param result_root: mutants_IRank_single根目录
    :return: (rank_list, cumulative_unique_killed) - Rank列表、对应累计唯一杀死数
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
    
    # 逐Rank计算累计唯一数量
    for rank in sorted_ranks:
        current_killed_ids = rank_killed_mutants[rank]
        prev_count = len(unique_killed_mutants)
        unique_killed_mutants.update(current_killed_ids)
        current_count = len(unique_killed_mutants)
        new_killed = current_count - prev_count  # 本次新增的唯一变异体数
        
        # 记录累计数
        cumulative_unique_killed.append(current_count)
        
        # 日志输出（直观看到去重效果）
        logging.info(f"Rank {rank}: 本次击杀{len(current_killed_ids)}个（重复{len(current_killed_ids)-new_killed}个），新增{new_killed}个唯一变异体，累计{current_count}个")

    # 最终汇总日志
    logging.info(f"\n=== 累计唯一杀死数计算完成 ===")
    logging.info(f"Rank范围: {rank_list[0]} ~ {rank_list[-1]}")
    logging.info(f"总杀死唯一变异体数: {cumulative_unique_killed[-1]}")
    return rank_list, cumulative_unique_killed

# ============================ 功能3：可视化折线图（优化X轴刻度重叠） ============================
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
    output_img: Path,
    last_non_zero_rank: Optional[int] = None
):
    """
    绘制累计杀死**唯一**变异体数折线图（解决X轴刻度密集重叠）
    :param rank_list: Rank列表
    :param cumulative_killed: 累计唯一杀死数列表
    :param output_img: 图片输出路径
    :param last_non_zero_rank: 最后一个final_score非零的Rank（可选）
    """
    # 创建画布
    fig, ax = plt.subplots(figsize=(12, 6))

    # 绘制折线图（标注“唯一”）
    ax.plot(rank_list, cumulative_killed, marker="o", color="#2E86AB", linewidth=2, markersize=4, 
            label="Cumulative Unique Killed Mutants")
    # X轴标签
    ax.set_xlabel("Assertion Rank", fontsize=12)
    # Y轴标签（标注“唯一”）
    ax.set_ylabel("Cumulative Number of Unique Killed Mutants", fontsize=12)
    # 标题（标注“唯一”）
    ax.set_title("Assertion Rank vs Cumulative Unique Killed Mutants", fontsize=14, fontweight="bold")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=10)

    # ========== 强制Y轴为整数刻度 ==========
    y_max = max(cumulative_killed)
    y_ticks = list(range(0, y_max + 1))  # 纯Python生成整数刻度（无需numpy）
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
    else:
        tick_interval = 5 # 超过50个Rank，每10个显示一个

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
                   label=f"Last Rank with Non-zero final_score: {last_non_zero_rank}")
        ax.legend(fontsize=10)

    # 保存图片
    output_img.parent.mkdir(parents=True, exist_ok=True)
    plt.tight_layout()
    plt.savefig(output_img, dpi=300, bbox_inches="tight")
    logging.info(f"可视化图片已保存: {output_img}")

# ============================ 主函数 ============================
def main():
    parser = argparse.ArgumentParser(description="变异体验证结果分析工具：超时搜索 + 累计唯一杀死数可视化（去重+整数刻度+防重叠）")
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

    # 步骤2：计算累计唯一杀死数
    try:
        rank_list, cumulative_killed = calculate_cumulative_killed(args.result_root)
    except Exception as e:
        logging.error(f"计算累计唯一杀死数失败: {e}")
        return

    # 步骤3：获取最后非零final_score的Rank（可选）
    last_non_zero_rank = None
    if args.score_file and args.top_module:
        try:
            last_non_zero_rank = get_last_non_zero_final_score_rank(args.score_file, args.top_module)
        except Exception as e:
            logging.error(f"读取分数文件失败: {e}")

    # 步骤4：绘制可视化图
    plot_cumulative_killed(rank_list, cumulative_killed, args.output_img, last_non_zero_rank)

    logging.info("\n=== 所有任务完成 ===")

if __name__ == "__main__":
    main()