import argparse
import json
import os
from pathlib import Path
import pandas as pd
import matplotlib.pyplot as plt
from typing import List, Dict, Any

# ============================ 配置项 ============================
# 移除中文字体配置，使用Matplotlib默认字体（避免字体查找警告）
plt.rcParams["axes.unicode_minus"] = False  # 仅保留解决负号显示问题

# ============================ 核心函数 ============================
def load_summary_data(result_root: Path) -> List[Dict[str, Any]]:
    """
    遍历结果根目录，读取所有top_k的summary.json文件，提取关键数据
    :param result_root: 结果根目录（如mutants_IRank）
    :return: 整理后的数据集
    """
    summary_data = []
    # 遍历所有top_k子目录（如top_25、top_50、top_100）
    for top_k_dir in result_root.iterdir():
        if not top_k_dir.is_dir() or not top_k_dir.name.startswith("top_"):
            continue
        # 读取summary.json
        summary_file = top_k_dir / "summary.json"
        if not summary_file.exists():
            print(f"Warning: summary.json not found in {top_k_dir.name}, skipped")
            continue
        try:
            with open(summary_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            # 提取关键字段
            top_k_name = data.get("top_k", top_k_dir.name)
            # 解析k值（如top_100 -> 100）
            k = int(top_k_name.replace("top_", "")) if "top_" in top_k_name else 0
            # 核心统计数据
            entry = {
                "top_k": top_k_name,
                "k_value": k,
                "total_mutants": data.get("total_mutants", 0),
                "processed_mutants": data.get("processed_mutants", 0),
                "killed_count": data.get("killed_count", 0),
                "survived_count": data.get("survived_count", 0),
                "failed_count": data.get("failed_count", 0),
                "killed_rate": (data.get("killed_count", 0) / data.get("total_mutants", 1)) * 100  # 杀死率（%）
            }
            summary_data.append(entry)
            print(f"Successfully loaded: {top_k_name} - Killed mutants: {entry['killed_count']}")
        except Exception as e:
            print(f"Error: Failed to read {summary_file} - {str(e)}")
            continue
    # 按k值排序（25 -> 50 -> 100）
    summary_data.sort(key=lambda x: x["k_value"])
    return summary_data

def generate_table(data: List[Dict[str, Any]], output_dir: Path) -> pd.DataFrame:
    """
    生成统计表格并保存为CSV文件
    :param data: 汇总数据
    :param output_dir: 输出目录
    :return: pandas DataFrame
    """
    df = pd.DataFrame(data)
    # 格式化数据（杀死率保留2位小数）
    df["killed_rate"] = df["killed_rate"].round(2)
    # 调整列顺序
    df = df[["top_k", "k_value", "total_mutants", "processed_mutants", 
             "killed_count", "survived_count", "failed_count", "killed_rate"]]
    # 保存为CSV
    table_file = output_dir / "mutants_killed_statistics.csv"
    df.to_csv(table_file, index=False, encoding="utf-8-sig")
    print(f"\nStatistics table saved to: {table_file}")
    # 打印表格
    print("\n=== Mutants Killed Statistics Table ===")
    print(df.to_string(index=False))
    return df

def generate_visualization(df: pd.DataFrame, output_dir: Path):
    """
    生成可视化图片（柱状图+折线图）
    :param df: 统计数据DataFrame
    :param output_dir: 输出目录
    """
    if df.empty:
        print("Error: No data to visualize")
        return
    # 创建画布（1行2列，分别显示杀死数和杀死率）
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))
    fig.suptitle("Mutants Killed Statistics Visualization", fontsize=16, fontweight="bold")

    # 1. 左图：柱状图（杀死数、存活数、失败数）
    x = df["top_k"]
    width = 0.25  # 柱子宽度
    ax1.bar([i - width for i in range(len(x))], df["killed_count"], width, 
            label="Killed Count", color="#e74c3c", alpha=0.8)
    ax1.bar(range(len(x)), df["survived_count"], width, 
            label="Survived Count", color="#2ecc71", alpha=0.8)
    ax1.bar([i + width for i in range(len(x))], df["failed_count"], width, 
            label="Failed Count", color="#f39c12", alpha=0.8)
    # 设置标签
    ax1.set_xlabel("top_k (Top k% Assertions)", fontsize=12)
    ax1.set_ylabel("Number of Mutants", fontsize=12)
    ax1.set_title("Mutants Distribution by top_k", fontsize=14)
    ax1.set_xticks(range(len(x)))
    ax1.set_xticklabels(x)
    ax1.legend()
    ax1.grid(axis="y", linestyle="--", alpha=0.5)

    # 2. 右图：折线图（杀死率）
    ax2.plot(df["top_k"], df["killed_rate"], marker="o", linewidth=2, 
             markersize=8, color="#3498db", label="Killed Rate (%)")
    # 标注杀死率数值
    for i, rate in enumerate(df["killed_rate"]):
        ax2.text(i, rate + 1, f"{rate}%", ha="center", va="bottom", fontsize=10)
    # 设置标签
    ax2.set_xlabel("top_k (Top k% Assertions)", fontsize=12)
    ax2.set_ylabel("Killed Rate (%)", fontsize=12)
    ax2.set_title("Mutants Killed Rate by top_k", fontsize=14)
    ax2.set_ylim(0, 100)  # 杀死率范围0-100%
    ax2.legend()
    ax2.grid(linestyle="--", alpha=0.5)

    # 保存图片
    img_file = output_dir / "mutants_killed_visualization.png"
    plt.tight_layout()
    plt.savefig(img_file, dpi=300, bbox_inches="tight")
    print(f"\nVisualization image saved to: {img_file}")
    plt.show()

# ============================ 主函数 ============================
def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description="Mutants Verification Result Visualization: Count killed mutants by top_k assertions")
    parser.add_argument("--result-root", required=True, type=Path,
                        help="Result root directory (path to mutants_IRank directory)")
    args = parser.parse_args()

    # 验证输入路径
    if not args.result_root.exists():
        print(f"Error: Path does not exist - {args.result_root}")
        return

    # 1. 读取summary数据
    print("Start loading summary data...")
    summary_data = load_summary_data(args.result_root)
    if not summary_data:
        print("Error: No summary data loaded")
        return

    # 2. 创建可视化输出目录
    output_dir = args.result_root / "visualization"
    output_dir.mkdir(parents=True, exist_ok=True)

    # 3. 生成统计表格
    df = generate_table(summary_data, output_dir)

    # 4. 生成可视化图片
    generate_visualization(df, output_dir)

    print("\nAll visualization tasks completed!")

if __name__ == "__main__":
    main()