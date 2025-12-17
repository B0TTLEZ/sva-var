import json
import argparse
import math
from pathlib import Path

def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description='Generate top-k percentage assertion files from the assertion scores JSON.')
    parser.add_argument('input_path', help='Path to the assertion scores JSON file (e.g., /data/assertion_scores.json)')
    args = parser.parse_args()

    # 处理输入路径，确保文件存在
    input_file = Path(args.input_path).resolve()
    if not input_file.exists():
        print(f"Error: Input file '{input_file}' does not exist!")
        return

    # 创建top_k子目录（在输入文件的同级目录）
    top_k_dir = input_file.parent / "top_k"
    top_k_dir.mkdir(exist_ok=True)  # 目录已存在则不报错

    # 读取断言分数JSON数据
    with open(input_file, 'r', encoding='utf-8') as f:
        assertion_data = json.load(f)

    # 定义需要生成的百分比列表
    percentages = [25, 50, 75, 100]

    # 遍历每个百分比，生成对应的top_k文件
    for p in percentages:
        top_percent_data = {}
        # 处理每个模块的断言
        for module_name, assertions in assertion_data.items():
            if not assertions:  # 模块无断言，保留空列表
                top_percent_data[module_name] = []
                continue

            # 按Rank升序排序（确保断言按排名顺序排列，鲁棒性处理）
            sorted_assertions = sorted(assertions, key=lambda x: x['Rank'])
            total_count = len(sorted_assertions)

            # 计算需要提取的断言数量（向上取整，避免0个的情况）
            take_count = math.ceil(total_count * p / 100)
            # 确保数量不超过总断言数（100%时取全部）
            take_count = min(take_count, total_count)

            # 提取前take_count个断言
            top_assertions = sorted_assertions[:take_count]
            top_percent_data[module_name] = top_assertions

        # 保存到对应的JSON文件
        output_file = top_k_dir / f"top_{p}.json"
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(top_percent_data, f, indent=2, ensure_ascii=False)

        print(f"Successfully generated: {output_file}")

if __name__ == "__main__":
    main()