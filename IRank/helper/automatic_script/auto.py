import json
import subprocess
from pathlib import Path
import argparse

def run_command(cmd, module_name, step_name):
    """封装命令执行逻辑，复用代码"""
    print(f"\n-------------------------------------")
    print(f"{module_name} - {step_name}")
    print(f"执行命令：{' '.join(cmd)}")
    print(f"-------------------------------------")
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding='utf-8'
        )
        if result.stdout:
            print(f"✅ {step_name} 输出：\n{result.stdout}")
        if result.stderr:
            print(f"⚠️  {step_name} 警告/错误：\n{result.stderr}")
        if result.returncode == 0:
            print(f"✅ {module_name} - {step_name} 完成")
            return True
        else:
            print(f"❌ {module_name} - {step_name} 失败，返回码：{result.returncode}")
            return False
    except Exception as e:
        print(f"❌ {module_name} - {step_name} 执行异常：{e}")
        return False

def main(json_file_path):
    # 1. 读取JSON文件
    try:
        with open(json_file_path, 'r', encoding='utf-8') as f:
            modules = json.load(f)
    except Exception as e:
        print(f"❌ 读取JSON文件失败：{e}")
        return

    # 2. 遍历每个模块条目
    for idx, module in enumerate(modules):
        module_name = module.get("name", f"模块{idx+1}")
        chains_input_path = module.get("outputPath")  # JSON中的outputPath作为generate_chains的输入路径
        if not chains_input_path:
            print(f"⚠️ {module_name} 未找到outputPath，跳过")
            continue

        # 3. 处理路径：获取统一的工作目录（所有文件都在这个目录下）
        input_path_obj = Path(chains_input_path)
        work_dir = input_path_obj.parent  # 核心工作目录（所有文件的父目录）
        # --- generate_chains.py 的路径配置 ---
        var_define_chain_path = work_dir / "var_define_chain.json"
        var_use_chain_path = work_dir / "var_use_chain.json"
        # --- generate_pagerank.py 的路径配置 ---
        pagerank_input_path = var_define_chain_path  # 输入是var_define_chain.json
        weight_map_path = work_dir / "weight_map.json"
        complete_pagerank_path = work_dir / "complete_PageRank.json"

        print(f"\n=====================================")
        print(f"开始处理模块：{module_name}")
        print(f"工作目录：{work_dir}")
        print(f"=====================================")

        # 4. 执行第一步：generate_chains.py
        chains_cmd = [
            "python",
            "/data/sva-var/IRank/VDG_builder/generate_chains.py",
            str(input_path_obj),
            str(var_define_chain_path),
            str(var_use_chain_path)
        ]
        chains_success = run_command(chains_cmd, module_name, "生成var_define_chain和var_use_chain")

        # 5. 执行第二步：generate_pagerank.py（仅当第一步成功时执行）
        if chains_success:
            pagerank_cmd = [
                "python",
                "/data/sva-var/IRank/weight_And_PageRank/generate_pagerank.py",
                str(pagerank_input_path),
                str(weight_map_path),
                str(complete_pagerank_path)
            ]
            run_command(pagerank_cmd, module_name, "生成weight_map和complete_PageRank")

    print(f"\n🎉 所有模块处理流程结束！")

if __name__ == "__main__":
    # 命令行参数解析：让用户传入JSON文件路径
    parser = argparse.ArgumentParser(description="批量执行generate_chains.py和generate_pagerank.py脚本")
    parser.add_argument("json_file", help="模块配置的JSON文件路径")
    args = parser.parse_args()
    main(args.json_file)