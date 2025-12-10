import os
import json

# ===================== 核心配置（可根据实际情况调整） =====================
# 根目录：assertsolver 所在路径
ROOT_DIR = "/data/my_data/sva-out/deepseek_v3/AssertionBench/assertsolver"
# 最终生成的 tests.json 路径（默认生成在根目录下，可自定义）
OUTPUT_JSON_PATH = "./tests_small.json"
# 关键文件名：需要提取的 combined 文件
COMBINED_FILE_NAME = "_combined_rtl_no_comments.sv"

def main():
    # 初始化 tests 列表（最终要写入 JSON 的内容）
    tests = []

    # 遍历根目录下的所有子目录（筛选 m1、m2、m30 等 mx 文件夹）
    for dir_name in os.listdir(ROOT_DIR):
        mx_dir = os.path.join(ROOT_DIR, dir_name)
        # 过滤：仅处理以 m 开头的目录（如 m30），且是真实目录
        if not os.path.isdir(mx_dir) or not dir_name.startswith("m"):
            print(f"跳过非 mx 目录：{mx_dir}")
            continue

        # 1. 检查 rtl 目录是否存在
        rtl_dir = os.path.join(mx_dir, "rtl")
        if not os.path.exists(rtl_dir):
            print(f"跳过 {mx_dir}：未找到 rtl 目录")
            continue

        # 2. 提取 _combined_rtl_no_comments.sv 的完整路径
        combined_sv_path = os.path.join(rtl_dir, COMBINED_FILE_NAME)
        if not os.path.exists(combined_sv_path):
            print(f"跳过 {mx_dir}：未找到 {COMBINED_FILE_NAME}")
            continue

        # 3. 提取模块名（如 Round_Sgf_Dec，来自非 _combined 开头的 .sv 文件）
        module_name = None
        for file_name in os.listdir(rtl_dir):
            # 筛选：.sv 后缀 + 不是 _combined 开头的文件
            if file_name.endswith(".sv") and not file_name.startswith("_combined"):
                # 去掉 .sv 后缀，得到模块名
                module_name = os.path.splitext(file_name)[0]
                break
        if not module_name:
            print(f"跳过 {mx_dir}：未找到非 _combined 开头的 .sv 模块文件")
            continue

        # 4. 构建 outputPath（mx/IRank/tmp_out/test_<模块名>.json）
        # 先确保 IRank/tmp_out 目录存在（不存在则创建）
        output_dir = os.path.join(mx_dir, "IRank", "tmp_out")
        os.makedirs(output_dir, exist_ok=True)
        # 关键修改：改为固定文件名 analyzer_results.json，移除模块名后缀
        output_path = os.path.join(output_dir, "analyzer_results.json")

        # 5. 构建单个 test 字典（匹配你要求的 JSON 格式）
        test_item = {
            "name": f"Case {module_name}",  # 示例：Case Round_Sgf_Dec
            "topModule": module_name,       # 示例：Round_Sgf_Dec
            "sourceFiles": [combined_sv_path],  # 示例：/xxx/m30/rtl/_combined_rtl_no_comments.sv
            "headerFiles": [],              # 固定为空
            "outputPath": output_path       # 示例：/xxx/m30/IRank/tmp_out/test_Round_Sgf_Dec.json
        }

        # 将当前 test 加入列表
        tests.append(test_item)
        print(f"成功处理：{mx_dir} → 模块名：{module_name}")

    # 6. 将 tests 列表写入 tests.json 文件（带缩进，格式美观）
    with open(OUTPUT_JSON_PATH, "w", encoding="utf-8") as f:
        json.dump(tests, f, indent=4, ensure_ascii=False)

    print(f"\n✅ tests.json 生成完成！路径：{OUTPUT_JSON_PATH}")
    print(f"📊 共处理 {len(tests)} 个 mx 模块")

if __name__ == "__main__":
    main()