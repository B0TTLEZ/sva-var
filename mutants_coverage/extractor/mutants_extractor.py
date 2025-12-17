import argparse
import shutil
from pathlib import Path

def main():
    # 解析命令行参数
    parser = argparse.ArgumentParser(description='Extract mutant SV files from the source mutants_verif directory to a new mutants directory.')
    parser.add_argument('source_dir', help='Path to the source mutants_verif directory (e.g., /data/.../mutants_verif)')
    args = parser.parse_args()

    # 处理源路径，转为绝对路径并检查是否存在
    source_dir = Path(args.source_dir).resolve()
    if not source_dir.exists():
        print(f"Error: Source directory '{source_dir}' does not exist!")
        return
    if not source_dir.is_dir():
        print(f"Error: '{source_dir}' is not a directory!")
        return

    # 定义目标目录：源目录的父目录 / "mutants"
    target_dir = source_dir.parent / "mutants"
    # 创建目标目录（已存在则不报错）
    target_dir.mkdir(exist_ok=True)
    print(f"Target directory created/verified: {target_dir}")

    # 遍历源目录下的子项，筛选出目录（如001、002）
    # 按名称排序（保证001、002、003的顺序）
    subdirs = sorted([item for item in source_dir.iterdir() if item.is_dir()], key=lambda x: x.name)

    if not subdirs:
        print(f"Warning: No subdirectories found in source directory '{source_dir}'!")
        return

    # 处理每个子目录
    for subdir in subdirs:
        # 定义源SV文件路径
        source_sv = subdir / "_combined_rtl_no_comments.sv"
        if not source_sv.exists():
            print(f"Warning: SV file not found in {subdir} -> {source_sv}, skipping this subdirectory!")
            continue

        # 定义目标子目录（如mutants/001）
        target_subdir = target_dir / subdir.name
        target_subdir.mkdir(exist_ok=True)

        # 定义目标SV文件路径
        target_sv = target_subdir / "_combined_rtl_no_comments.sv"

        # 复制文件（使用copy2保留文件元数据，如修改时间）
        shutil.copy2(source_sv, target_sv)
        print(f"Successfully copied: {source_sv} -> {target_sv}")

    print("\nMutant extraction completed!")

if __name__ == "__main__":
    main()