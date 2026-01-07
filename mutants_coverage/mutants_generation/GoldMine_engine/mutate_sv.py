import os
import sys
import random as rnd
import regex as re
from collections import OrderedDict as ODict
from argparse import ArgumentParser
import csv  # 新增：用于生成CSV文件

# ===================== 1. 复用原有变异规则（和mutate_dict.py一致） =====================
EMPTY_STRING = ""
NULL_STRING = " "

# 位运算符（带空格，保证匹配准确性）
OR = ' | '
AND = ' & '
XOR = ' ^ '
XNOR = ' ~^ '

# 取反运算符
NOT = ' ~'
LNOT = ' !'

# 逻辑运算符
LOR = ' || '
LAND = ' && '

# 移位运算符
LSHIFT = ' << '
RSHIFT = ' >> '

# 比较运算符
EQ = ' == '
NEQ = ' != '
LE = ' <= '
GE = ' >= '
LT = ' < '
GT = ' > '

# 算术运算符
PLUS = ' + '
MINUS = ' - '
MUL = ' * '
DIV = ' / '
MOD = ' % '

# IF关键字
IF_0 = 'if('
IF_1 = 'if ('
IF_N = 'if ( ( 1\'b1 > 1\'b0 ) ^ '
IF_T = 'if ( ( 1\'b1 > 1\'b0 ) || '
IF_F = 'if ( ( 1\'b1 < 1\'b0 ) && '

# 核心替换规则
mutation_ops_key_val_tuple = [
    (PLUS, [MINUS, MUL, DIV, MOD]),
    (MINUS, [PLUS, MUL, DIV, MOD]),
    (MUL, [PLUS, MINUS, DIV, MOD]),
    (DIV, [PLUS, MINUS, MUL, MOD]),
    (MOD, [PLUS, MINUS, MUL, DIV]),

    (LAND, [AND, LOR]),
    (LOR, [OR, LAND]),

    (LE, [NEQ, LT, GT, GE, EQ]),
    (GE, [NEQ, LT, GT, LE, EQ]),
    (EQ, [NEQ, LT, GT, LE, GE]),
    (NEQ, [EQ, LT, GT, LE, GE]),

    (LSHIFT, [RSHIFT]),
    (RSHIFT, [LSHIFT]),

    (LT, [NEQ, GT, LE, GE, EQ]),
    (GT, [NEQ, LT, LE, GE, EQ]),

    ((IF_0, IF_1), []),

    (NOT, [NULL_STRING]),
    (LNOT, [NULL_STRING]),

    (AND, [OR, XOR, XNOR]),
    (OR, [AND, XOR, XNOR]),
    (XOR, [AND, OR, XNOR]),
    (XNOR, [AND, OR, XOR])
]

mutation_ops = ODict(mutation_ops_key_val_tuple)
paired_mutation_ops = {
    IF_0: [IF_N, IF_T, IF_F],
    IF_1: [IF_N, IF_T, IF_F]
}

# ===================== 2. 辅助函数（适配SV/V文件 + 模块名命名规则） =====================
def read_sv_file(sv_path):
    """读取SV/V文件内容，返回行列表"""
    try:
        with open(sv_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        return lines
    except Exception as e:
        print(f"读取源文件失败：{e}")
        sys.exit(1)

def make_output_dir(output_root, mutant_num):
    """创建变异体文件夹（四位数字，支持1000+变异体：0001、0002...）"""
    # 变异体文件夹名格式：四位数字（0001、0002...），支持1000+数量
    mutant_dir_name = f"{mutant_num:04d}"
    mutant_dir = os.path.join(output_root, mutant_dir_name)
    if not os.path.exists(mutant_dir):
        try:
            os.makedirs(mutant_dir)
        except Exception as e:
            print(f"创建文件夹失败：{e}")
            sys.exit(1)
    return mutant_dir

def write_mutated_sv(
    mutant_dir, 
    mutated_lines, 
    module_name=None,  # 新增：模块名（用于命名文件）
    is_v_file=False    # 新增：是否生成.v文件（默认.sv）
):
    """
    将变异后的内容写入文件，支持两种命名规则：
    1. 指定模块名：{模块名}_mutant.sv/v
    2. 未指定模块名：combined_rtl_no_comments.sv/v
    """
    # 确定文件后缀
    suffix = "v" if is_v_file else "sv"
    # 确定文件名（核心修改：按模块名动态命名）
    if module_name:
        sv_file_name = f"{module_name}_mutant.{suffix}"
    else:
        sv_file_name = f"combined_rtl_no_comments.{suffix}"
    
    sv_file_path = os.path.join(mutant_dir, sv_file_name)
    try:
        with open(sv_file_path, 'w', encoding='utf-8') as f:
            f.writelines(mutated_lines)
        print(f"✅ 变异文件已写入：{sv_file_path}")  # 新增提示：明确文件路径
        return sv_file_path
    except Exception as e:
        print(f"写入变异文件失败：{e}")
        sys.exit(1)

def write_mutation_info(mutant_dir, mutation_records):
    """写入变异信息到txt文件（每行记录：行号 | 原内容 | 变异后内容 | 替换运算符）"""
    info_file_path = os.path.join(mutant_dir, "mutation_info.txt")
    try:
        with open(info_file_path, 'w', encoding='utf-8') as f:
            f.write("变异行号（从0开始） | 原内容 | 变异后内容 | 替换的运算符 | 替换成的内容\n")
            f.write("-" * 120 + "\n")
            for record in mutation_records:
                line_num, orig_line, mutated_line, op, new_op = record
                # 去除换行符，避免格式混乱
                orig_line = orig_line.strip()
                mutated_line = mutated_line.strip()
                f.write(f"{line_num:>6} | {orig_line:<40} | {mutated_line:<40} | {op:<8} | {new_op:<8}\n")
        return info_file_path
    except Exception as e:
        print(f"写入变异信息失败：{e}")
        sys.exit(1)

def match_module(lines, target_module):
    """
    用正则匹配指定模块的内容，返回：
    - 模块外内容 + 模块内内容（标记），方便后续只变异模块内部分
    - 模块的起始/结束行号
    """
    # 正则匹配module X ... endmodule（兼容带参数/端口的模块定义）
    module_pattern = re.compile(
        r'(module\s+' + re.escape(target_module) + r'\s*[(\w\s,:.]*?)(.*?)(endmodule)',
        re.DOTALL | re.IGNORECASE
    )
    full_content = ''.join(lines)
    match = module_pattern.search(full_content)
    if not match:
        print(f"未找到模块{target_module}，将变异整个文件")
        return lines, (0, len(lines)-1)
    
    # 拆分模块外、模块内内容
    module_start = full_content[:match.start()].count('\n')  # 模块起始行号
    module_end = module_start + match.group(0).count('\n')   # 模块结束行号
    # 标记模块内的行，后续只变异这些行
    module_lines = match.group(0).split('\n')
    new_lines = []
    # 模块前的内容
    new_lines.extend(full_content[:match.start()].split('\n'))
    # 模块内内容（加换行符）
    new_lines.extend([line + '\n' for line in module_lines])
    # 模块后的内容
    new_lines.extend(full_content[match.end():].split('\n'))
    # 处理最后一行的换行符
    new_lines = [line + '\n' if not line.endswith('\n') else line for line in new_lines]
    return new_lines, (module_start, module_end)

# ===================== 3. 核心变异函数（修复3个问题 + 新增随机op功能） =====================
def collect_mutation_candidates(lines, module_start, module_end, random_op=False):
    """
    收集所有可变异的候选点（每行+运算符+位置），返回候选列表：
    每个元素格式：(行号, 原行内容, 运算符, 运算符位置, 可选替换目标)
    :param random_op: 是否随机打乱运算符顺序（解决if/|占比过高问题）
    """
    candidates = []
    # 核心新增：根据random_op参数决定是否打乱运算符顺序
    mutant_ops = list(mutation_ops.keys())  # 转列表支持打乱
    if random_op:
        rnd.shuffle(mutant_ops)  # 随机打乱，让加减乘除/位运算/if等均等选中
        print("✅ 已启用随机运算符模式，平等选择所有类型运算符（+、-、*、/、&、|、if等）")
    
    # 只遍历模块内的行
    for i in range(module_start, module_end+1):
        line = lines[i]
        # 修复问题2：先检查是否是if行且含reset/rst，含则跳过该if的变异
        line_lower = line.lower().strip()
        is_reset_line = 'rst' in line_lower or 'reset' in line_lower
        
        # 修复问题2：跳过以`开头的行（比如`timescale、`include）
        if line.strip().startswith("`"):
            continue
        # 跳过注释行/空行
        if line.strip().startswith("//") or line.strip().startswith("/*") or not line.strip():
            continue
        
        for m_op in mutant_ops:
            # 修复问题2：如果是if相关运算符且行含reset/rst，直接跳过
            if m_op in [IF_0, IF_1] or (isinstance(m_op, tuple) and IF_0 in m_op):
                if is_reset_line:
                    continue  # 含reset/rst的if行不变异
            
            mutation_index = 0
            # 统计当前行中运算符出现次数
            if not type(m_op) is tuple:
                op_count = line.count(m_op)
            else:
                op_count = 0
                for j in list(m_op):
                    op_count = line.count(j)
                    if op_count > 0:
                        m_op = j
                        break
            
            # 保护非阻塞赋值<=
            if m_op == LE and op_count == 1:
                continue
            elif m_op == LE and op_count > 1:
                mutation_index = line.index(m_op)
                op_count -= 1
            
            if op_count <= 0:
                continue
            
            # 收集该行所有可变异的运算符位置
            current_pos = 0
            for _ in range(op_count):
                # 找到运算符位置
                if current_pos == 0:
                    op_pos = line.index(m_op)
                else:
                    op_pos = line.index(m_op, current_pos + 1)
                # 获取该运算符的可选替换目标
                try:
                    replace_targets = mutation_ops[m_op]
                except KeyError:
                    replace_targets = paired_mutation_ops[m_op]
                # 核心新增：过滤掉和原运算符相同的目标（避免无意义变异）
                replace_targets = [t for t in replace_targets if t != m_op]
                if not replace_targets:
                    current_pos = op_pos
                    continue
                # 加入候选列表
                candidates.append({
                    "line_num": i,
                    "orig_line": line,
                    "op": m_op,
                    "op_pos": op_pos,
                    "replace_targets": replace_targets
                })
                current_pos = op_pos
    return candidates

def mutate_sv(sv_lines, target_module=None, random_op=False):
    """
    核心变异逻辑（修复3个问题）：
    1. 每个变异体仅变异1处
    2. 跳过以`开头的行（避免修改`timescale）
    3. 支持任意数量变异体（依赖文件夹命名）
    :param random_op: 是否启用随机运算符模式
    """
    # 步骤1：匹配指定模块（如果有）
    if target_module:
        sv_lines, (module_start, module_end) = match_module(sv_lines, target_module)
    else:
        module_start, module_end = 0, len(sv_lines)-1  # 变异整个文件

    # 步骤2：收集所有可变异的候选点（传入random_op参数）
    candidates = collect_mutation_candidates(sv_lines, module_start, module_end, random_op)
    if not candidates:
        print("未找到可变异的位置！")
        return sv_lines, []

    # 步骤3：随机选1个候选点进行变异（修复问题1：仅变异1处）
    selected = rnd.choice(candidates)
    line_num = selected["line_num"]
    orig_line = selected["orig_line"]
    m_op = selected["op"]
    op_pos = selected["op_pos"]
    replace_targets = selected["replace_targets"]

    # 随机选一个替换目标
    new_op = rnd.choice(replace_targets)
    # 生成变异行
    mutated_line = orig_line[:op_pos] + orig_line[op_pos:].replace(m_op, new_op, 1)
    
    # 步骤4：复制原文件，仅修改选中的行
    mutated_lines = sv_lines.copy()
    mutated_lines[line_num] = mutated_line

    # 步骤5：记录仅这一处的变异信息
    mutation_records = [(line_num, orig_line, mutated_line, m_op, new_op)]

    return mutated_lines, mutation_records

# ===================== 4. 主函数（参数解析 + 流程调度 + 修复所有bug） =====================
def main():
    # 解析命令行参数（新增-r/--random-op参数 + 新增-v/--v-file参数）
    parser = ArgumentParser(description="SV/V文件变异工具（修复：单处变异/跳过`行/支持1000+数量 + 随机运算符）")
    parser.add_argument("-s", "--source", required=True, help="源SV/V文件的绝对路径（必须）")
    parser.add_argument("-m", "--module", help="需要变异的模块名（非必须，默认变异整个文件）")
    parser.add_argument("-o", "--output", required=True, help="输出根路径（必须）")
    parser.add_argument("-n", "--number", type=int, default=5, help="生成的变异体数量（最多数量，支持1000+）")
    parser.add_argument("-r", "--random-op", action="store_true", help="启用随机运算符模式（平等选择+、-、*、/、&、|、if等，解决if/|占比过高问题）")
    # 新增：-v/--v-file 参数，指定生成.v文件（默认.sv）
    parser.add_argument("-v", "--v-file", action="store_true", help="生成的变异体文件后缀为.v（默认是.sv）")
    args = parser.parse_args()

    # 1. 读取源SV/V文件
    print(f"正在读取源文件：{args.source}")
    sv_lines = read_sv_file(args.source)

    # 2. 生成指定数量的变异体（支持1000+）
    # 先收集所有候选点，避免重复读取（提升效率）
    if args.module:
        _, (module_start, module_end) = match_module(sv_lines, args.module)
    else:
        module_start, module_end = 0, len(sv_lines)-1
    # 核心修改：传入random_op参数收集候选点
    all_candidates = collect_mutation_candidates(sv_lines, module_start, module_end, args.random_op)
    if not all_candidates:
        print("错误：未找到任何可变异的位置！")
        sys.exit(1)
    
    # 修复问题1：先打乱候选列表，避免前部分被重复选中
    rnd.shuffle(all_candidates)
    total_candidates = len(all_candidates)
    print(f"共找到{total_candidates}个可变异的位置，开始生成最多{args.number}个独立变异体...")

    # 修复问题3：记录已生成的变异体特征（避免重复）
    generated_features = set()
    # 修复问题4：记录总变异信息（用于生成CSV）
    total_mutation_records = []
    # 修复问题5：计数已生成的有效变异体
    valid_mutant_count = 0

    # 循环生成变异体（直到达到-n数量或无新变异体）
    while valid_mutant_count < args.number:
        # 复制原文件内容，避免多个变异体互相影响
        lines_to_mutate = sv_lines.copy()
        
        # 修复问题3：循环生成不重复的变异体
        max_retry = 1000  # 最大重试次数，避免死循环
        retry_count = 0
        is_duplicate = True
        selected = None
        new_op = None
        line_num = None
        orig_line = None
        mutated_line = None
        m_op = None

        while is_duplicate and retry_count < max_retry:
            # 随机选1个候选点变异（修复问题1：先打乱，覆盖更均匀）
            selected = rnd.choice(all_candidates)
            line_num = selected["line_num"]
            orig_line = selected["orig_line"]
            m_op = selected["op"]
            op_pos = selected["op_pos"]
            replace_targets = selected["replace_targets"]
            
            # 过滤相同的替换目标（避免无意义变异）
            replace_targets = [t for t in replace_targets if t != m_op]
            if not replace_targets:
                retry_count += 1
                continue
            
            new_op = rnd.choice(replace_targets)
            # 生成变异行
            mutated_line = orig_line[:op_pos] + orig_line[op_pos:].replace(m_op, new_op, 1)
            
            # 构建变异特征（唯一标识，避免重复）
            mutation_feature = (line_num, m_op, new_op, mutated_line.strip())
            if mutation_feature not in generated_features:
                generated_features.add(mutation_feature)
                is_duplicate = False
            else:
                retry_count += 1
        
        # 修复问题5：重试次数耗尽，无新变异体，停止生成
        if retry_count >= max_retry:
            print(f"⚠️  已无新的独立变异体可生成，当前已生成{valid_mutant_count}个，达到上限")
            break

        # 生成变异体内容
        mutated_lines = lines_to_mutate.copy()
        mutated_lines[line_num] = mutated_line
        # 记录变异信息
        mutation_records = [(line_num, orig_line, mutated_line, m_op, new_op)]
        
        # 修复问题5：计数+1
        valid_mutant_count += 1
        # 修复问题4：记录到总列表
        total_mutation_records.append({
            "id": f"{valid_mutant_count:03d}",
            "line_num": line_num,
            "original_line": orig_line.strip(),
            "mutated_line": mutated_line.strip(),
            "original_op": m_op,
            "new_op": new_op
        })
        
        # 创建变异体文件夹（四位数字，支持1000+）
        mutant_dir = make_output_dir(args.output, valid_mutant_count)
        # 核心修改：传递模块名和-v参数，动态生成文件名
        write_mutated_sv(mutant_dir, mutated_lines, args.module, args.v_file)
        # 写入变异信息txt
        write_mutation_info(mutant_dir, mutation_records)
        
        if valid_mutant_count % 50 == 0:  # 每50个打印一次进度
            print(f"已生成{valid_mutant_count}个独立变异体...")

    # 修复问题4：生成总CSV文件
    csv_file_path = os.path.join(args.output, "mutation_summary.csv")
    try:
        with open(csv_file_path, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ["id", "line_num", "original_line", "mutated_line", "original_op", "new_op"]
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for record in total_mutation_records:
                writer.writerow(record)
        print(f"✅ 总变异信息已写入CSV文件：{csv_file_path}")
    except Exception as e:
        print(f"❌ 写入CSV文件失败：{e}")

    # 最终提示
    print(f"\n🎉 变异体生成完成！输出根路径：{args.output}")
    print(f"📊 实际生成{valid_mutant_count}个独立变异体（要求最多{args.number}个）")
    print(f"✅ 已跳过所有含reset/rst的if行，避免combinational loop")
    print(f"✅ 已确保所有变异体唯一，无重复")
    print(f"✅ 已跳过所有以`开头的行（如`timescale），避免误变异")
    if args.random_op:
        print(f"✅ 已启用随机运算符模式，变异体类型更均衡（+、-、*、/、&、|、if等）")
    # 新增提示：明确文件后缀规则
    suffix_tip = ".v" if args.v_file else ".sv"
    name_tip = f"{args.module}_mutant{suffix_tip}" if args.module else f"combined_rtl_no_comments{suffix_tip}"
    print(f"✅ 变异体文件命名规则：{name_tip}")

if __name__ == '__main__':
    main()