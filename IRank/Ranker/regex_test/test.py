import re
import math
import json
from typing import List, Tuple


# -------------------------- 核心解析函数（带调试+修复）--------------------------
def parse_delay(delay_str):
    """
    解析延迟字符串，支持以下格式：
    - ##n（普通数字延迟）：返回n
    - ##[a:b]（数字范围延迟）：返回(a + b) / 2 向上取整
    - ##[a:$]（无限范围延迟）：返回a + 3
    """
    delay_core = delay_str.lstrip('##')
    if '[' in delay_core and ']' in delay_core:
        range_part = delay_core.strip('[]')
        a_str, b_str = range_part.split(':', 1)
        a = int(a_str.strip())
        b = b_str.strip()
        if b == '$' or not b:
            return a + 3
        else:
            b_int = int(b)
            avg = (a + b_int) / 2
            return math.ceil(avg)
    else:
        return int(delay_core)


def extract_vars_from_expr(expr):
    """从表达式中提取变量名，直接移除数组索引，过滤关键字"""
    print(f"\n[调试] extract_vars_from_expr 输入: {expr}")
    # 移除Verilog风格常量
    verilog_const_pattern = re.compile(r'\d+\'[bdho][0-9a-fA-F]+', re.IGNORECASE)
    expr = verilog_const_pattern.sub(' ', expr)
    print(f"[调试] 移除Verilog常量后: {expr}")
    
    # 直接删除数组索引（[]及内部所有内容）
    expr = re.sub(r'\[.*?\]', '', expr)
    print(f"[调试] 移除数组索引后: {expr}")
    
    # 匹配变量名（支持层级：A.B.C格式）
    var_pattern = re.compile(r'\b([A-Za-z_][A-Za-z0-9_.]*)\b')
    forbidden_words = {
        'posedge', 'negedge', 'disable', 'iff', 'assert', 'property', 'return',
        'if', 'else', 'case', 'rose', 'fell', 'past', 'true', 'false', 'null', 'default',
        'stable', 'always', 'inside', '$isunknown', '$past', '$rose', '$fell'
    }
    
    vars = []
    for match in var_pattern.finditer(expr):
        var = match.group(1)
        # 过滤关键字和系统函数
        if (var not in forbidden_words and
            not var.startswith('$') and
            not var[0].isdigit()):
            vars.append(var)
            print(f"[调试] 提取到变量: {var} (过滤后保留)")
        else:
            print(f"[调试] 过滤变量: {var} (关键字/系统函数)")
    
    print(f"[调试] extract_vars_from_expr 最终提取变量列表: {vars}")
    return vars


def clean_and_split_sva(sva_string):
    """
    提取并清洗SVA核心表达式，分割前件/后件，适配|->（立即蕴含）/|=>（延迟蕴含）
    """
    print(f"\n========== clean_and_split_sva 调试信息 ==========")
    print(f"原始输入SVA: {sva_string}")
    
    # 步骤1：提取assert property(...)括号内的核心内容
    assert_pattern = re.compile(r'assert\s+property\s*\(\s*(.*?)\s*\)\s*;', re.DOTALL | re.IGNORECASE)
    match_assert = assert_pattern.search(sva_string)
    if not match_assert:
        raise ValueError("无法识别断言的结构：未找到assert property语句")
    assert_arg = match_assert.group(1).strip()
    print(f"步骤1 - 提取property内内容: {assert_arg}")

    # 步骤2：移除disable iff子句
    disable_iff_pattern = re.compile(r'disable\s+iff\s*\(.*?\)', re.DOTALL | re.IGNORECASE)
    clean_arg = disable_iff_pattern.sub('', assert_arg).strip()
    print(f"步骤2 - 移除disable iff后: {clean_arg}")

    # 步骤3：移除时钟子句（@(posedge clk)等）
    clock_pattern = re.compile(r'@\(.*?\)', re.DOTALL | re.IGNORECASE)
    core_expr = clock_pattern.sub('', clean_arg).strip()
    print(f"步骤3 - 移除时钟子句后: {core_expr}")

    # 步骤4：去除核心表达式的外层括号（修复：更严谨的括号匹配）
    def remove_outer_brackets(s):
        """仅移除最外层的成对括号，严格检查括号深度"""
        if not s.startswith('(') or not s.endswith(')'):
            return s.strip()
        
        bracket_depth = 0
        valid_outer = True
        for i, char in enumerate(s):
            if char == '(':
                bracket_depth += 1
            elif char == ')':
                bracket_depth -= 1
            # 只有当最后一个字符才让深度归0，才是外层括号
            if bracket_depth == 0 and i != len(s)-1:
                valid_outer = False
                break
        
        if valid_outer:
            return remove_outer_brackets(s[1:-1].strip())
        else:
            return s.strip()
    
    core_expr = remove_outer_brackets(core_expr)
    print(f"步骤4 - 移除外层括号后: {core_expr}")

    # 步骤5：识别蕴含符并分割前件/后件（修复：括号深度计算更严谨）
    implication_pos = -1
    implication_op = None
    bracket_depth = 0
    i = 0
    while i < len(core_expr):
        char = core_expr[i]
        if char == '(':
            bracket_depth += 1
        elif char == ')':
            bracket_depth -= 1
        elif bracket_depth == 0:
            # 优先识别长的|=>，避免被|->匹配
            if i + 2 < len(core_expr) and core_expr[i:i+3] == '|=>':
                implication_pos = i
                implication_op = '|=>'
                break
            elif i + 2 < len(core_expr) and core_expr[i:i+3] == '|->':
                implication_pos = i
                implication_op = '|->'
                break
        i += 1

    # 分割并清洗前件/后件
    if implication_pos != -1:
        antecedent_part = core_expr[:implication_pos].strip()
        consequent_part = core_expr[implication_pos + len(implication_op):].strip()
        # 仅移除前件/后件首尾的空白，不碰括号
        antecedent_part = antecedent_part.strip()
        consequent_part = consequent_part.strip()
        is_delayed_implication = (implication_op == '|=>')
        print(f"步骤5 - 识别到蕴含符: {implication_op}")
        print(f"步骤5 - 前件: {antecedent_part}")
        print(f"步骤5 - 后件: {consequent_part}")
        print(f"步骤5 - 是否延迟蕴含: {is_delayed_implication}")
    else:
        antecedent_part = ""
        consequent_part = core_expr.strip()
        is_delayed_implication = False
        print(f"步骤5 - 未识别到蕴含符")
        print(f"步骤5 - 前件: 空")
        print(f"步骤5 - 后件: {consequent_part}")

    return antecedent_part, consequent_part, is_delayed_implication


def extract_variables(expression, current_cycle):
    """从条件表达式提取变量+对应周期（修复：$past正则匹配+括号处理）"""
    print(f"\n========== extract_variables 调试信息 ==========")
    print(f"输入表达式: {expression}")
    print(f"当前基准周期: {current_cycle}")
    
    variables = []
    
    def add_vars_from_expr(expr, cycle):
        print(f"\n--- add_vars_from_expr 子函数 ---")
        print(f"子函数输入表达式: {expr}")
        print(f"子函数目标周期: {cycle}")
        extracted_vars = extract_vars_from_expr(expr)
        for var in extracted_vars:
            # 检查是否已存在相同变量+周期
            exists = any(v[0] == var and v[1] == cycle for v in variables)
            if not exists:
                variables.append((var, cycle))
                print(f"添加变量-周期对: ({var}, {cycle})")
            else:
                print(f"变量-周期对已存在，跳过: ({var}, {cycle})")
    
    # 处理信号拼接
    concat_pattern = re.compile(r'\{(.*?)\}', re.DOTALL)
    for match in concat_pattern.finditer(expression):
        print(f"\n处理信号拼接: {match.group(0)}")
        concat_content = match.group(1).strip()
        concat_vars = [v.strip() for v in concat_content.split(',') if v.strip()]
        for var in concat_vars:
            add_vars_from_expr(var, current_cycle)
        # 替换拼接内容为空格，避免重复处理
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]
    
    # 处理$past（修复：基于括号深度的正则匹配，确保完整捕获）
    # 匹配$past(...) 包含嵌套括号
    def find_past_expressions(s):
        past_matches = []
        start = 0
        while start < len(s):
            past_start = s.find('$past(', start)
            if past_start == -1:
                break
            # 计算括号深度，找到对应的闭合括号
            bracket_depth = 0
            past_end = -1
            for i in range(past_start + len('$past('), len(s)):
                if s[i] == '(':
                    bracket_depth += 1
                elif s[i] == ')':
                    if bracket_depth == 0:
                        past_end = i
                        break
                    else:
                        bracket_depth -= 1
            if past_end != -1:
                past_matches.append((past_start, past_end + 1))
                start = past_end + 1
            else:
                start = past_start + 1
        return past_matches
    
    past_matches = find_past_expressions(expression)
    for (start, end) in past_matches:
        past_expr = expression[start:end]
        print(f"\n处理$past函数: {past_expr}")
        # 提取$past内部内容
        past_content = past_expr[len('$past('):-1].strip()
        print(f"$past内部内容: {past_content}")
        
        # 分割$past的参数（处理括号嵌套）
        past_parts = []
        bracket_depth = 0
        current_part = []
        for char in past_content:
            if char == ',' and bracket_depth == 0:
                past_parts.append(''.join(current_part).strip())
                current_part = []
            else:
                if char == '(':
                    bracket_depth += 1
                elif char == ')':
                    bracket_depth -= 1
                current_part.append(char)
        if current_part:
            past_parts.append(''.join(current_part).strip())
        
        print(f"$past分割后的参数: {past_parts}")
        signal_expr = past_parts[0] if past_parts else ''
        past_delay = int(past_parts[1]) if len(past_parts) >= 2 and past_parts[1].strip().isdigit() else 1
        past_var_cycle = current_cycle - past_delay
        
        print(f"$past信号表达式: {signal_expr}")
        print(f"$past延迟值: {past_delay}")
        print(f"计算出的$past变量周期: {past_var_cycle}")
        
        # 添加$past中的变量
        add_vars_from_expr(signal_expr, past_var_cycle)
        
        # 替换$past内容为空格，避免重复处理
        expression = expression[:start] + ' ' * (end - start) + expression[end:]
    
    # 处理$rose/$fell/$isunknown
    rise_fall_unknown_pattern = re.compile(r'\$(rose|fell|isunknown)\s*\((.*?)\)', re.DOTALL | re.IGNORECASE)
    for match in rise_fall_unknown_pattern.finditer(expression):
        print(f"\n处理$rose/$fell/$isunknown: {match.group(0)}")
        signal_expr = match.group(2).strip()
        add_vars_from_expr(signal_expr, current_cycle)
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]
    
    # 处理通用变量
    print(f"\n处理通用变量（剩余表达式）: {expression}")
    add_vars_from_expr(expression, current_cycle)
    
    print(f"\n========== extract_variables 结果 ==========")
    print(f"最终提取的变量-周期列表: {variables}")
    return variables


def parse_sva_sequence(antecedent_str, consequent_str, is_delayed):
    """解析SVA前件/后件的变量和相对周期（修复：不再移除表达式内的括号）"""
    print(f"\n========== parse_sva_sequence 调试信息 ==========")
    print(f"前件字符串: {antecedent_str}")
    print(f"后件字符串: {consequent_str}")
    print(f"是否延迟蕴含: {is_delayed}")
    
    delay_pattern = r'(##(?:\d+|\[\s*\d+\s*:\s*(?:\$|\d+)\s*\]))'

    # 解析前件
    antecedent_vars = []
    relative_cycle = 0
    print(f"\n--- 解析前件 ---")
    if antecedent_str:
        sequence_parts = re.split(delay_pattern, antecedent_str)
        print(f"前件分割后的部分: {sequence_parts}")
        for part in sequence_parts:
            part = part.strip()
            if not part:
                continue
            if part.startswith('##'):
                delay_val = parse_delay(part)
                relative_cycle += delay_val
                print(f"处理延迟 {part} → 延迟值 {delay_val} → 当前周期 {relative_cycle}")
                continue
            # 只替换&&为&，不分割（避免括号内的&被分割）
            part = part.replace('&&', '&')
            # 修复：仅strip空白，不再strip括号！！！
            prop = part.strip()
            if prop:
                print(f"处理前件命题: {prop} (当前周期 {relative_cycle})")
                vars = extract_variables(prop, relative_cycle)
                antecedent_vars.extend(vars)
    else:
        print(f"前件为空")

    # 解析后件
    consequent_vars = []
    consequent_base_cycle = 1 if is_delayed else 0
    current_consequent_cycle = consequent_base_cycle
    print(f"\n--- 解析后件 ---")
    print(f"后件基础周期: {consequent_base_cycle} (延迟蕴含: {is_delayed})")
    if consequent_str:
        sequence_parts = re.split(delay_pattern, consequent_str)
        print(f"后件分割后的部分: {sequence_parts}")
        for part in sequence_parts:
            part = part.strip()
            if not part:
                continue
            if part.startswith('##'):
                delay_val = parse_delay(part)
                current_consequent_cycle += delay_val
                print(f"处理延迟 {part} → 延迟值 {delay_val} → 当前周期 {current_consequent_cycle}")
                continue
            # 只替换&&为&，不分割（避免括号内的&被分割）
            part = part.replace('&&', '&')
            # 修复：仅strip空白，不再strip括号！！！
            prop = part.strip()
            if prop:
                print(f"处理后件命题: {prop} (当前周期 {current_consequent_cycle})")
                vars = extract_variables(prop, current_consequent_cycle)
                consequent_vars.extend(vars)
    else:
        print(f"后件为空")

    # 去重并排序
    def dedup_and_sort(vars_list):
        print(f"\n--- 去重排序 ---")
        print(f"去重前列表: {vars_list}")
        deduped = list({(var, cycle) for var, cycle in vars_list})
        sorted_list = sorted(deduped, key=lambda x: (x[1], x[0]))
        print(f"去重排序后列表: {sorted_list}")
        return sorted_list

    antecedent_dedup = dedup_and_sort(antecedent_vars)
    consequent_dedup = dedup_and_sort(consequent_vars)

    result = {
        "antecedent": [
            {"variable": var, "relative_cycle": cycle}
            for var, cycle in antecedent_dedup
        ],
        "consequent": [
            {"variable": var, "relative_cycle": cycle}
            for var, cycle in consequent_dedup
        ]
    }
    
    print(f"\n========== parse_sva_sequence 最终结果 ==========")
    print(f"前件变量: {result['antecedent']}")
    print(f"后件变量: {result['consequent']}")
    
    return result


# -------------------------- 测试主函数 --------------------------
def test_sva_parser():
    # 你的测试输入字符串
    test_sva = """i2c_master_top_wb_dat_o_3: assert property (@(posedge i2c_master_top.byte_controller.bit_controller.clk) disable iff (!i2c_master_top.byte_controller.bit_controller.nReset) (($changed(i2c_master_top.byte_controller.bit_controller.cSDA)) |-> ($past(!i2c_master_top.byte_controller.bit_controller.nReset) || $past(i2c_master_top.byte_controller.bit_controller.rst) || ($past(i2c_master_top.byte_controller.bit_controller.nReset && !i2c_master_top.byte_controller.bit_controller.rst)))));"""
    
    print("========== 测试开始 ==========")
    print(f"原始测试输入: {test_sva}")
    
    # 提取纯SVA部分（去掉前面的assert_id）
    if ':' in test_sva:
        _, sva_str = test_sva.split(':', 1)
        sva_str = sva_str.strip()
    else:
        sva_str = test_sva.strip()
    
    try:
        # 执行解析
        antecedent, consequent, is_delayed = clean_and_split_sva(sva_str)
        result = parse_sva_sequence(antecedent, consequent, is_delayed)
        
        # 构造输出格式（和你要求的一致）
        output = {
            "antecedents": result["antecedent"],
            "consequents": result["consequent"]
        }
        
        # 格式化输出（缩进2个空格，和示例一致）
        print(f"\n========== 最终输出结果 ==========")
        print(json.dumps(output, indent=2))
        
    except Exception as e:
        print(f"\n解析出错：{str(e)}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    test_sva_parser()