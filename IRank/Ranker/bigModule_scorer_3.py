import json
import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Any, Set, Tuple
from collections import defaultdict
import math


# -------------------------- 延迟解析函数（无修改）--------------------------
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
    """从表达式中提取变量名，修复：直接移除数组索引，不再使用占位符"""
    # 移除Verilog风格常量
    verilog_const_pattern = re.compile(r'\d+\'[bdho][0-9a-fA-F]+', re.IGNORECASE)
    expr = verilog_const_pattern.sub(' ', expr)
    
    # 核心修复：直接删除数组索引（[]及内部所有内容），而非替换为占位符
    # 例如：cSDA[0] → cSDA，data[addr+1] → data
    expr = re.sub(r'\[.*?\]', '', expr)
    
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
    
    return vars

def clean_and_split_sva(sva_string):
    """
    修复：优先去除核心表达式的外层括号，确保蕴含符识别正确
    精确分割SVA前件/后件，适配|->（立即蕴含）/|=>（延迟蕴含）
    """
    # ========== 步骤1：提取assert property(...)括号内的核心内容 ==========
    assert_pattern = re.compile(r'assert\s+property\s*\(\s*(.*?)\s*\)\s*;', re.DOTALL | re.IGNORECASE)
    match_assert = assert_pattern.search(sva_string)
    if not match_assert:
        raise ValueError("无法识别断言的结构：未找到assert property语句")
    assert_arg = match_assert.group(1).strip()

    # ========== 步骤2：移除disable iff子句 ==========
    disable_iff_pattern = re.compile(r'disable\s+iff\s*\(.*?\)', re.DOTALL | re.IGNORECASE)
    clean_arg = disable_iff_pattern.sub('', assert_arg).strip()

    # ========== 步骤3：移除时钟子句（@(posedge clk)等） ==========
    clock_pattern = re.compile(r'@\(.*?\)', re.DOTALL | re.IGNORECASE)
    core_expr = clock_pattern.sub('', clean_arg).strip()

    # ========== 关键修复：更严谨的外层括号移除逻辑 ==========
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

    # ========== 步骤4：识别蕴含符（|->/|=>），核心修复逻辑 ==========
    implication_pos = -1
    implication_op = None
    bracket_depth = 0
    i = 0
    # 遍历每个字符，仅在括号深度为0时识别蕴含符
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

    # ========== 步骤5：分割前件/后件（修复：不再移除前件后件的括号） ==========
    if implication_pos != -1:
        # 有蕴含符：正确分割前件和后件（仅strip空白，不移除括号）
        antecedent_part = core_expr[:implication_pos].strip()
        consequent_part = core_expr[implication_pos + len(implication_op):].strip()
        is_delayed_implication = (implication_op == '|=>')
    else:
        # 无蕴含符：前件为空，后件为核心表达式
        antecedent_part = ""
        consequent_part = core_expr.strip()
        is_delayed_implication = False

    return antecedent_part, consequent_part, is_delayed_implication

def extract_variables(expression, current_cycle):
    """从条件表达式提取变量+周期（修复：$past匹配逻辑+括号处理）"""
    variables = []
    
    def add_vars_from_expr(expr, cycle):
        extracted_vars = extract_vars_from_expr(expr)
        for var in extracted_vars:
            if not any(v[0] == var and v[1] == cycle for v in variables):
                variables.append((var, cycle))
    
    # 处理信号拼接
    concat_pattern = re.compile(r'\{(.*?)\}', re.DOTALL)
    for match in concat_pattern.finditer(expression):
        concat_content = match.group(1).strip()
        concat_vars = [v.strip() for v in concat_content.split(',') if v.strip()]
        for var in concat_vars:
            add_vars_from_expr(var, current_cycle)
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]
    
    # 修复：基于括号深度匹配$past，避免截断
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
        # 提取$past内部内容
        past_content = past_expr[len('$past('):-1].strip()
        
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
        
        signal_expr = past_parts[0] if past_parts else ''
        past_delay = int(past_parts[1]) if len(past_parts) >= 2 and past_parts[1].strip().isdigit() else 1
        past_var_cycle = current_cycle - past_delay
        
        # 添加$past中的变量
        add_vars_from_expr(signal_expr, past_var_cycle)
        # 替换$past内容为空格，避免重复处理
        expression = expression[:start] + ' ' * (end - start) + expression[end:]
    
    # 处理$rose/$fell/$isunknown
    rise_fall_unknown_pattern = re.compile(r'\$(rose|fell|isunknown)\s*\((.*?)\)', re.DOTALL | re.IGNORECASE)
    for match in rise_fall_unknown_pattern.finditer(expression):
        signal_expr = match.group(2).strip()
        add_vars_from_expr(signal_expr, current_cycle)
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]
    
    # 处理通用变量
    add_vars_from_expr(expression, current_cycle)
    return variables

def parse_sva_sequence(antecedent_str, consequent_str, is_delayed):
    """
    修复：确保前件/后件周期计算正确，不再移除表达式内的括号
    - |->（立即蕴含）：后件周期 = 前件周期
    - |=>（延迟蕴含）：后件周期 = 前件周期 + 1
    """
    delay_pattern = r'(##(?:\d+|\[\s*\d+\s*:\s*(?:\$|\d+)\s*\]))'

    # ========== 解析前件 ==========
    antecedent_vars = []
    relative_cycle = 0  # 前件基础周期为0
    if antecedent_str:
        sequence_parts = re.split(delay_pattern, antecedent_str)
        for part in sequence_parts:
            part = part.strip()
            if not part:
                continue
            if part.startswith('##'):
                relative_cycle += parse_delay(part)
                continue
            # 修复：仅替换&&为&，不再分割命题，不再移除括号
            part = part.replace('&&', '&')
            prop = part.strip()  # 仅移除空白，不移除括号
            if prop:
                vars = extract_variables(prop, relative_cycle)
                antecedent_vars.extend(vars)

    # ========== 解析后件（核心修复：延迟蕴含周期+1） ==========
    consequent_vars = []
    # 后件基础周期：|=>则+1，|->则=0
    consequent_base_cycle = 1 if is_delayed else 0
    current_consequent_cycle = consequent_base_cycle
    if consequent_str:
        sequence_parts = re.split(delay_pattern, consequent_str)
        for part in sequence_parts:
            part = part.strip()
            if not part:
                continue
            if part.startswith('##'):
                current_consequent_cycle += parse_delay(part)
                continue
            # 修复：仅替换&&为&，不再分割命题，不再移除括号
            part = part.replace('&&', '&')
            prop = part.strip()  # 仅移除空白，不移除括号
            if prop:
                vars = extract_variables(prop, current_consequent_cycle)
                consequent_vars.extend(vars)

    # 去重并排序
    def dedup_and_sort(vars_list):
        deduped = list({(var, cycle) for var, cycle in vars_list})
        return sorted(deduped, key=lambda x: (x[1], x[0]))

    return {
        "antecedent": [
            {"variable": var, "relative_cycle": cycle}
            for var, cycle in dedup_and_sort(antecedent_vars)
        ],
        "consequent": [
            {"variable": var, "relative_cycle": cycle}
            for var, cycle in dedup_and_sort(consequent_vars)
        ]
    }

# -------------------------- 以下代码无核心逻辑错误，保留 --------------------------
class COIBuilder:
    def __init__(self, var_define_chain: Dict, var_use_chain: Dict, pagerank: Dict, weight_map: Dict):
        self.var_define_chain = var_define_chain
        self.var_use_chain = var_use_chain
        self.pagerank = pagerank
        self.weight_map = weight_map
        self.cois = {}  # Cache for built COIs
    
    def build_coi(self, target_var: str, max_cycles: int) -> Dict:
        cache_key = (target_var, max_cycles)
        if cache_key in self.cois:
            return self.cois[cache_key]
        
        coi = {
            "nodes": {},
            "target": target_var
        }
        
        target_importance = self.pagerank.get(target_var, 0.0)
        target_complexity = self.calculate_complexity(target_var)
        coi["nodes"][(target_var, 0)] = {
            "importance": target_importance,
            "complexity": target_complexity
        }
        
        self._expand_coi(target_var, 0, max_cycles, coi, target_importance, target_complexity)
        self.cois[cache_key] = coi
        return coi 

    def _expand_coi(self, var: str, cycle: int, max_cycles: int, coi: Dict, 
                    parent_importance: float, parent_complexity: float):
        if cycle >= max_cycles:
            return
        
        var_info = self.var_define_chain.get(var, {})
        
        # Process CDeps
        c_deps = var_info.get('CDeps', [])
        for assignment_c_deps in c_deps:
            for control_dep_list in assignment_c_deps:
                for dep_var in control_dep_list:
                    if dep_var:
                        is_clocked = var_info.get('Clocked', False)
                        new_cycle = cycle + (1 if is_clocked else 0)
                        if new_cycle <= max_cycles:
                            node_key = (dep_var, new_cycle)
                            if node_key not in coi["nodes"]:
                                edge_weight = self._get_edge_weight(dep_var, var)
                                relative_importance = self.pagerank.get(dep_var, 0.0) + edge_weight * parent_importance
                                intersection_count = self._calculate_expression_intersection(var, dep_var)
                                relative_complexity = intersection_count + parent_complexity
                                coi["nodes"][node_key] = {
                                    "importance": relative_importance,
                                    "complexity": relative_complexity
                                }
                                self._expand_coi(dep_var, new_cycle, max_cycles, coi, 
                                               relative_importance, relative_complexity)
        
        # Process DDeps
        d_deps = var_info.get('DDeps', [])
        for i, dep_list in enumerate(d_deps):
            expressions = var_info.get('Expressions', [])
            logic_type = expressions[i].get('logicType', 'unknown') if i < len(expressions) else 'unknown'
            for dep_var in dep_list:
                if dep_var:
                    new_cycle = cycle + (1 if logic_type == 'sequential' else 0)
                    if new_cycle <= max_cycles:
                        node_key = (dep_var, new_cycle)
                        if node_key not in coi["nodes"]:
                            edge_weight = self._get_edge_weight(dep_var, var)
                            relative_importance = self.pagerank.get(dep_var, 0.0) + edge_weight * parent_importance
                            intersection_count = self._calculate_expression_intersection(var, dep_var)
                            relative_complexity = intersection_count + parent_complexity
                            coi["nodes"][node_key] = {
                                "importance": relative_importance,
                                "complexity": relative_complexity
                            }
                            self._expand_coi(dep_var, new_cycle, max_cycles, coi, 
                                           relative_importance, relative_complexity)

    def _get_edge_weight(self, src_var: str, dst_var: str) -> int:
        return self.weight_map.get(src_var, {}).get(dst_var, 0)

    def _calculate_expression_intersection(self, var: str, dep_var: str) -> int:
        var_info = self.var_define_chain.get(var, {})
        data_expressions = []
        ddeps = var_info.get('DDeps', [])
        dlines = var_info.get('DLines', [])
        for ddep_list, dline in zip(ddeps, dlines):
            ddep_tuple = tuple(ddep_list)
            data_expressions.append((ddep_tuple, dline))

        control_expressions = []
        cdeps = var_info.get('CDeps', [])
        clines = var_info.get('CLines', [])
        for assignment_cdeps, assignment_clines in zip(cdeps, clines):
            for cdep_list, cline in zip(assignment_cdeps, assignment_clines):
                cdep_tuple = tuple(cdep_list)
                control_expressions.append((cdep_tuple, cline))

        total_expressions = data_expressions + control_expressions
        var_expressions_set = set(total_expressions)

        dep_use_info = self.var_use_chain.get(dep_var, {})
        sensitive_expressions = []
        sens_expr_list = dep_use_info.get('Sensitivities_Expressions', [])
        for sens_expr in sens_expr_list:
            line = sens_expr.get('line', 0)
            driving_signals = sens_expr.get('drivingSignals', [])
            driving_tuple = tuple(driving_signals)
            sensitive_expressions.append((driving_tuple, line))
        dep_sensitive_set = set(sensitive_expressions)

        intersection = var_expressions_set & dep_sensitive_set
        total_count = 0
        for expr_tuple, _ in intersection:
            total_count += len(expr_tuple)
        return total_count

    def calculate_complexity(self, var: str) -> float:
        var_info = self.var_define_chain.get(var, {})
        use_info = self.var_use_chain.get(var, {})
        
        expressions = var_info.get('Expressions', [])
        expr_map = {}
        for expr in expressions:
            key = (expr.get('file', ''), expr.get('line', 0))
            expr_map[key] = expr
        
        sensitivities = use_info.get('Sensitivities_Expressions', [])
        sens_map = {}
        for sens in sensitivities:
            key = (sens.get('file', ''), sens.get('line', 0))
            sens_map[key] = sens
        
        common_keys = set(expr_map.keys()) & set(sens_map.keys())
        complexity = 0.0
        for key in common_keys:
            expr = expr_map[key]
            driving_signals = expr.get('drivingSignals', [])
            complexity += len(driving_signals)
        return float(complexity)
    
    def get_node_scores(self, var: str, cycle: int, coi: Dict) -> Tuple[float, float]:
        node_key = (var, cycle)
        if node_key in coi["nodes"]:
            node = coi["nodes"][node_key]
            return node["importance"], node["complexity"]
        return 0.0, 0.0

def save_coi_cache(cois: Dict, coi_cache_path: str):
    def convert_tuple_keys(obj):
        if isinstance(obj, dict):
            new_dict = {}
            for key, value in obj.items():
                if isinstance(key, tuple):
                    new_key = f"({key[0]},{key[1]})"
                else:
                    new_key = key
                new_dict[new_key] = convert_tuple_keys(value)
            return new_dict
        elif isinstance(obj, list):
            return [convert_tuple_keys(item) for item in obj]
        else:
            return obj
    
    Path(coi_cache_path).parent.mkdir(parents=True, exist_ok=True)
    serializable_cois = convert_tuple_keys(cois)
    with open(coi_cache_path, 'w') as f:
        json.dump(serializable_cois, f, indent=2)
    print(f"Generated COI cache: {coi_cache_path}")
    print(f"Saved {len(cois)} COI structures")

def parse_new_assertions_txt(txt_path: Path, module_name: str) -> Dict[str, List[dict]]:
    assertions_dict = defaultdict(list)
    with open(txt_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    for line_num, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
        # 核心：正确分割ID和SVA字符串（split(':')仅分割第一个冒号）
        if ':' in line:
            assert_id, sva_string = line.split(':', 1)
            assert_id = assert_id.strip()
            sva_string = sva_string.strip()
        else:
            assert_id = f"assert_{line_num}"
            sva_string = line.strip()
        assertions_dict[module_name].append({
            "id": assert_id,       # 正确保存每行的原始ID
            "sva_string": sva_string,
            "status": "proven"
        })
    return dict(assertions_dict)

def process_single_module(module_name: str, module_assertions: List[dict], root_path: Path, mod: str) -> List[dict]:
    # 构建文件路径
    module_dir = root_path / "IRank" / "tmp_out" / module_name
    var_define_chain_path = module_dir / "var_define_chain.json"
    var_use_chain_path = module_dir / "var_use_chain.json"
    pagerank_path = module_dir / "complete_PageRank.json"
    weight_map_path = module_dir / "weight_map.json"
    coi_cache_path = module_dir / "coi_cache.json"

    # 检查文件存在性
    required_files = [var_define_chain_path, var_use_chain_path, pagerank_path, weight_map_path]
    for file_path in required_files:
        if not file_path.exists():
            print(f"Error: 模块{module_name}的文件{file_path}不存在，跳过该模块")
            return []

    # 加载依赖文件
    with open(var_define_chain_path, 'r') as f:
        var_define_chain = json.load(f)
    with open(var_use_chain_path, 'r') as f:
        var_use_chain = json.load(f)
    with open(pagerank_path, 'r') as f:
        pagerank = json.load(f)
    with open(weight_map_path, 'r') as f:
        weight_map = json.load(f)

    coi_builder = COIBuilder(var_define_chain, var_use_chain, pagerank, weight_map)
    proven_assertions = [(idx, item) for idx, item in enumerate(module_assertions) if item.get("status") == "proven"]
    if not proven_assertions:
        print(f"模块{module_name}没有proven的断言，跳过")
        save_coi_cache({}, coi_cache_path)
        return []

    module_results = []
    max_cycle = 0
    parsed_assertions = []

    for idx, assertion in proven_assertions:
        sva_string = assertion["sva_string"]
        assert_id = assertion.get("id", idx)  # 正确获取每行的原始ID
        try:
            antecedent_str, consequent_str, is_delayed = clean_and_split_sva(sva_string)
            parsed = parse_sva_sequence(antecedent_str, consequent_str, is_delayed)

            # 模式判断：是否拼接模块名
            if mod == "original":
                for item in parsed["antecedent"]:
                    item["variable"] = f"{module_name}.{item['variable']}"
                for item in parsed["consequent"]:
                    item["variable"] = f"{module_name}.{item['variable']}"

            # 更新最大周期
            all_cycles = [item["relative_cycle"] for item in parsed["antecedent"] + parsed["consequent"]]
            if all_cycles:
                max_cycle = max(max_cycle, max(all_cycles))

            parsed_assertions.append({
                "idx": idx,
                "assert_id": assert_id,  # 保存当前断言的原始ID
                "sva_string": sva_string,
                "status": "proven",
                "module": module_name,
                **parsed
            })
        except Exception as e:
            print(f"模块{module_name}的断言{assert_id}解析失败：{e}")
            module_results.append({
                "sva_string": sva_string,
                "status": "proven",
                "module": module_name,
                "id": assert_id,  # 异常时也使用原始ID
                "importance_score": 0.0,
                "complexity_score": 0.0,
                "final_score": 0.0,
                "antecedents": [],
                "consequents": []
            })
            continue

    # 计算分数（核心修复：使用当前断言的assert_id，而非外层变量）
    for assertion in parsed_assertions:
        antecedents = assertion["antecedent"]
        consequents = assertion["consequent"]
        total_importance = 0.0
        total_complexity = 0.0
        current_assert_id = assertion["assert_id"]  # 获取当前断言的原始ID

        for consequent in consequents:
            target_var = consequent["variable"]
            target_cycle = consequent["relative_cycle"]
            coi = coi_builder.build_coi(target_var, max_cycle + 1)
            for antecedent in antecedents:
                antecedent_var = antecedent["variable"]
                antecedent_cycle = antecedent["relative_cycle"]
                coi_cycle = target_cycle - antecedent_cycle
                if coi_cycle >= 0:
                    importance, complexity = coi_builder.get_node_scores(antecedent_var, coi_cycle, coi)
                    total_importance += importance
                    total_complexity += complexity

        final_score = total_importance / total_complexity if total_complexity > 0 else 0.0
        module_results.append({
            "sva_string": assertion["sva_string"],
            "status": assertion["status"],
            "module": assertion["module"],
            "id": current_assert_id,  # 关键修复：使用当前断言的原始ID
            "importance_score": total_importance,
            "complexity_score": total_complexity,
            "final_score": final_score,
            "antecedents": antecedents,
            "consequents": consequents
        })

    # 排序并添加排名
    if module_results:
        module_results = sorted(module_results, key=lambda x: (-x["final_score"], x["id"]))
        for idx, item in enumerate(module_results, start=1):
            item["Rank"] = idx

    save_coi_cache(coi_builder.cois, coi_cache_path)
    return module_results

def main():
    parser = argparse.ArgumentParser(description='Calculate assertion scores (support original/new mode)')
    parser.add_argument('--mod', type=str, default='original', choices=['original', 'new'],
                        help='运行模式：original（原逻辑）/ new（新txt格式逻辑）')
    parser.add_argument('--module', type=str, default='i2c_master_top',
                        help='指定模块名（new模式下生效，默认：i2c_master_top）')
    parser.add_argument('input_path', help='输入文件路径：original模式为JSON，new模式为TXT')
    parser.add_argument('root_path', help='根路径')
    parser.add_argument('output_path', help='输出JSON文件路径')

    args = parser.parse_args()
    root_path = Path(args.root_path).resolve()

    # 加载断言数据
    if args.mod == "new":
        txt_path = Path(args.input_path).resolve()
        if not txt_path.exists():
            print(f"Error: 输入文件{txt_path}不存在")
            sys.exit(1)
        assertions_data = parse_new_assertions_txt(txt_path, args.module)
        print(f"Loaded new format assertions: {txt_path}, module={args.module}, total {sum(len(v) for v in assertions_data.values())} assertions")
    else:
        json_path = Path(args.input_path).resolve()
        if not json_path.exists():
            print(f"Error: 输入文件{json_path}不存在")
            sys.exit(1)
        with open(json_path, 'r') as f:
            assertions_data = json.load(f)
        print(f"Loaded original format assertions: {json_path}, {len(assertions_data)} modules found")

    # 处理所有模块
    final_results = defaultdict(list)
    for module_name, module_assertions in assertions_data.items():
        print(f"\nProcessing module: {module_name}")
        module_results = process_single_module(module_name, module_assertions, root_path, args.mod)
        final_results[module_name] = module_results

    # 保存结果
    output_path = Path(args.output_path).resolve()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(dict(final_results), f, indent=2, ensure_ascii=False)

    total_processed = sum(len(assertions) for assertions in final_results.values())
    print(f"\nGenerated assertion scores: {output_path}")
    print(f"Processed {total_processed} proven assertions across {len(final_results)} modules")

if __name__ == "__main__":
    main()