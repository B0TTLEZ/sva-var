import json  
import argparse  
import re  
from pathlib import Path  
from typing import Dict, List, Any, Set, Tuple  
from collections import defaultdict  
  
def extract_vars_from_expr(expr):  
    """从表达式中提取变量名，处理Verilog常量、数组索引、关键字等"""  
    # 移除Verilog风格常量  
    verilog_const_pattern = re.compile(r'\d+\'[bdho][0-9a-fA-F]+', re.IGNORECASE)  
    expr = verilog_const_pattern.sub(' ', expr)  
      
    # 去掉数组索引  
    expr = re.sub(r'\[.*?\]', '', expr)  
      
    # 匹配变量名  
    var_pattern = re.compile(r'\b([A-Za-z_][A-Za-z0-9_]*)\b')  
    forbidden_words = {  
        'posedge', 'negedge', 'disable', 'iff', 'assert', 'property', 'return',  
        'if', 'else', 'case', 'rose', 'fell', 'past', 'true', 'false', 'null', 'default',  
        'stable'  # 新增：覆盖$stable拆解后的关键词  
    }  
      
    vars = []  
    for match in var_pattern.finditer(expr):  
        var = match.group(1)  
        if (var not in forbidden_words and  
            not var.startswith('$') and  
            not var[0].isdigit()):  
            vars.append(var)  
    return vars  
  
def clean_and_split_sva(sva_string):  
    """精确地将SVA字符串分割为前件和后件"""  
    match_core = re.search(r'assert\s+property\s*\((.*)\)\s*;', sva_string, re.DOTALL | re.IGNORECASE)  
    if not match_core:  
        raise ValueError("无法识别断言的结构")  
      
    clean_sva = match_core.group(1).strip()  
      
    # 移除时钟和disable iff  
    header_pattern = re.compile(r'@\(.*?\)(\s*disable\s+iff\(.*?\))?\s*', re.DOTALL | re.IGNORECASE)  
    match_head = header_pattern.match(clean_sva)  
    header_end_index = match_head.end() if match_head else 0  
    core_sequence = clean_sva[header_end_index:].strip()  
      
    # 找到蕴含符  
    implication_pos = -1  
    implication_op = None  
    bracket_depth = 0  
    i = 0  
    while i < len(core_sequence):  
        char = core_sequence[i]  
        if char == '(':  
            bracket_depth += 1  
        elif char == ')':  
            bracket_depth -= 1  
        elif bracket_depth == 0:  
            if core_sequence.startswith('|->', i):  
                implication_pos = i  
                implication_op = '|->'  
                break  
            elif core_sequence.startswith('|=>', i):  
                implication_pos = i  
                implication_op = '|=>'  
                break  
        i += 1  
      
    if implication_pos == -1:  
        raise ValueError("未找到顶层蕴含符")  
      
    antecedent_part = core_sequence[:implication_pos].strip()  
    consequent_part = core_sequence[implication_pos + len(implication_op):].strip()  
      
    antecedent_part = re.sub(r'^\s*\(|\)\s*$', '', antecedent_part).strip()  
    consequent_part = re.sub(r'^\s*\(|\)\s*$', '', consequent_part).strip()  
      
    is_delayed_implication = (implication_op == '|=>')  
    # Fixed: Return the actual variables that were defined  
    return antecedent_part, consequent_part, is_delayed_implication
  
def extract_variables(expression, current_cycle):  
    """从条件表达式中提取变量名和相对时钟周期"""  
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
      
    # 处理$past ：核心修复点，明确周期计算逻辑   
    past_pattern = re.compile(r'\$past\s*\((.*?)\)', re.DOTALL | re.IGNORECASE)  
    for match in past_pattern.finditer(expression):  
        past_content = match.group(1).strip()  
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
        past_delay = int(past_parts[1]) if len(past_parts) >= 2 else 1  
        # 关键修复：$past变量的周期 = 当前表达式周期 - past_delay  
        # 示例：后件周期1，past_delay=1 → rst_p的周期=1-1=0  
        past_var_cycle = current_cycle - past_delay  
        add_vars_from_expr(signal_expr, past_var_cycle)  
          
        # 替换$past表达式为空格，避免后续重复解析  
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]  
      
    # 处理$rose/$fell  
    rise_fall_pattern = re.compile(r'\$(rose|fell)\s*\((.*?)\)', re.DOTALL | re.IGNORECASE)  
    for match in rise_fall_pattern.finditer(expression):  
        signal_expr = match.group(2).strip()  
        add_vars_from_expr(signal_expr, current_cycle)  
        expression = expression[:match.start()] + ' ' * (match.end() - match.start()) + expression[match.end():]  
      
    # 处理通用信号  
    add_vars_from_expr(expression, current_cycle)  
    return variables  
  
def parse_sva_sequence(antecedent_str, consequent_str, is_delayed):  
    """解析前件和后件，计算所有信号的相对周期"""  
    sequence_parts = re.split(r'(##\d+)', antecedent_str)  
    relative_cycle = 0  
    antecedent_assertions = []  
      
    for part in sequence_parts:  
        part = part.strip()  
        if not part:  
            continue  
        if part.startswith('##'):  
            delay = int(part.lstrip('##'))  
            relative_cycle += delay  
            continue  
          
        part = part.replace('&&', '&')  
        propositions = re.split(r'(?<!\^)&(?!\^)', part)  
        for prop in propositions:  
            prop = prop.strip(' ()')  
            if prop:  
                variables = extract_variables(prop, relative_cycle)  
                antecedent_assertions.extend(variables)  
      
    # ---------------------- 后件解析（修复点2：新增##延迟处理） ----------------------
    consequent_assertions = []  
    consequent_cycle = relative_cycle + (1 if is_delayed else 0)  
    # 修复点2.1：解析后件中的##延迟（如##1），累加周期  
    consequent_parts = re.split(r'(##\d+)', consequent_str)  
    current_consequent_cycle = consequent_cycle  # 后件基础周期
    for part in consequent_parts:  
        part = part.strip()  
        if not part:  
            continue  
        if part.startswith('##'):  
            delay = int(part.lstrip('##'))  
            current_consequent_cycle += delay  # 累加后件内的延迟
            continue  

        part = part.replace('&&', '&')  
        propositions = re.split(r'(?<!\^)&(?!\^)', part)  
        for prop in propositions:  
            prop = prop.strip(' ()')  
            if prop:  
                variables = extract_variables(prop, current_consequent_cycle)  
                consequent_assertions.extend(variables)  
      
    return {  
        "antecedent": [  
            {"variable": var, "relative_cycle": cycle}  
            for var, cycle in sorted(antecedent_assertions, key=lambda x: (x[1], x[0]))  
        ],  
        "consequent": [  
            {"variable": var, "relative_cycle": cycle}  
            for var, cycle in sorted(consequent_assertions, key=lambda x: (x[1], x[0]))  
        ]  
    }  
  
class COIBuilder:  
    def __init__(self, var_define_chain: Dict, var_use_chain: Dict, pagerank: Dict, weight_map: Dict):  
        self.var_define_chain = var_define_chain  
        self.var_use_chain = var_use_chain  
        self.pagerank = pagerank  
        self.weight_map = weight_map  
        self.cois = {}  # Cache for built COIs  
      
    # Update the initial call in build_coi  
    def build_coi(self, target_var: str, max_cycles: int) -> Dict:  
        """构建Cone of Influence with correct relative importance and complexity"""  
        cache_key = (target_var, max_cycles)  
        if cache_key in self.cois:  
            return self.cois[cache_key]  
          
        coi = {  
            "nodes": {},  # {(var, cycle): {"importance": float, "complexity": float}}  
            "target": target_var  
        }  
          
        # Initialize target node at cycle 0  
        target_importance = self.pagerank.get(target_var, 0.0)  
        target_complexity = self.calculate_complexity(target_var)  
        coi["nodes"][(target_var, 0)] = {  
            "importance": target_importance,  
            "complexity": target_complexity  
        }  
          
        # Build COI recursively with relative values  
        self._expand_coi(target_var, 0, max_cycles, coi, target_importance, target_complexity)  
          
        self.cois[cache_key] = coi  
        return coi 
      
    def _expand_coi(self, var: str, cycle: int, max_cycles: int, coi: Dict,   
                    parent_importance: float, parent_complexity: float):  
        """递归扩展COI，计算相对重要性和相对复杂度"""  
        if cycle >= max_cycles:  
            return  
          
        # Get dependencies from var_define_chain  
        var_info = self.var_define_chain.get(var, {})  
          
        # Process CDeps (control dependencies)  
        c_deps = var_info.get('CDeps', [])  
        for assignment_c_deps in c_deps:  
            for control_dep_list in assignment_c_deps:  
                for dep_var in control_dep_list:  
                    if dep_var:  
                        # Check if Clocked for cycle adjustment  
                        var_info = self.var_define_chain.get(var, {})  
                        is_clocked = var_info.get('Clocked', False)  
                        new_cycle = cycle + (1 if is_clocked else 0)  
                          
                        if new_cycle <= max_cycles:  
                            node_key = (dep_var, new_cycle)  
                            if node_key not in coi["nodes"]:  
                                # Calculate relative importance  
                                edge_weight = self._get_edge_weight(dep_var, var)  
                                relative_importance = self.pagerank.get(dep_var, 0.0) + edge_weight * parent_importance  
                                  
                                # Calculate relative complexity  
                                intersection_count = self._calculate_expression_intersection(var, dep_var)  
                                relative_complexity = intersection_count + parent_complexity  
                                  
                                coi["nodes"][node_key] = {  
                                    "importance": relative_importance,  
                                    "complexity": relative_complexity  
                                }  
                                # Recursively expand with new relative values  
                                self._expand_coi(dep_var, new_cycle, max_cycles, coi,   
                                               relative_importance, relative_complexity)  
          
        # Process DDeps (data dependencies)  
        d_deps = var_info.get('DDeps', [])  
        for i, dep_list in enumerate(d_deps):  
            expressions = var_info.get('Expressions', [])  
            logic_type = expressions[i].get('logicType', 'unknown') if i < len(expressions) else 'unknown'  
              
            for dep_var in dep_list:  
                if dep_var:  
                    # Check logicType for cycle adjustment  
                    new_cycle = cycle + (1 if logic_type == 'sequential' else 0)  
                      
                    if new_cycle <= max_cycles:  
                        node_key = (dep_var, new_cycle)  
                        if node_key not in coi["nodes"]:  
                            # Calculate relative importance  
                            edge_weight = self._get_edge_weight(dep_var, var)  
                            relative_importance = self.pagerank.get(dep_var, 0.0) + edge_weight * parent_importance  
                              
                            # Calculate relative complexity  
                            intersection_count = self._calculate_expression_intersection(var, dep_var)  
                            relative_complexity = intersection_count + parent_complexity  
                              
                            coi["nodes"][node_key] = {  
                                "importance": relative_importance,  
                                "complexity": relative_complexity  
                            }  
                            # Recursively expand with new relative values  
                            self._expand_coi(dep_var, new_cycle, max_cycles, coi,   
                                           relative_importance, relative_complexity)  
      
    def _get_edge_weight(self, src_var: str, dst_var: str) -> int:  
        """获取两个变量之间的边权重"""  
        return self.weight_map.get(src_var, {}).get(dst_var, 0)  

    def _calculate_expression_intersection(self, var: str, dep_var: str) -> int:  
        """
        计算var的表达式与dep_var的敏感表达式的交集元素个数之和
        新逻辑：
        1. 以(driving_signals_list, line)为核心key（不再用file+line）
        2. 构建var的total_expressions（DDeps+DLines + CDeps+CLines）
        3. 构建dep_var的sensitive_expressions（Sensitivities_Expressions的line+drivingSignals）
        4. 求交集后计算所有交集元素中list的元素个数之和（去重但保留list内部元素）
        """  
        # ===================== 步骤1：构建var的data_expressions（DDeps + DLines） =====================
        var_info = self.var_define_chain.get(var, {})  
        data_expressions = []  # 存储(ddep_list_tuple, line)

        # DDeps和DLines是一一对应的列表，遍历每个元素
        ddeps = var_info.get('DDeps', [])  # 例如: [[key], [key], [key]]
        dlines = var_info.get('DLines', [])  # 例如: [15, 11, 7]
        for ddep_list, dline in zip(ddeps, dlines):
            # 列表转元组（可哈希，用于集合去重）
            ddep_tuple = tuple(ddep_list)
            data_expressions.append((ddep_tuple, dline))

        # ===================== 步骤2：构建var的control_expressions（CDeps + CLines） =====================
        control_expressions = []  # 存储(cdep_list_tuple, line)

        # CDeps和CLines嵌套更深：外层是assignment，内层是clause
        cdeps = var_info.get('CDeps', [])  # 例如: [[[count], [count,nrq1,nrq2], [count,nrq3]], [...], [...]]
        clines = var_info.get('CLines', [])  # 例如: [[5,9,13], [5,9], [5]]
        for assignment_cdeps, assignment_clines in zip(cdeps, clines):
            # 遍历每个assignment下的clause（CDeps和CLines的内层列表）
            for cdep_list, cline in zip(assignment_cdeps, assignment_clines):
                cdep_tuple = tuple(cdep_list)
                control_expressions.append((cdep_tuple, cline))

        # ===================== 步骤3：构建var的total_expressions并去重 =====================
        total_expressions = data_expressions + control_expressions
        # 转集合去重（同一个(dep_list, line)只保留一次）
        var_expressions_set = set(total_expressions)

        # ===================== 步骤4：构建dep_var的sensitive_expressions =====================
        dep_use_info = self.var_use_chain.get(dep_var, {})
        sensitive_expressions = []  # 存储(driving_signals_tuple, line)

        # 遍历dep_var的Sensitivities_Expressions
        sens_expr_list = dep_use_info.get('Sensitivities_Expressions', [])
        for sens_expr in sens_expr_list:
            line = sens_expr.get('line', 0)
            driving_signals = sens_expr.get('drivingSignals', [])
            # 列表转元组（可哈希）
            driving_tuple = tuple(driving_signals)
            sensitive_expressions.append((driving_tuple, line))

        # 转集合去重
        dep_sensitive_set = set(sensitive_expressions)

        # ===================== 步骤5：求交集并计算元素个数之和 =====================
        # 求两个集合的交集
        intersection = var_expressions_set & dep_sensitive_set

        # 计算交集元素中每个tuple（driving_list）的元素个数之和
        total_count = 0
        for expr_tuple, _ in intersection:
            total_count += len(expr_tuple)

        return total_count


    def calculate_complexity(self, var: str) -> float:  
        """计算变量复杂度 - 基于表达式交集"""  
        var_info = self.var_define_chain.get(var, {})  
        use_info = self.var_use_chain.get(var, {})  
          
        # Get expressions from define chain  
        expressions = var_info.get('Expressions', [])  
        expr_map = {}  # {(file, line): expression}  
        for expr in expressions:  
            key = (expr.get('file', ''), expr.get('line', 0))  
            expr_map[key] = expr  
          
        # Get sensitivities from use chain  
        sensitivities = use_info.get('Sensitivities_Expressions', [])  
        sens_map = {}  # {(file, line): sensitivity}  
        for sens in sensitivities:  
            key = (sens.get('file', ''), sens.get('line', 0))  
            sens_map[key] = sens  
          
        # Find intersection based on file and line  
        common_keys = set(expr_map.keys()) & set(sens_map.keys())  
          
        # Count drivingSignals from matching expressions  
        complexity = 0.0  
        for key in common_keys:  
            expr = expr_map[key]  
            driving_signals = expr.get('drivingSignals', [])  
            complexity += len(driving_signals)  
          
        return float(complexity)  
      
    def get_node_scores(self, var: str, cycle: int, coi: Dict) -> Tuple[float, float]:  
        """获取特定节点的Importance和Complexity分数"""  
        node_key = (var, cycle)  
        if node_key in coi["nodes"]:  
            node = coi["nodes"][node_key]  
            return node["importance"], node["complexity"]  
        return 0.0, 0.0  
  
def calculate_assertion_scores(assertions_json: str, var_define_chain_path: str,   
                               var_use_chain_path: str, pagerank_path: str,  
                               weight_map_path: str, output_path: str, coi_cache_path: str = None): 
    """计算断言分数"""  
    # Load input files  
    with open(assertions_json, 'r') as f:  
        assertions_data = json.load(f)  
      
    with open(var_define_chain_path, 'r') as f:  
        var_define_chain = json.load(f)  
      
    with open(var_use_chain_path, 'r') as f:  
        var_use_chain = json.load(f)  
      
    with open(pagerank_path, 'r') as f:  
        pagerank = json.load(f)  
      
    with open(weight_map_path, 'r') as f:  
        weight_map = json.load(f)  
      
    # Initialize COI builder with weight_map  
    coi_builder = COIBuilder(var_define_chain, var_use_chain, pagerank, weight_map)  
      
    # Find maximum cycle across all assertions  
    max_cycle = 0  
    parsed_assertions = []  
      
    # Iterate through all modules (not just the first one)  
    for module_name in assertions_data.keys():  
        for assertion in assertions_data[module_name]:  
            if assertion.get("status") == "proven":  
                try:  
                    sva_string = assertion["sva_string"]  
                    antecedent_str, consequent_str, is_delayed = clean_and_split_sva(sva_string)  
                    parsed = parse_sva_sequence(antecedent_str, consequent_str, is_delayed)  
                      
                    # Prefix variables with module name  
                    for item in parsed["antecedent"]:  
                        item["variable"] = f"{module_name}.{item['variable']}"  
                    for item in parsed["consequent"]:  
                        item["variable"] = f"{module_name}.{item['variable']}"  
                      
                    # Update max cycle  
                    for item in parsed["antecedent"] + parsed["consequent"]:  
                        max_cycle = max(max_cycle, item["relative_cycle"])  
                      
                    parsed_assertions.append({  
                        "sva_string": sva_string,  
                        "status": "proven",  
                        "module": module_name,  
                        **parsed  
                    })  
                except Exception as e:  
                    print(f"Error parsing assertion: {e}")  
      
    # Calculate scores for each assertion  
    # 修改点1：改用按模块分组的字典存储结果，保留模块层级  
    results = defaultdict(list)
    for assertion in parsed_assertions:  
        antecedents = assertion["antecedent"]  
        consequents = assertion["consequent"]  
          
        total_importance = 0.0  
        total_complexity = 0.0  
          
        # For each consequent, calculate scores  
        for consequent in consequents:  
            target_var = consequent["variable"]  
            target_cycle = consequent["relative_cycle"]  
              
            # Build COI for this consequent  
            coi = coi_builder.build_coi(target_var, max_cycle + 1)  
              
            # Calculate scores for each antecedent relative to this consequent  
            for antecedent in antecedents:  
                antecedent_var = antecedent["variable"]  
                antecedent_cycle = antecedent["relative_cycle"]  
                  
                # Calculate backward cycles for COI (fixed timing logic)  
                # If antecedent is at cycle 0 and consequent at cycle 2,  
                # then antecedent is 2 cycles before consequent  
                coi_cycle = target_cycle - antecedent_cycle  
                if coi_cycle >= 0:  
                    importance, complexity = coi_builder.get_node_scores(  
                        antecedent_var, coi_cycle, coi  
                    )  
                    total_importance += importance  
                    total_complexity += complexity  
          
        # Calculate final score  
        final_score = total_importance / total_complexity if total_complexity > 0 else 0.0  
          
        # 修改点2：按模块分组存储断言结果  
        results[assertion["module"]].append({  
            "sva_string": assertion["sva_string"],  
            "status": assertion["status"],  
            "module": assertion.get("module", ""),  
            "importance_score": total_importance,  
            "complexity_score": total_complexity,  
            "final_score": final_score,  
            "antecedents": antecedents,  
            "consequents": consequents  
        })  
      
    # 修改点3：对每个模块的断言按final_score降序排序，并添加Rank属性（从1开始）  
    for module_name in results:  
        # 按final_score降序排序，分数相同则保持原顺序  
        sorted_assertions = sorted(results[module_name], key=lambda x: x["final_score"], reverse=True)  
        # 为每个断言添加Rank属性  
        for idx, assert_item in enumerate(sorted_assertions, start=1):  
            assert_item["Rank"] = idx  
        # 更新该模块的断言列表为排序后的结果  
        results[module_name] = sorted_assertions

    # Save COI cache if requested  
    if coi_cache_path:  
        save_coi_cache(coi_builder.cois, coi_cache_path)

    # 修改点4：将defaultdict转为普通dict，保证输出JSON结构与输入一致（模块为key）  
    with open(output_path, 'w') as f:  
        json.dump(dict(results), f, indent=2) 
      
    # 修改点5：更新打印信息，按模块统计数量  
    total_processed = sum(len(assertions) for assertions in results.values())  
    print(f"Generated assertion scores: {output_path}")  
    print(f"Processed {total_processed} proven assertions across {len(results)} modules")
  

def save_coi_cache(cois: Dict, coi_cache_path: str):  
    """Save COI cache to JSON file with stringified keys"""  
    def convert_tuple_keys(obj):  
        """Recursively convert tuple keys to strings"""  
        if isinstance(obj, dict):  
            new_dict = {}  
            for key, value in obj.items():  
                # Convert tuple keys to strings  
                if isinstance(key, tuple):  
                    new_key = f"({key[0]},{key[1]})"  
                else:  
                    new_key = key  
                  
                # Recursively process nested structures  
                new_dict[new_key] = convert_tuple_keys(value)  
            return new_dict  
        elif isinstance(obj, list):  
            return [convert_tuple_keys(item) for item in obj]  
        else:  
            return obj  
      
    # Convert all tuple keys recursively  
    serializable_cois = convert_tuple_keys(cois)  
      
    with open(coi_cache_path, 'w') as f:  
        json.dump(serializable_cois, f, indent=2)  
      
    print(f"Generated COI cache: {coi_cache_path}")  
    print(f"Saved {len(cois)} COI structures") 

def main():  
    parser = argparse.ArgumentParser(description='Calculate assertion scores using COI analysis')  
    parser.add_argument('assertions_json', help='Input assertions JSON file')  
    parser.add_argument('var_define_chain', help='var_define_chain.json file')  
    parser.add_argument('var_use_chain', help='var_use_chain.json file')  
    parser.add_argument('pagerank', help='complete_PageRank.json file')  
    parser.add_argument('weight_map', help='weight_map.json file')  
    parser.add_argument('output', help='Output assertion scores JSON file')  
    parser.add_argument('--coi-cache', help='Optional: Output COI cache JSON file')  
      
    args = parser.parse_args()  
      
    calculate_assertion_scores(  
        args.assertions_json,  
        args.var_define_chain,  
        args.var_use_chain,  
        args.pagerank,  
        args.weight_map,  
        args.output,  
        args.coi_cache  
    )
  
if __name__ == "__main__":  
    main()