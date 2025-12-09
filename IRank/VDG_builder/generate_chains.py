import json  
import argparse  
from pathlib import Path  
from typing import Dict, List, Any, Set  
  
def generate_var_chains(json_file_path: str, define_chain_path: str, use_chain_path: str):  
    """Generate var_define_chain and var_use_chain from RTL analyzer JSON output."""  
      
    # Load JSON data  
    with open(json_file_path, 'r', encoding='utf-8') as f:  
        data = json.load(f)  
      
    analysis_results = data.get('analysisResults', {})  
      
    # Initialize output structures  
    var_define_chain = {}  
    var_use_chain = {}  
      
    # First pass: build define chains and initialize use chains  
    for var_name, var_info in analysis_results.items():  
        # Build define chain  
        define_chain = build_define_chain(var_name, var_info)  
        var_define_chain[var_name] = define_chain  
          
        # Initialize use chain structure  
        var_use_chain[var_name] = {  
            "DefVars": [],  
            "Lines": [],  
            "Sensitivities_Expressions": []  
        }  
      
    # Second pass: build use chains by analyzing assignments and paths  
    build_use_chains(analysis_results, var_use_chain)  
      
    # Save results  
    with open(define_chain_path, 'w', encoding='utf-8') as f:  
        json.dump(var_define_chain, f, indent=2, ensure_ascii=False)  
      
    with open(use_chain_path, 'w', encoding='utf-8') as f:  
        json.dump(var_use_chain, f, indent=2, ensure_ascii=False)  
      
    print(f"Generated var_define_chain: {define_chain_path}")  
    print(f"Generated var_use_chain: {use_chain_path}")  
  
def build_define_chain(var_name: str, var_info: Dict) -> Dict:  
    """Build define chain for a single variable."""  
      
    # Determine Clocked property - check if any assignment has clock sensitivity  
    is_clocked = False  
    assignments = var_info.get('assignments', [])  
      
    for assignment in assignments:  
        sensitivity_signals = assignment.get('sensitivitySignals', [])  
        for sig in sensitivity_signals:  
            sig_lower = sig.lower()  
            if 'clk' in sig_lower or 'clock' in sig_lower:  
                is_clocked = True  
                break  
        if is_clocked:  
            break  
      
    # Initialize arrays for each assignment  
    c_deps = []  
    c_lines = []  
    d_deps = []  
    d_lines = []  
    expressions = []  
      
    assignments = var_info.get('assignments', [])  
      
    for assignment in assignments:  
        # DDeps: driving signals for this assignment  
        driving_signals = assignment.get('drivingSignals', [])  
        d_deps.append(driving_signals)  
          
        # DLines: line number of this assignment  
        d_lines.append(assignment.get('line', 0))  
          
        # Expressions: detailed assignment info  
        expression_info = {  
            "drivingSignals": driving_signals,  
            "file": assignment.get('file', ''),  
            "line": assignment.get('line', 0),  
            "logicType": assignment.get('logicType', 'unknown')  
        }  
        expressions.append(expression_info)  
          
        # Process control flow (path)  
        path = assignment.get('path', [])  
        assignment_c_deps = []  
        assignment_c_lines = []  
          

        # TODO: 这里没有累加，如果后续有影响的话，需要累加一下
        for clause in path:  
            expr_info = clause.get('expr', {})  
            # Merge involvedSignals and involvedParameters  
            involved_signals = expr_info.get('involvedSignals', [])  
            involved_params = expr_info.get('involvedParameters', [])  
            all_involved = involved_signals + involved_params  
            assignment_c_deps.append(all_involved)  
              
            # Line number for this condition  
            assignment_c_lines.append(expr_info.get('line', 0))  
          
        c_deps.append(assignment_c_deps)  
        c_lines.append(assignment_c_lines)  
      
    return {  
        "Clocked": is_clocked,  
        "CDeps": c_deps,  
        "CLines": c_lines,  
        "DDeps": d_deps,  
        "DLines": d_lines,  
        "Expressions": expressions  
    }  
  
def build_use_chains(analysis_results: Dict, var_use_chain: Dict):  
    """Build use chains by analyzing how variables are used in assignments and conditions."""  
      
    for var_name, var_info in analysis_results.items():  
        assignments = var_info.get('assignments', [])  
          
        for assignment in assignments:  
            # Variables that this assignment defines (the LHS variable)  
            defined_var = var_name  
            line = assignment.get('line', 0)  
              
            # Expression info for this assignment  
            expr_info = {  
                "file": assignment.get('file', ''),  
                "line": line,  
                "logicType": assignment.get('logicType', 'unknown')  
            }  
              
            # For each driving signal, add this assignment to its use chain  
            driving_signals = assignment.get('drivingSignals', [])  
            for driving_signal in driving_signals:  
                if driving_signal in var_use_chain:  
                    var_use_chain[driving_signal]["DefVars"].append(defined_var)  
                    var_use_chain[driving_signal]["Lines"].append(line)  
                    var_use_chain[driving_signal]["Sensitivities_Expressions"].append(expr_info)  
              
            # Process control flow conditions  
            path = assignment.get('path', [])  
            for clause in path:  
                expr_data = clause.get('expr', {})  
                clause_line = expr_data.get('line', 0)  
                clause_file = expr_data.get('file', '')  
                  
                # For signals involved in conditions  
                involved_signals = expr_data.get('involvedSignals', [])  
                involved_params = expr_data.get('involvedParameters', [])  
                all_involved = involved_signals + involved_params  
                  
                clause_expr_info = {  
                    "file": clause_file,  
                    "line": clause_line,  
                    "logicType": "condition"  # Special marker for conditions  
                }  
                  
                for involved_signal in all_involved:  
                    if involved_signal in var_use_chain:  
                        # For conditions, DefVars is empty (as specified)  
                        var_use_chain[involved_signal]["DefVars"].append("")  
                        var_use_chain[involved_signal]["Lines"].append(clause_line)  
                        var_use_chain[involved_signal]["Sensitivities_Expressions"].append(clause_expr_info)  
  
def main():  
    parser = argparse.ArgumentParser(description='Generate var_define_chain and var_use_chain from RTL analyzer JSON')  
    parser.add_argument('json_file', help='Input JSON file path from rtl_analyzer')  
    parser.add_argument('define_chain_file', help='Output file path for var_define_chain')  
    parser.add_argument('use_chain_file', help='Output file path for var_use_chain')  
      
    args = parser.parse_args()  
      
    generate_var_chains(args.json_file, args.define_chain_file, args.use_chain_file)  
  
if __name__ == "__main__":  
    main()