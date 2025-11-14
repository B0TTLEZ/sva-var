import json
from pathlib import Path
import networkx as nx
import argparse
import csv
from collections import defaultdict
import math
import os
import openai
import pandas as pd
import time

# ============================================================================
# Section 1: 原始关键变量评分
# ============================================================================

def load_analysis_results(json_path: str) -> dict:
    """从C++分析器生成的JSON文件中加载分析结果。"""
    try:
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        print(f"[INFO] Successfully loaded analysis results from: {json_path}")
        return data.get('analysisResults', {})
    except FileNotFoundError:
        print(f"[ERROR] Input JSON file not found at: {json_path}")
        exit(1)
    except json.JSONDecodeError as e:
        print(f"[ERROR] Failed to parse JSON file. It might be corrupted: {json_path}. Details: {e}")
        exit(1)

def build_graph_from_results(analysis_results: dict):
    """根据分析结果构建一个带类型的有向图。"""
    G = nx.DiGraph()
    pis, pos = set(), set()
    for var_name, var_info in analysis_results.items():
        G.add_node(var_name)
        direction = var_info.get('direction', 'unknown')
        if direction in ('input', 'inout'):
            pis.add(var_name)
        if direction in ('output', 'inout'):
            pos.add(var_name)
        for assignment in var_info.get('assignments', []):
            etype = 'seq' if assignment.get('logicType') == 'sequential' else 'comb'
            for src_node in assignment.get('drivingSignals', []):
                if src_node not in G:
                    G.add_node(src_node)
                G.add_edge(src_node, var_name, etype=etype)
    print(f"[INFO] Graph built: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges.")
    return G, pis, pos

def scc_condensation_with_weights(G):
    """将原图凝缩为SCC DAG，并为跨SCC的边赋权。"""
    sccs = list(nx.strongly_connected_components(G))
    id_of = {n: i for i, comp in enumerate(sccs) for n in comp}
    members = {i: set(comp) for i, comp in enumerate(sccs)}
    CDAG = nx.DiGraph()
    CDAG.add_nodes_from(range(len(sccs)))
    for u, v, d in G.edges(data=True):
        cu, cv = id_of.get(u, -1), id_of.get(v, -1)
        if cu == -1 or cv == -1 or cu == cv:
            continue
        w = 1 if d.get("etype") == "seq" else 0
        if not CDAG.has_edge(cu, cv) or w < CDAG[cu][cv].get("w", 1):
            CDAG.add_edge(cu, cv, w=w)
    return CDAG, id_of, members

def dp_on_cdag(CDAG, id_of, members, PIs, POs):
    """在SCC DAG上做DP，计算时序指标。"""
    INF = float('inf')
    N = CDAG.number_of_nodes()
    distPI, distPO, po_mask = [INF] * N, [INF] * N, [0] * N
    po_list = sorted(list(POs))
    po_idx = {p: i for i, p in enumerate(po_list)}
    
    for cid, comp in members.items():
        if any(n in PIs for n in comp):
            distPI[cid] = 0
        mask = sum(1 << po_idx[n] for n in comp if n in po_idx)
        if mask > 0:
            distPO[cid] = 0
            po_mask[cid] = mask
            
    try:
        topo_order = list(nx.topological_sort(CDAG))
    except nx.NetworkXUnfeasible:
        print("[WARNING] Condensation graph has a cycle. Skipping DP.")
        return {}, {}, {}
        
    for u in topo_order:
        if distPI[u] == INF:
            continue
        for v in CDAG.successors(u):
            distPI[v] = min(distPI[v], distPI[u] + CDAG[u][v].get('w', 0))
            
    for u in reversed(topo_order):
        for v in CDAG.successors(u):
            po_mask[u] |= po_mask[v]
            distPO[u] = min(distPO[u], distPO[v] + CDAG[u][v].get('w', 0))
            
    distPI_node = {n: distPI[cid] for n, cid in id_of.items()}
    distPO_node = {n: distPO[cid] for n, cid in id_of.items()}
    reachPO_cnt = {n: bin(po_mask[cid]).count("1") for n, cid in id_of.items()}
    return distPI_node, distPO_node, reachPO_cnt

def normalize(d: dict) -> dict:
    """对字典的值进行最大最小值归一化。"""
    vals = [v for v in d.values() if v is not None and not math.isinf(v)]
    if not vals:
        return {k: 0.0 for k in d}
    min_v, max_v = min(vals), max(vals)
    if max_v == min_v:
        return {k: 1.0 for k in d}
    return {k: (v - min_v) / (max_v - min_v) if v is not None and not math.isinf(v) else 0.0 for k, v in d.items()}

def invert_norm(d: dict) -> dict:
    """对距离类指标进行归一化 (值越小，分数越高)。"""
    nd = normalize(d)
    return {k: 1.0 - v for k, v in nd.items()}

def calculate_initial_scores(analysis_results: dict, G: nx.DiGraph, pis: set, pos: set, weights: dict):
    """计算所有变量的初始关键性得分。"""
    metrics = defaultdict(dict)
    for name, info in analysis_results.items():
        metrics[name]['fan_out'] = len(info.get('fanOut', []))
        metrics[name]['is_control'] = 1.0 if info.get('isControlVariable') else 0.0
        metrics[name]['logic_depth'] = max((a.get('conditionDepth', 0) for a in info.get('assignments', [])), default=0)
    
    CDAG, id_of, members = scc_condensation_with_weights(G)
    distPI, distPO, reachPO = dp_on_cdag(CDAG, id_of, members, pis, pos)
    for name in analysis_results:
        metrics[name]['dist_pi_cycles'] = distPI.get(name, float('inf'))
        metrics[name]['dist_po_cycles'] = distPO.get(name, float('inf'))
        metrics[name]['reachable_pos'] = reachPO.get(name, 0)

    def get_metric_dict(name):
        return {var: metrics[var].get(name, 0) for var in analysis_results}

    n_fan_out = normalize(get_metric_dict('fan_out'))
    n_is_control = get_metric_dict('is_control')
    n_logic_depth = normalize(get_metric_dict('logic_depth'))
    n_dist_pi = invert_norm(get_metric_dict('dist_pi_cycles'))
    n_dist_po = invert_norm(get_metric_dict('dist_po_cycles'))
    n_reach_po = normalize(get_metric_dict('reachable_pos'))

    scores = []
    for var in analysis_results:
        score = (weights['fan_out'] * n_fan_out.get(var, 0) +
                 weights['is_control'] * n_is_control.get(var, 0) +
                 weights['logic_depth'] * n_logic_depth.get(var, 0) +
                 weights['dist_pi'] * n_dist_pi.get(var, 0) +
                 weights['dist_po'] * n_dist_po.get(var, 0) +
                 weights['reach_po'] * n_reach_po.get(var, 0))
        row = {'variable': var, 'score': score}
        row.update(metrics[var])
        scores.append(row)
    
    return sorted(scores, key=lambda x: x['score'], reverse=True)

# ============================================================================
# Section 2: LLM-based Property Extraction
# ============================================================================

def load_prompt_template(file_path: str) -> str:
    """从文件加载提示词模板。"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    except FileNotFoundError:
        print(f"[ERROR] Prompt template file not found: {file_path}")
        exit(1)

def gather_context_for_var(var_name: str, analysis_results: dict, max_neighbors: int = 5):
    """为目标变量提取其自身和邻居的JSON信息。"""
    context = {
        var_name: analysis_results.get(var_name, {})
    }
    target_info = context[var_name]

    driving_signals = set()
    for assign in target_info.get("assignments", []):
        driving_signals.update(assign.get("drivingSignals", []))
    for i, sig in enumerate(list(driving_signals)):
        if i >= max_neighbors:
            break
        context[sig] = analysis_results.get(sig, {"comment": "Driver signal info"})

    for i, sig in enumerate(target_info.get("fanOut", [])):
        if i >= max_neighbors:
            break
        context[sig] = analysis_results.get(sig, {"comment": "Load signal info"})
        
    return context

def query_llm(prompt: str, client: openai.OpenAI):
    """调用LLM API并返回结果，包含重试机制。"""
    for attempt in range(3):
        try:
            response = client.chat.completions.create(
                model="deepseek-chat",
                messages=[{"role": "user", "content": prompt}],
                response_format={"type": "json_object"},
                temperature=0.1,
                seed=42
            )
            return json.loads(response.choices[0].message.content)
        except Exception as e:
            print(f"[WARNING] LLM API call failed (attempt {attempt+1}/3): {e}")
            time.sleep(5)
    return None

def analyze_properties_with_llm(top_k_vars: list, analysis_results: dict, client: openai.OpenAI, prompt_template: str):
    """对Top-K变量进行LLM属性分析。"""
    extracted_properties = {}
    for i, var_name in enumerate(top_k_vars):
        print(f"\n[INFO] Analyzing properties for var {i+1}/{len(top_k_vars)}: {var_name}")
        context = gather_context_for_var(var_name, analysis_results)
        context_json_str = json.dumps(context, indent=2)

        prompt = prompt_template.format(var_name=var_name, context_json=context_json_str)
        result = query_llm(prompt, client)
        
        if result and result.get("identified_property") != "Other":
            print(f"  -> Identified as {result.get('identified_property')} with confidence {result.get('confidence_score')}")
            extracted_properties[var_name] = result
            
    return extracted_properties

# ============================================================================
# Section 3: 主函数与报告生成
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="Identify key variables and their properties from RTL static analysis.")
    parser.add_argument("-i", "--input", required=True, help="Path to the input JSON file from C++ analyzer.")
    parser.add_argument("-o", "--output", default="key_variables_report.csv", help="Path to the final output CSV report.")
    parser.add_argument("--top_k", type=int, default=3, help="Number of top variables to analyze with LLM for properties.")
    parser.add_argument("--prompt", default="/data/fhj/sva-var/rtl_analyzer/ranker/prompts/prop_extraction.txt", help="Path to the general property prompt template file.")
    args = parser.parse_args()

    # if "OPENAI_API_KEY" not in os.environ:
    #     print("[ERROR] OPENAI_API_KEY environment variable not set. Please set it before running.")
    #     exit(1)
    client = openai.OpenAI(api_key="sk-56457d9e10e7481495c76899b1a28392",base_url="https://api.deepseek.com/v1")

    print("--- Stage 1: Calculating Initial Criticality Scores ---")
    weights = {
        "fan_out": 0.15, "is_control": 0.25, "logic_depth": 0.10,
        "dist_pi": 0.15, "dist_po": 0.15, "reach_po": 0.20
    }
    analysis_results = load_analysis_results(args.input)
    if not analysis_results:
        return
    
    G, pis, pos = build_graph_from_results(analysis_results)
    initial_scores = calculate_initial_scores(analysis_results, G, pis, pos, weights)
    
    print(f"\n--- Stage 2: Extracting Properties for Top-{args.top_k} Variables using LLM ---")
    prompt_template = load_prompt_template(args.prompt)
    top_k_vars = [row['variable'] for row in initial_scores[:args.top_k]]
    llm_properties = analyze_properties_with_llm(top_k_vars, analysis_results, client, prompt_template)

    print("\n--- Stage 3: Generating High-Level Inference Report ---")
    # 将DataFrame转换为更适合报告的格式
    scores_dict = {row['variable']: row for row in initial_scores}
    args.output=Path(args.input).stem+"_key_prop.md"
    try:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write("# RTL Design High-Level Inference Report\n\n")
            f.write("This report contains AI-generated inferences about the design's architecture and verification challenges, "
                    "deduced from the properties of its most critical signals.\n\n")
            
            for var_name, inferences in llm_properties.items():
                score_info = scores_dict.get(var_name, {})
                f.write(f"## Analysis based on Critical Signal: `{var_name}`\n\n")
                f.write(f"**Criticality Score:** `{score_info.get('score', 'N/A'):.3f}`\n\n")
                
                f.write("### Inferred Module Function\n")
                f.write(f"> {inferences.get('inferred_module_function', 'N/A')}\n\n")
                
                f.write("### Key Architectural Pattern Revealed\n")
                f.write(f"> {inferences.get('key_architectural_pattern_revealed', 'N/A')}\n\n")

                f.write("### Primary Verification Challenge\n")
                f.write(f"> **{inferences.get('primary_verification_challenge', 'N/A')}**\n\n")
                
                f.write("---\n\n")
        
        print(f"[SUCCESS] High-level inference report saved to: {args.output}")
    except IOError:
        print(f"[ERROR] Could not write to output file: {args.output}")

    
    # try:
    #     report_df.to_csv(args.output, index=False)
    #     print(f"\n[SUCCESS] Final report saved to: {args.output}")
    # except IOError:
    #     print(f"[ERROR] Could not write to output file: {args.output}")

if __name__ == "__main__":
    main()