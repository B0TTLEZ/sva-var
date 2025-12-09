import json  
import argparse  
from pathlib import Path  
import networkx as nx  
from collections import defaultdict, Counter  
  
def generate_weight_and_pagerank(define_chain_path: str, weight_map_path: str, pagerank_path: str):  
    """Generate weight_map and PageRank from var_define_chain.json."""  
      
    # Load var_define_chain data  
    with open(define_chain_path, 'r', encoding='utf-8') as f:  
        var_define_chain = json.load(f)  
      
    # Build weight map from dependencies  
    weight_map = build_weight_map(var_define_chain)  
      
    # Calculate PageRank using NetworkX  
    pagerank_scores = calculate_pagerank(weight_map)  
      
    # Save results  
    with open(weight_map_path, 'w', encoding='utf-8') as f:  
        json.dump(weight_map, f, indent=2, ensure_ascii=False)  
      
    with open(pagerank_path, 'w', encoding='utf-8') as f:  
        json.dump(pagerank_scores, f, indent=2, ensure_ascii=False)  
      
    print(f"Generated weight_map: {weight_map_path}")  
    print(f"Generated complete_PageRank: {pagerank_path}")  
  
def build_weight_map(var_define_chain: dict) -> dict:  
    """Build weight map from variable dependencies including both data and control dependencies."""  
    weight_map = defaultdict(lambda: defaultdict(int))  
      
    for var_name, define_info in var_define_chain.items():  
        # Extract DDeps (data dependencies) from each assignment  
        d_deps = define_info.get('DDeps', [])  
          
        for dep_list in d_deps:  
            for dep_signal in dep_list:  
                if dep_signal:  # Skip empty dependencies  
                    weight_map[dep_signal][var_name] += 1  
          
        # Extract CDeps (control dependencies) from each assignment  
        c_deps = define_info.get('CDeps', [])  
          
        for assignment_c_deps in c_deps:  
            # CDeps is a nested list structure for each assignment  
            for control_dep_list in assignment_c_deps:  
                for control_signal in control_dep_list:  
                    if control_signal:  # Skip empty dependencies  
                        weight_map[control_signal][var_name] += 1  
      
    # Convert to regular dict for JSON serialization  
    return {src: dict(dests) for src, dests in weight_map.items()}
  
def calculate_pagerank(weight_map: dict, damping: float = 0.85, max_iter: int = 100, tolerance: float = 1e-6) -> dict:  
    """Calculate PageRank scores using NetworkX."""  
      
    # Build directed graph with weights  
    G = nx.DiGraph()  
      
    # Add edges with weights  
    for src, dests in weight_map.items():  
        for dest, weight in dests.items():  
            G.add_edge(src, dest, weight=weight)  
      
    # Calculate PageRank with weights  
    if G.number_of_nodes() > 0:  
        # Use weighted PageRank where edge weights influence the transition probabilities  
        pagerank = nx.pagerank(G, alpha=damping, max_iter=max_iter, tol=tolerance, weight='weight')  
    else:  
        pagerank = {}  
      
    return pagerank  
  
def main():  
    parser = argparse.ArgumentParser(description='Generate weight_map and PageRank from var_define_chain')  
    parser.add_argument('define_chain_file', help='Input var_define_chain.json file path')  
    parser.add_argument('weight_map_file', help='Output weight_map.json file path')  
    parser.add_argument('pagerank_file', help='Output complete_PageRank.json file path')  
      
    args = parser.parse_args()  
      
    generate_weight_and_pagerank(args.define_chain_file, args.weight_map_file, args.pagerank_file)  
  
if __name__ == "__main__":  
    main()