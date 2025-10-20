import logging
from pathlib import Path
import networkx as nx
from src.utils import ensure_dir

logger = logging.getLogger(__name__)

def generate_connectivity_report(connectivity_graph: nx.Graph, output_path: Path):
    """
    Generates a simple text report describing the structure of the
    initial connectivity graph from the static analysis.

    Args:
        connectivity_graph (nx.Graph): The graph built from static analysis.
        output_path (Path): The path to save the output .txt report.
    """
    logger.info(f"Generating connectivity graph text report at: {output_path}")
    
    ensure_dir(output_path.parent)

    try:
        report_lines = []
        report_lines.append("=" * 80)
        report_lines.append(" ForesightSVA - Static Analysis Connectivity Report")
        report_lines.append("=" * 80)
        
        report_lines.append(f"\nThis report describes the connectivity graph built directly from the static analysis JSON.")
        report_lines.append(f"It is used to guide the intelligent, context-aware chunking process.\n")
        
        report_lines.append(f"Graph Summary:")
        report_lines.append(f"  - Total Signals (Nodes): {connectivity_graph.number_of_nodes()}")
        report_lines.append(f"  - Total Connections (Edges): {connectivity_graph.number_of_edges()}")

        # --- Section on Connected Components ---
        connected_components = list(nx.connected_components(connectivity_graph))
        connected_components.sort(key=len, reverse=True)
        
        report_lines.append(f"\nFound {len(connected_components)} logically connected signal groups (components):")

        for i, component in enumerate(connected_components):
            report_lines.append("\n" + "-" * 50)
            report_lines.append(f"Component #{i+1} (Size: {len(component)} signals)")
            report_lines.append("-" * 50)
            
            component_nodes = sorted(list(component))
            for node_id in component_nodes:
                # short_name = node_id.split('.')[-1]
                short_name=node_id
                # Find all neighbors of this node within the same component
                neighbors = sorted([n for n in connectivity_graph.neighbors(node_id)])
                
                report_lines.append(f"  - {short_name:<30} is connected to: {', '.join(neighbors)}")

        report_lines.append("\n" + "=" * 80)
        report_lines.append(" End of Report")
        report_lines.append("=" * 80)
        
        with open(output_path, 'w') as f:
            f.write("\n".join(report_lines))
        
        logger.info("✅ Connectivity report saved successfully.")

    except Exception as e:
        logger.error(f"Failed to generate connectivity report: {e}", exc_info=True)