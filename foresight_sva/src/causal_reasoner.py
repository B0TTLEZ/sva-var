import logging
import json
import asyncio
from tqdm.asyncio import tqdm as asyncio_tqdm
import networkx as nx

# Get a logger for this module
logger = logging.getLogger(__name__)

# Helper function to split a dictionary into uniformly sized chunks
def chunk_dict(data: dict, chunk_size: int):
    """Splits a dictionary into smaller dictionary chunks of a given size."""
    it = iter(data)
    for _ in range(0, len(data), chunk_size):
        chunk = {k: data[k] for k in [next(it, None) for _ in range(chunk_size)] if k is not None}
        if chunk:
            yield chunk

class CausalReasoner:
    """
    The core reasoning engine of ForesightSVA. It performs a multi-stage analysis:
    1.  Labels semantic roles of signals using an LLM with context-aware batching.
    2.  Builds a detailed, LLM-labeled causal graph.
    3.  Reasons on the graph to generate "what-if" attack scenarios.
    """
    def __init__(self, llm_handler, prompts):
        self.llm = llm_handler
        self.prompts = prompts
        self.graph = None # The causal graph will be built during Phase 2
        logger.info("CausalReasoner initialized.")

    # ==============================================================================
    # STAGE 1: SEMANTIC ROLE LABELING (with Context-Aware Batching)
    # ==============================================================================

    def _create_connectivity_graph(self, analysis_data: dict) -> nx.Graph:
        """
        Creates a comprehensive undirected graph based on static analysis data.
        This graph represents all functional connections (data and control).
        """
        logger.info("Building connectivity graph from static analysis data...")
        G = nx.Graph()
        all_signal_names = list(analysis_data.keys())
        
        G.add_nodes_from(all_signal_names)
            
        for signal_name, details in analysis_data.items():
            # Edge Type 1: Direct Data Flow (using fanOut)
            for fanout_signal in details.get("fanOut", []):
                if fanout_signal in all_signal_names:
                    G.add_edge(signal_name, fanout_signal)

            # Edge Type 2: Dependencies from assignments
            if "assignments" in details and details.get("assignments"):
                for assignment in details["assignments"]:
                    # a) Connect driving signals to the assigned signal (data flow)
                    for driver in assignment.get("drivingSignals", []):
                         if driver in all_signal_names:
                            G.add_edge(driver, signal_name)
                    
                    # b) Connect control signals to the assigned signal (control dependency)
                    if "path" in assignment and assignment.get("path"):
                        for condition in assignment["path"]:
                            if "expr" in condition and "involvedSignals" in condition["expr"]:
                                for control_signal in condition["expr"]["involvedSignals"]:
                                    if control_signal in all_signal_names:
                                        G.add_edge(signal_name, control_signal)
        
        logger.info(f"Connectivity graph built with {G.number_of_nodes()} nodes and {G.number_of_edges()} edges.")
        return G

    def _generate_context_aware_chunks(self, analysis_data: dict, signals_for_llm: dict, chunk_size: int = 30) -> list[dict]:
        """
        Generates signal chunks that are aware of connectivity to preserve context for the LLM.
        """
        logger.info("Generating context-aware chunks for labeling...")
        connectivity_graph = self._create_connectivity_graph(analysis_data)
        
        connected_components = list(nx.connected_components(connectivity_graph))
        logger.info(f"Found {len(connected_components)} logically connected signal groups.")
        
        chunks = []
        current_chunk = {}
        connected_components.sort(key=len)

        for component in connected_components:
            component_dict = {sig: signals_for_llm[sig] for sig in component if sig in signals_for_llm}
            
            if len(component) > chunk_size:
                logger.warning(f"A large signal group ({len(component)} signals) is larger than chunk_size ({chunk_size}) and will be split.")
                component_iter = iter(component_dict.items())
                while True:
                    sub_chunk_items = [next(component_iter, None) for _ in range(chunk_size)]
                    sub_chunk = {k: v for k, v in sub_chunk_items if k is not None}
                    if not sub_chunk: break
                    chunks.append(sub_chunk)
            elif len(current_chunk) + len(component) > chunk_size and current_chunk:
                chunks.append(current_chunk)
                current_chunk = component_dict
            else:
                current_chunk.update(component_dict)
        
        if current_chunk:
            chunks.append(current_chunk)
            
        logger.info(f"Intelligently created {len(chunks)} chunks from the signal groups.")
        return chunks, connectivity_graph

    async def _label_role_chunk_async(self, signal_chunk: dict) -> dict | None:
        """Asynchronously processes a single chunk to get their semantic roles."""
        prompt_template = self.prompts.get('semantic_role_labeling')
        if not prompt_template:
            logger.error("Prompt 'semantic_role_labeling' not found.")
            return None
            
        signal_info_json_str = json.dumps(signal_chunk, indent=2)
        prompt = prompt_template.format(signal_info_json=signal_info_json_str)
        return await self.llm.make_request_async(prompt, is_json=True)

    async def label_semantic_roles_async(self, analysis_data: dict, chunk_size: int = 30) -> dict | None:
        """Asynchronously enriches analysis data with semantic roles using context-aware batching."""
        logger.info(f"Starting CONTEXT-AWARE semantic role labeling for {len(analysis_data)} signals...")
        
        signals_for_llm = {
            full_name: {
                "direction": details.get("direction", "internal"),
                "isControl": details.get("isControlVariable", False),
                "bitWidth": details.get("bitWidth", 1)
            } for full_name, details in analysis_data.items()
        }
        
        signal_chunks, connectivity_graph = self._generate_context_aware_chunks(analysis_data, signals_for_llm, chunk_size)
        
        if not signal_chunks:
            logger.error("No signal chunks were generated. Aborting.")
            return None

        logger.info(f"Sending all {len(signal_chunks)} chunks in parallel...")
        all_roles = {}
        
        tasks = [self._label_role_chunk_async(chunk) for chunk in signal_chunks]
        results = await asyncio_tqdm.gather(*tasks, desc="Labeling Signal Chunks (Async)")

        for res in results:
            if isinstance(res, dict):
                all_roles.update(res)
        
        if not all_roles:
            logger.error("Failed to get any valid semantic roles from LLM. Aborting.")
            return None

        logger.info(f"Received all role chunks. Merging roles into the analysis data...")
        enriched_data = analysis_data.copy()
        for signal_name in enriched_data:
            enriched_data[signal_name]['semantic_role'] = all_roles.get(signal_name, 'Unknown')
        
        logger.info("Semantic role labeling complete.")
        return enriched_data

    # ==============================================================================
    # STAGE 2: CAUSAL GRAPH & SCENARIO REASONING
    # ==============================================================================
    
    def _extract_code_snippet(self, analysis_data: dict, driver: str, load: str) -> str:
        """Extracts a relevant code snippet showing the connection between a driver and a load."""
        load_details = analysis_data.get(load, {})
        if "assignments" in load_details and load_details["assignments"]:
            for assignment in load_details["assignments"]:
                all_involved = assignment.get("drivingSignals", [])
                if "path" in assignment and assignment["path"]:
                    for cond in assignment["path"]:
                        all_involved.extend(cond.get("expr", {}).get("involvedSignals", []))
                
                if driver in all_involved:
                    path_str = " & ".join([p['expr']['expression'] for p in assignment.get('path', [])])
                    drivers_str = ", ".join(assignment.get('drivingSignals', []))
                    if path_str and drivers_str:
                        return f"{load} <= func({drivers_str}) WHEN ({path_str})"
                    elif drivers_str:
                         return f"{load} <= func({drivers_str})"
                    else:
                        return f"{load} is affected WHEN ({path_str})"

        return f"Connection between {driver} and {load} found, but no simple code snippet."

    async def _label_edge_causality_async(self, edge: tuple, enriched_data: dict) -> tuple | None:
        """
        Asynchronously labels a single edge with its causal type using an LLM.
        (This version does NOT require a pbar argument).
        """
        driver_name, load_name = edge
        driver_node = enriched_data.get(driver_name, {})
        load_node = enriched_data.get(load_name, {})
        
        prompt_template = self.prompts.get('causal_link_inference')
        if not prompt_template:
            logger.error("Prompt 'causal_link_inference' not found.")
            return None

        code_snippet = self._extract_code_snippet(enriched_data, driver_name, load_name)

        prompt = prompt_template.format(
            driver_signal=driver_name,
            driver_role=driver_node.get('semantic_role', 'Unknown'),
            driver_direction=driver_node.get('direction', 'internal'),
            load_signal=load_name,
            load_role=load_node.get('semantic_role', 'Unknown'),
            load_direction=load_node.get('direction', 'internal'),
            code_snippet=code_snippet
        )
        
        link_type_str = await self.llm.make_request_async(prompt, is_json=False)
        
        # We no longer manually update pbar here.
        
        if link_type_str and "no_link" not in link_type_str.lower():
            return (driver_name, load_name, {"label": link_type_str.strip()})
        
        logger.debug(f"LLM determined no valid causal link from {driver_name} to {load_name}")
        return None

    async def build_causal_graph_async(self, enriched_data: dict) -> dict:
        """
        Builds a directed causal graph by using an LLM to label the causality of
        edges from the connectivity graph.
        """
        logger.info("Starting causal graph construction with LLM-based edge labeling...")
        
        connectivity_graph = self._create_connectivity_graph(enriched_data)
        self.graph = nx.DiGraph()
        self.graph.add_nodes_from(connectivity_graph.nodes())
        
        edges_to_label = list(connectivity_graph.edges())
        if not edges_to_label:
            logger.warning("Connectivity graph has no edges. Causal graph will be empty.")
            return nx.node_link_data(self.graph)

        logger.info(f"Sending {len(edges_to_label)} edges to LLM for causality labeling in parallel...")
        
        # The list comprehension now correctly calls the updated helper function
        tasks = [self._label_edge_causality_async(edge, enriched_data) for edge in edges_to_label]
        
        # tqdm.asyncio.gather automatically handles the progress bar for the tasks
        results = await asyncio_tqdm.gather(*tasks, desc="Labeling Causal Edges (Async)")

        labeled_edges = [res for res in results if res is not None]
        
        self.graph.add_edges_from(labeled_edges)
        logger.info(f"Causal graph construction complete with {self.graph.number_of_edges()} labeled edges.")
        
        for node in self.graph.nodes():
            if node in enriched_data:
                self.graph.nodes[node].update(enriched_data[node])
        
        return nx.node_link_data(self.graph)

    def reason_attack_scenarios(self, enriched_data: dict) -> str | None:
        """Reasons about the design to generate 'What-if' attack scenarios."""
        logger.info("Starting attack scenario reasoning...")

        control_signals = [name for name, data in enriched_data.items() if data.get('semantic_role') == 'Configuration']
        state_signals = [name for name, data in enriched_data.items() if 'state' in name.lower() and data.get('semantic_role') == 'Status']
        output_signals = [name for name, data in enriched_data.items() if data.get('direction') == 'output']
        
        conditional_paths = {}
        for signal, details in enriched_data.items():
            if 'assignments' in details and details.get('assignments'):
                deepest_assignment = max(details['assignments'], key=lambda x: x.get('conditionDepth', 0), default=None)
                if deepest_assignment and deepest_assignment.get('conditionDepth', 0) > 2:
                    simple_path = [p['expr']['expression'] for p in deepest_assignment.get('path', [])]
                    conditional_paths[signal] = simple_path

        prompt_template = self.prompts.get('attack_scenario_generation')
        prompt = prompt_template.format(
            control_signals = ", ".join(control_signals) or "None",
            state_signals = ", ".join(state_signals) or "None",
            output_signals = ", ".join(output_signals) or "None",
            conditional_paths = json.dumps(conditional_paths, indent=2)
        )
        
        logger.info("Sending request to LLM for attack scenario generation...")
        scenario = self.llm.make_request(prompt)
        
        if scenario:
            logger.info("Successfully generated an attack scenario.")
            return scenario
        else:
            logger.error("Failed to generate an attack scenario.")
            return None