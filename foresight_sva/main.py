import argparse
import logging
from pathlib import Path
import sys
import asyncio

# Add the project root to Python's path to allow for clean imports from 'src'
# This makes the script runnable from various locations.
try:
    project_root = Path(__file__).resolve().parent
    sys.path.insert(0, str(project_root))
    from src.utils import setup_logging, load_config, load_prompts, save_json
    from src.llm_handler import LLMHandler
    from src.analysis_loader import AnalysisLoader
    from src.causal_reasoner import CausalReasoner
    from src.visualizer import generate_connectivity_report
except ImportError as e:
    print(f"Error: Failed to import necessary modules. Ensure the script is run from a directory where 'src' is accessible. Details: {e}")
    sys.exit(1)


# Get a logger for the main script
logger = logging.getLogger(__name__)

async def async_main():
    """
    The asynchronous main function to run the complete ForesightSVA pipeline.
    """
    # 1. Setup & Configuration
    parser = argparse.ArgumentParser(description="ForesightSVA: AI-driven SVA Generation")
    parser.add_argument("--analysis_file", type=Path, required=True, help="Path to the JSON analysis file from the C++ tool.")
    # parser.add_argument("--clk", type=str, default="clk", help="Name of the clock signal (without module prefix).")
    # parser.add_argument("--rst_n", type=str, default="rst_n", help="Name of the active-low reset signal (without module prefix).")
    args = parser.parse_args()

    try:
        config = load_config()
        prompts = load_prompts()
        setup_logging(config)
    except Exception as e:
        logging.basicConfig()
        logger.error(f"Failed to load configuration. Aborting. Error: {e}")
        return

    logger.info("=" * 50)
    logger.info("🚀 Starting ForesightSVA Full Pipeline (Async Mode)")
    logger.info("=" * 50)
    
    analysis_file_path = args.analysis_file.resolve()
    logger.info(f"Processing analysis file: {analysis_file_path}")


    # 2. Instantiate core components
    llm_handler = LLMHandler(config)
    
    try:
        # --- Phase 1: Load and Annotate ---
        loader = AnalysisLoader(analysis_file_path)
        from src.utils import APP_ROOT
        design_name = loader.design_name
        reports_root = APP_ROOT / config['paths']['reports_dir']
        output_dir = reports_root / design_name

        analysis_data = loader.data
        # --- Phase 0: Build graph ---
        reasoner = CausalReasoner(llm_handler, prompts)
        connectivity_graph = reasoner._create_connectivity_graph(analysis_data)
        output_path_phase0 = output_dir / "0_connectivity_report.txt"
        generate_connectivity_report(connectivity_graph, output_path_phase0)
        return
        enriched_data = await reasoner.label_semantic_roles_async(analysis_data)     
        if not enriched_data:
            logger.error("❌ Phase 1 failed: Could not obtain semantically enriched data. Aborting pipeline.")
            return
        output_path_phase1 = output_dir / "1_semantic_analysis.json"
        save_json(enriched_data, output_path_phase1)
        logger.info(f"✅ Phase 1 successful. Enriched analysis saved to: {output_path_phase1}")


        # --- Phase 2: Reason and Generate Scenarios ---
        logger.info("\n" + "=" * 20 + " Starting Phase 2: Reasoning " + "=" * 20)
        
        graph_data = await reasoner.build_causal_graph_async(enriched_data)
        
        output_path_phase2_graph = output_dir / "2_causal_graph.json"
        save_json(graph_data, output_path_phase2_graph)
        logger.info(f"✅ LLM-labeled causal graph saved to: {output_path_phase2_graph}")
        scenario = reasoner.reason_attack_scenarios(enriched_data)
        if not scenario:
            logger.error("❌ Phase 2 failed to generate an attack scenario. Aborting pipeline.")
            return

        output_path_phase2_scenario = output_dir / "3_attack_scenarios.txt"
        with open(output_path_phase2_scenario, 'w') as f:
            f.write(scenario)
        logger.info(f"✅ Attack scenario saved to: {output_path_phase2_scenario}")
        logger.info(f"🔥 Generated Scenario: {scenario.strip()}")


        # # --- Phase 3: Generate SVA ---
        # logger.info("\n" + "=" * 20 + " Starting Phase 3: SVA Generation " + "=" * 20)
        
        # sva_generator = SVAGenerator(llm_handler, prompts)
        
        # # Find the full hierarchical names of clock and reset signals from the analysis data
        # clk_full_name = next((name for name in enriched_data if name.endswith(f".{args.clk}")), args.clk)
        # rst_n_full_name = next((name for name in enriched_data if name.endswith(f".{args.rst_n}")), args.rst_n)
        
        # sva_code = sva_generator.generate_sva(scenario, enriched_data, design_name, clk_full_name, rst_n_full_name)

        # if sva_code:
        #     output_path_phase3_sva = output_dir / "4_generated_sva.sv"
        #     with open(output_path_phase3_sva, 'w') as f:
        #         f.write(sva_code)
        #     logger.info(f"✅ SVA code generated and saved to: {output_path_phase3_sva}")
        #     logger.info("--- Generated SVA Code ---")
        #     print("\n" + sva_code)
        #     logger.info("--------------------------")
        #     logger.info("🎉 ForesightSVA pipeline completed successfully! 🎉")
        # else:
        #     logger.error("❌ Phase 3 failed to generate SVA code.")
        
    except FileNotFoundError as e:
        logger.error(f"❌ Critical Error: Input file not found. {e}")
    except Exception as e:
        logger.error(f"An unexpected error occurred in the main pipeline: {e}", exc_info=True)

#TODO
'''
信号提取过于抽象
'''

if __name__ == "__main__":
    # Standard way to run a top-level async function with graceful exit
    try:
        asyncio.run(async_main())
    except KeyboardInterrupt:
        print("\nAnalysis interrupted by user.")
    except Exception as e:
        # Fallback logger in case config loading failed
        logging.basicConfig()
        logging.getLogger(__name__).critical(f"A critical error prevented the application from running: {e}", exc_info=True)