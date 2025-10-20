import json
import logging
from pathlib import Path

logger = logging.getLogger(__name__)

class AnalysisLoader:
    def __init__(self, analysis_file_path):
        self.file_path = Path(analysis_file_path)
        if not self.file_path.exists():
            raise FileNotFoundError(f"Analysis file not found at: {self.file_path}")
        self.data = self._load_data()
        self.design_name = self.file_path.stem

    def _load_data(self):
        """Loads the JSON data from the analysis file."""
        logger.info(f"Loading analysis data from {self.file_path}...")
        with open(self.file_path, 'r') as f:
            try:
                data = json.load(f)
                logger.info("Analysis data loaded successfully.")
                return data
            except json.JSONDecodeError as e:
                logger.error(f"Failed to decode JSON from {self.file_path}: {e}")
                raise
    
    def get_signals_for_role_labeling(self):
        """Prepares a simplified dictionary of signals for the LLM."""
        signals_for_llm = {}
        for full_name, details in self.data.items():
            # Extract only the most relevant info for the LLM to avoid clutter
            signals_for_llm[full_name] = {
                "direction": details.get("direction", "internal"),
                "isControl": details.get("isControlVariable", False),
                "bitWidth": details.get("bitWidth", 1)
            }
        return signals_for_llm