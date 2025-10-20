import logging
import yaml
from pathlib import Path

# Define the project's root directory relative to this utils.py file.
# Path(__file__) is the path to the current file (utils.py).
# .parent is the 'src' directory.
# .parent.parent is the 'foresight_sva' directory, which is our root for this app.
APP_ROOT = Path(__file__).parent.parent

def setup_logging(config: dict):
    """Sets up the logging configuration from the config dictionary."""
    logging.basicConfig(
        level=config.get('logging', {}).get('level', 'INFO'),
        format=config.get('logging', {}).get('format', '%(asctime)s - %(message)s')
    )

def load_config(config_path: str = 'config/config.yaml'):
    """
    Loads the main configuration file relative to the application root.
    """
    # Construct the full, absolute path to the config file
    full_path = APP_ROOT / config_path
    logger = logging.getLogger(__name__)
    logger.debug(f"Attempting to load config from: {full_path}")
    
    try:
        with open(full_path, 'r') as f:
            return yaml.safe_load(f)
    except FileNotFoundError:
        logger.error(f"Configuration file not found at: {full_path}")
        raise
    except Exception as e:
        logger.error(f"Error loading configuration file: {e}")
        raise

def load_prompts(prompts_path: str = 'config/prompts.yaml'):
    """
    Loads the LLM prompts file relative to the application root.
    """
    full_path = APP_ROOT / prompts_path
    logger = logging.getLogger(__name__)
    logger.debug(f"Attempting to load prompts from: {full_path}")
    
    try:
        with open(full_path, 'r') as f:
            return yaml.safe_load(f)
    except FileNotFoundError:
        logger.error(f"Prompts file not found at: {full_path}")
        raise
    except Exception as e:
        logger.error(f"Error loading prompts file: {e}")
        raise


def ensure_dir(path: Path):
    """Ensures that a directory exists, creating it if necessary."""
    path.mkdir(parents=True, exist_ok=True)

def save_json(data: dict, file_path: Path):
    """Saves a dictionary to a JSON file with pretty printing."""
    ensure_dir(file_path.parent)
    with open(file_path, 'w') as f:
        import json
        json.dump(data, f, indent=4)