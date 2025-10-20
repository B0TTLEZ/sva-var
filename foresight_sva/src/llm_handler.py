import os
import logging
import json
from openai import OpenAI, AsyncOpenAI, APITimeoutError, APIConnectionError

# Get a logger for this module
logger = logging.getLogger(__name__)

class LLMHandler:
    """
    A robust handler for making both synchronous and asynchronous API calls
    to various LLM providers. It is configured via the main config file and
    supports any OpenAI-compatible API.
    """
    def __init__(self, config: dict):
        """
        Initializes the LLMHandler based on the 'active_provider' in the config.

        Args:
            config (dict): The loaded application configuration dictionary.
        """
        llm_config = config.get('llm', {})
        active_provider_name = llm_config.get('active_provider')

        if not active_provider_name:
            raise ValueError("LLM config is missing 'active_provider'.")
        
        provider_config = llm_config.get('providers', {}).get(active_provider_name)
        if not provider_config:
            raise ValueError(f"Config for provider '{active_provider_name}' not found.")

        # --- Extract provider-specific configuration ---
        self.model = provider_config.get('model')
        self.temperature = provider_config.get('temperature', 0.1)
        self.timeout = provider_config.get('timeout', 120)
        api_key = provider_config.get('api_key')
        base_url = provider_config.get('base_url')

        if not all([self.model, api_key, base_url]):
            raise ValueError(f"Provider '{active_provider_name}' config is missing required keys.")


        if not api_key:
            raise ValueError(f"Environment variable '{api_key}' is not set.")

        # --- Initialize BOTH synchronous and asynchronous clients ---
        self.sync_client = OpenAI(api_key=api_key, base_url=base_url)
        self.async_client = AsyncOpenAI(api_key=api_key, base_url=base_url)
        
        logger.info(f"LLMHandler initialized for provider: '{active_provider_name}', model: '{self.model}'")

    def make_request(self, prompt: str, is_json: bool = False) -> str | dict | None:
        """
        Makes a synchronous request to the LLM API.
        """
        logger.debug(f"Making SYNC request (JSON: {is_json}). Prompt starts with: {prompt[:100]}...")
        try:
            response_format = {"type": "json_object"} if is_json else {"type": "text"}
            response = self.sync_client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                timeout=self.timeout,
                response_format=response_format
            )
            content = response.choices[0].message.content.strip()
            if is_json:
                return json.loads(content)
            return content
        except Exception as e:
            logger.error(f"An error occurred during sync LLM call: {e}", exc_info=True)
            return None

    async def make_request_async(self, prompt: str, is_json: bool = False) -> str | dict | None:
        """
        Asynchronously makes a request to the configured LLM API provider.
        """
        logger.debug(f"Making ASYNC request (JSON: {is_json}). Prompt starts with: {prompt[:100]}...")
        try:
            response_format = {"type": "json_object"} if is_json else {"type": "text"}
            response = await self.async_client.chat.completions.create(
                model=self.model,
                messages=[{"role": "user", "content": prompt}],
                temperature=self.temperature,
                timeout=self.timeout,
                response_format=response_format
            )
            content = response.choices[0].message.content.strip()
            if is_json:
                try:
                    return json.loads(content)
                except json.JSONDecodeError:
                    logger.error(f"Failed to decode JSON from async response. Raw: {content}")
                    return None
            return content
        except Exception as e:
            logger.error(f"An error occurred during async LLM call: {e}", exc_info=True)
            return None