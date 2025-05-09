"""
Validates and extracts values from config file - specified provided model type
"""

import lib.config as cfg
from lib.exceptions import ParsingError, ConfigFormatError

from typing import List

import logging

logger = logging.getLogger("bt.model_config_parser")


class ModelConfigParser:
    """
    Validates and extracts values from model type configurations.
    It always expect full model type to be passed. Only partial type (model base) will generate an error.
    """

    def __init__(self, model_type_name: str):
        self.top_level = cfg.config["model_types"]
        self.model_type_bases = model_type_name.split("-")
        self.check()

    def check(self):
        current_level = self.top_level

        for level in self.model_type_bases:
            if level in current_level:
                current_level = current_level[level]
            else:
                raise ParsingError(self.__class__.__name__, self.model_type_bases, level)
        # Check if type has specified Rotor command in config file
        required_values = ["command"]
        for value in required_values:
            if not current_level or value not in current_level:
                raise ConfigFormatError(
                    message=f"{value} not present/or at the wrong place in specified model type.",
                    error_format=value,
                )

        allowed_formats = cfg.config["allowed_formats"]
        if self.parse_format() not in allowed_formats:
            raise ConfigFormatError(
                message=f"{self.parse_format()} is not an allowed format.",
                error_format=self.parse_format(),
            )
    
    def get_bases(self):
        return self.model_type_bases

    def parse_format(self):
        return self.model_type_bases[-1]

    def parse_model_generation_cmd(self):
        current_level = self.top_level

        for level in self.model_type_bases:
            current_level = current_level[level]

        return current_level["command"]

    def parse_compile_cmd(self):
        """
        That we can drill down with provided bases does not have to be checked since it was already checked in constructor.
        """
        current_level = self.top_level

        for level in self.model_type_bases:
            if "compilation" in current_level:
                return current_level["compilation"]
            current_level = current_level[level]

        return None
