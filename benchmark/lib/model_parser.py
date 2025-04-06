from abc import ABC, abstractmethod
from lib.paths import OutputPath

from pathlib import Path

class ModelParser:
    def __init__(self, path: OutputPath):
        self.path = path

    @abstractmethod
    def parse(self):
        pass

    @abstractmethod
    def log(self):
        pass

class SMT2ModelParser(ModelParser):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path)

    def parse(self):
        pass

    def log(self):
        pass


class BTORModelParser(ModelParser):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path)

    def parse(self):
        pass

    def log(self):
        pass
