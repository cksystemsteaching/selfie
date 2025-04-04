from abc import ABC, abstractmethod
from pathlib import Path

class ModelParser:
    def __init__(self, path: Path):
        self.path

    @abstractmethod
    def parse(self):
        pass

    @abstractmethod
    def log(self):
        pass

class SMT2ModelParser(ModelParser):
    def parse(self):
        pass

    def log(self):
        pass


class BTORModelParser(ModelParser):
    def parse(self):
        pass

    def log(self):
        pass
