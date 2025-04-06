from model_parser import SMT2ModelParser, BTORModelParser
from paths import OutputPath
class Model:
    def __init__(self, output_path, parser):
        self.output_path = output_path
        self.parser = parser

    def log(self):
        self.parser.parse()
        self.parser.log()


class SMT2Model(Model):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path, SMT2ModelParser(output_path))


class BTORModel(Model):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path, BTORModelParser(output_path))