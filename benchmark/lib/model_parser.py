from abc import ABC, abstractmethod
from lib.paths import OutputPath

from pathlib import Path


import re
from collections import defaultdict
from typing import Tuple, Dict

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
        """
        Analyzes an SMT-LIBv2 file and returns statistics.
        
        Returns:
            Dictionary with keys:
            - total_lines
            - comment_lines
            - code_lines
            - blank_lines
            - define_count (number of define-fun commands)
        """
        self.stats = {
            'total_lines': 0,
            'comment_lines': 0,
            'code_lines': 0,
            'blank_lines': 0,
            'define_count': 0,
        }
        
        # Regex patterns
        comment_pattern = re.compile(r'^\s*;')
        blank_pattern = re.compile(r'^\s*$')
        define_pattern = re.compile(r'^\s*\(define-fun', re.IGNORECASE)
        
        previous_command = None
        
        with open(self.path, 'r') as f:
            for line in f:
                self.stats['total_lines'] += 1
                
                if comment_pattern.match(line):
                    self.stats['comment_lines'] += 1
                elif blank_pattern.match(line):
                    self.stats['blank_lines'] += 1
                else:
                    self.stats['code_lines'] += 1
                    
                    # Check for define-fun commands
                    if define_pattern.search(line):
                        self.stats['define_count'] += 1
                    
    
        return self.stats

    def log(self):
        self.parse()
        print("SMT-LIBv2 File Analysis:")
        print(f"File name: {self.path.name}")
        if len(self.path.parents) > 1:
            print(f"File path: {self.path}")
        print(f"Total lines: {self.stats['total_lines']}")
        print(f"Code lines: {self.stats['code_lines']}")
        print(f"Comment lines: {self.stats['comment_lines']}")
        print(f"Blank lines: {self.stats['blank_lines']}")
        print(f"define-fun commands: {self.stats['define_count']}")


class BTORModelParser(ModelParser):
    def __init__(self, output_path: OutputPath):
        super().__init__(output_path)

    def parse(self):
        pass

    def log(self):
        pass
