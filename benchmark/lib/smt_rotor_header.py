import re
from typing import Dict, List, Optional
from pathlib import Path
from dataclasses import dataclass

@dataclass
class RotorHeader:
    source_file: Optional[str] = None
    kmin: Optional[int] = None
    kmax: Optional[int] = None
    bytecode_size: Optional[int] = None
    data_size: Optional[int] = None
    virtual_address_space: Optional[int] = None
    code_word_size: Optional[int] = None
    memory_word_size: Optional[int] = None
    heap_allowance: Optional[int] = None
    stack_allowance: Optional[int] = None
    cores: Optional[int] = None
    bytestoread: Optional[int] = None
    flags: List[str] = None
    comments_removed: bool = False

    def __post_init__(self):
        self.flags = self.flags or []
    
    def log(self):
        print("----TESTING----")
        print(f"source_file: {self.source_file}")
        print(f"k_min: {self.kmin}")
        print(f"k_max: {self.kmax}")
        print(f"bytecode_size: {self.bytecode_size}")
        print(f"data_size: {self.data_size}")
        print(f"virtual_address_space: {self.virtual_address_space}")
        print(f"code_word_size: {self.code_word_size}")
        print(f"memory_word_size: {self.memory_word_size}")
        print(f"heap_allowance: {self.heap_allowance}")
        print(f"stack_allowance: {self.stack_allowance}")
        print(f"cores: {self.cores}")
        print(f"bytes_to_read: {self.bytestoread}")
        print(f"flags: {self.flags}")
        print(f"comments_removed: {self.comments_removed}")

class RotorParser:
    HEADER_PATTERNS = {
        'source_file': re.compile(r'; for RISC-V executable obtained from (.+)'),
        'kmin': re.compile(r'; with -kmin (\d+)'),
        'kmax': re.compile(r'; with .* -kmax (\d+)'),
        'bytecode': re.compile(r'; with (\d+) bytes of code'),
        'data': re.compile(r'; and (\d+) bytes of data'),
        'virtual_address': re.compile(r'; with -virtualaddressspace (\d+)'),
        'code_word': re.compile(r'; with -codewordsize (\d+)'),
        'memory_word': re.compile(r'; with -memorywordsize (\d+)'),
        'heap': re.compile(r'; with -heapallowance (\d+)'),
        'stack': re.compile(r'; with -stackallowance (\d+)'),
        'cores': re.compile(r'; with -cores (\d+)'),
        'bytes_to_read': re.compile(r'; with -bytestoread (\d+)'),
        'nocomments': re.compile(r'; with -nocomments')
    }

    @classmethod
    def parse_header(cls, file_path) -> RotorHeader:
        header = RotorHeader()
        flags = []
        
        with open(file_path, 'r') as f:
            for line in f:
                # Check each pattern
                for field, pattern in cls.HEADER_PATTERNS.items():
                    if match := pattern.search(line):
                        value = match.group(1) if match.groups() else None
                        cls._set_header_field(header, field, value, flags)
        
        header.flags = flags
        return header

    @staticmethod
    def _set_header_field(header, field, value, flags):
        if field == 'source_file':
            header.source_file = value
        elif field == 'kmin':
            header.kmin = int(value)
        elif field == 'kmax':
            header.kmax = int(value)
        elif field == 'bytecode':
            header.bytecode_size = int(value)
        elif field == 'data':
            header.data_size = int(value)
        elif field == 'virtual_address':
            header.virtual_address_space = int(value)
        elif field == 'code_word':
            header.code_word_size = int(value)
        elif field == 'memory_word':
            header.memory_word_size = int(value)
        elif field == 'heap':
            header.heap_allowance = int(value)
        elif field == 'stack':
            header.stack_allowance = int(value)
        elif field == 'cores':
            header.cores = int(value)
        elif field == 'bytes_to_read':
            header.bytestoread = int(value)
        elif field == 'constants':
            header.constants_propagated = True
        elif field == 'nocomments':
            header.comments_removed = True
        else:
            flags.append(field.replace('_', '-'))