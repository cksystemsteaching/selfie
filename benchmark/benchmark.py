""" 

1. First I need to parse arguments
-> what arguments will be available?

    1) --generate-all-examples
    2) --clean -> will delete all generated examples 
    3) --help 
    4) --model "file1" "file2"
    5) --output "output1" "output2"
    6) --compiler gcc || selfie     -> default: selfie
    7) --isa riscv || riscu         -> default: riscv

2. I should first do generate all examples then clean
    GCC
    ---
    -> I need to invoke gcc with specific option based on what I am generating (specify riscv architecture)
        1) rv32i    (32-bit architecture, base integer instruction set)
        2) rv32im   (32-bit architecture, base integer instruction set, multiplication/division)
        3) rv32imac (32-bit archutecture, base integer instruction set, multiplication/division, atomic, compressed instrctions)
        4) rv64imac (32-bit architecture, base integer instructions et, multiplication/division, atomic, cmpressed instructions)

    Selfie
    ------
    -> I need to invoke Selfie with speciic options 
    ! Since rotor does already include Selfie inside, selfie does not need to be invoked by itself, you can straight up generate models from source files !

        1) 32-bit architecture 
            a) full risc-v
            b) risc-u
        2) 64-bit architecture
            a) full risc-v
            b) risc-u
"""
import sys
import shutil
from pathlib import Path

# Define exit error codes
EXIT_SUCCESS = 0
EXIT_TOOL_NOT_FOUND = 3

rotor_path = Path("../rotor")
examples_dir = Path("../examples/symbolic")
models_dir = Path("../models")

class ToolNotAvailableError(Exception):
    pass

def is_tool_available(name) -> bool: 
    from shutil import which

    return which(name) is not None


def check_needed_tools() -> None:
    check_internal_tools(rotor_path)
    check_directory(examples_dir)
    #check_tool("riscv64-unknown-elf-gcc")

def check_tool(name) -> None:
    print(f"Checking if {name} is available...")
    if not is_tool_available(name):
        raise ToolNotAvailableError(f"Error: {name} is not available on this machine")

def check_internal_tools(tool) -> None:
    print(f"Checking if {tool} is exists...")
    if not tool.is_file():
        raise ToolNotAvailableError(f"Error: {tool} is not available inside project's directory")

def check_directory(dir) -> None:
    print(f"Checking if {dir} exists...")
    if not dir.is_dir():
        raise ToolNotAvailableError(f"Error: {dir} directory doesn't exist...")

def clean_examples() -> None:
    if models_dir.is_dir():
        shutil.rmtree(models_dir)


def custom_exit(message, code = 0):
    print(message)
    sys.exit(code)

def generate_all_examples() -> None:
    # check if selfie || gcc is available
    # locate examples directory
    # take each individual file and try to create model from it into all possible options
    #check if models directory exists, if it does remove all files inside and 
    clean_examples()
    models_dir.mkdir()
    files = [file for file in examples_dir.iterdir()]
    for file in files:
        print(file)
        # shutil.copy2(file, models_dir)
    # share info about the process in console

if __name__ == "__main__":
    try: 
        check_needed_tools()
    except ToolNotAvailableError as e:
        custom_exit(str(e), EXIT_TOOL_NOT_FOUND);
    
    generate_all_examples()

