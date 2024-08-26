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
import shlex
from subprocess import Popen, TimeoutExpired
from pathlib import Path

PIPE = -1
STDOUT = -2
DEVNULL = -3

# Define exit error codes
EXIT_SUCCESS = 0
EXIT_MODEL_GENERATION_ERROR = 2
EXIT_TOOL_NOT_FOUND = 3

rotor_path = Path("../rotor")
examples_dir = Path("../examples/symbolic")
models_dir = Path("../models")


starc_64_riscv_path = Path(models_dir/"starc"/"64-bit"/"riscv")
starc_64_riscu_path = Path(models_dir/"starc"/"64-bit"/"riscu")



class ToolNotAvailableError(Exception):
    pass

class TimeoutException(Exception):
    def __init__(self, command, timeout, output): # , error_output):
        Exception.__init__(self, 'The command \"' + command +
                           '\" has timed out after ' + str(timeout) + 's')

        self.output = output
        # self.error_output = error_output

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

def execute(command, timeout=30):
    process = Popen(shlex.split(command), stdout=PIPE, stderr=STDOUT)

    timedout = False

    if sys.version_info < (3,3):
        stdoutdata, _ = process.communicate()
    else:
        try:
            stdoutdata, _ = process.communicate(timeout=timeout)
        except TimeoutExpired:
            process.kill()
            stout, _ = process.communicate()
            timedout = True
    output = stdoutdata.decode(sys.stdout.encoding)

    if timedout:
        raise TimeoutException(command, timeout, output)
    
    return (process.returncode, output)

def generate_model(file, args, output_dir) -> None:
    returncode, output = execute(f"{rotor_path} -c {file} -o {output_dir / file.name} {args}")
    outputpath = Path(output_dir / file.name)
    outputpath.unlink()

    if(returncode != 0):
        custom_exit(output, EXIT_MODEL_GENERATION_ERROR)

def generate_starc_64_bit_riscu(file) -> None:
    generate_model(file,"- 1 -riscuonly", starc_64_riscu_path)

def generate_starc_64_bit_riscv(file) -> None:
    generate_model(file,"- 1", starc_64_riscv_path)

def generate_all_examples() -> None:
    # check if selfie || gcc is available
    # locate examples directory
    # take each individual file and try to create model from it into all possible options
    #check if models directory exists, if it does remove all files inside and 
    clean_examples()
    #prepare directories
    models_dir.mkdir()
    starc_64_riscv_path.mkdir(parents=True)
    starc_64_riscu_path.mkdir(parents=True)

    files = [file for file in examples_dir.iterdir()]
    for file in files:
        if(file.suffix != ".c"):
            continue
        # STARC
        # -----
        #1) 64-bit architecture risc-u
        generate_starc_64_bit_riscu(file)
        #2) 64-bit architecture risc-v
        generate_starc_64_bit_riscv(file)



    # share info about the process in console

if __name__ == "__main__":
    try: 
        check_needed_tools()
    except ToolNotAvailableError as e:
        custom_exit(str(e), EXIT_TOOL_NOT_FOUND);
    
    generate_all_examples()

