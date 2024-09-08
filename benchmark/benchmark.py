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


from lib.checks import check_needed_tools
from lib.exceptions import ToolNotAvailableError, DirectoryNotFoundError, InternalToolNotAvailableError, TimeoutException
import lib.config as cfg
from lib.generate import generate_all_examples, clean_examples, ModelType
from lib.print import custom_exit
import lib.argument_parser as arg_parser

if __name__ == "__main__":
    try:
        args = arg_parser.parse_arguments()

        check_needed_tools()

        if args.clean:
            clean_examples()
            # exit

        if args.generate_examples:
            generate_all_examples()
            # exit

        if args.model_type and args.source_file:
            ModelType(args.source_file, args.model_type).generate()
            exit(0)

        if not args.model_type:
            custom_exit(f"{cfg.RED}ERROR: --model-type is required")
        
        if not args.source_file:
            custom_exit(f"{cfg.RED}ERROR: --source-file is required")

    except ToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except DirectoryNotFoundError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except InternalToolNotAvailableError as e:
        custom_exit(str(e), cfg.EXIT_TOOL_NOT_FOUND)
    except TimeoutException as e:
        custom_exit(str(e), cfg.EXIT_MODEL_GENERATION_ERROR)
