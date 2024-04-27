import re
from typing import Callable


class Logger:
    class Colors:
        RESET = "\033[0m"
        RED = "\033[31m"
        GREEN = "\033[32m"
        YELLOW = "\033[33m"
        BLUE = "\033[34m"
        PURPLE = "\033[35m"
        CYAN = "\033[36m"
        WHITE = "\033[37m"

    @staticmethod
    def error(message: str, prefix="ERROR: "):
        Logger.__log_colored(Logger.Colors.RED, prefix, message)

    @staticmethod
    def problem(message: str, prefix="PROBLEM: "):
        Logger.__log_colored(Logger.Colors.YELLOW, prefix, message)

    @staticmethod
    def header(message: str, prefix="===== ", suffix=" ====="):
        Logger.__log_colored(Logger.Colors.BLUE, prefix, message, suffix)

    @staticmethod
    def inline_header(message: str, header: str):
        Logger.__log_colored(Logger.Colors.BLUE, header + Logger.Colors.RESET, message)

    @staticmethod
    def print_instruction_array(max_elements: int, array: list):
        if len(array) == 0:
            print("[]")
            return

        if len(array) <= max_elements:
            for item in array:
                print(item)
            return

        start_elements_count = max_elements // 2
        end_elements_count = max_elements - start_elements_count

        for i in range(start_elements_count):
            print(array[i])
        print("...")
        for i in range(end_elements_count):
            print(array[-end_elements_count + i])

    @staticmethod
    def __log_colored(color: str, prefix: str, message: str, suffix="", color_end=Colors.RESET):
        print(f"{color}{prefix}{message}{suffix}{color_end}")


class Instruction:
    class Source:
        RISCV = "RISC-V"
        ROTOR = "Rotor"

    def __init__(self, source: str, address: str, instruction: str, operands: list[str] | None, comments: str | None):
        if source is None:
            raise ValueError("Source must be provided")

        if address is None or instruction is None:
            raise ValueError("Address and instruction must be provided")

        self.source = source
        self.address = int(address, 16)
        self.instruction = instruction
        self.operands = operands if operands else []
        self.comments = comments

    @staticmethod
    def from_riscv(instruction: str) -> "Instruction":
        return Instruction.__create(instruction, Instruction.Source.RISCV, r"\s+([\da-f]+):\s+[\da-f]+\s+(\w*)(?:\s+([\w,()\-]*))?(.*?)[\n$]")

    @staticmethod
    def from_rotor(instruction: str) -> "Instruction":
        return Instruction.__create(instruction, Instruction.Source.ROTOR, r"0x([\da-f]+):\s+([\w.]*)(?:\s+([\w,()\-]*))?(.*?)[\n$]")

    @staticmethod
    def __create(instruction: str, source: str, regex: str):
        match = re.match(regex, instruction, re.IGNORECASE)
        if not match:
            # print("Instruction " + instruction + " does not match regex")
            raise ValueError("Instruction does not match regex")

        address = match.group(1)
        instruction = match.group(2)
        operands = match.group(3).split(",") if match.group(3) else None
        comments = match.group(4).strip() if match.group(4) else None

        return Instruction(source, address, instruction, operands, comments)

    def __eq__(self, other: "Instruction"):
        return self.address == other.address and self.instruction == other.instruction and Instruction.__operands_eq(self.operands, other.operands)

    def __ne__(self, other: "Instruction"):
        return not self.__eq__(other)

    @staticmethod
    def __operands_eq(op_a: list[str], op_b: list[str]):
        if op_a is None and op_b is None:
            return True

        if op_a is None or op_b is None:
            return False

        if len(op_a) != len(op_b):
            return False

        for i in range(len(op_a)):
            if not Instruction.__operand_eq(op_a[i], op_b[i]):
                return False

        return True

    @staticmethod
    def __operand_eq(op_a: str, op_b: str):
        op_a = op_a.lower()
        op_b = op_b.lower()

        if op_a == op_b or op_a == "0x" + op_b or op_b == "0x" + op_a:
            return True

        return False

    def __str__(self):
        return f"{hex(self.address)}: {self.instruction} {', '.join(self.operands)}"

    def __repr__(self):
        return self.__str__()


class FileReader:
    def __init__(self, file_path, instruction_class: Callable[[str], Instruction]):
        self.file = open(file_path, "r")
        self.instruction_class = instruction_class
        self.__peek: Instruction | None = None

    def peek_instruction(self) -> Instruction:
        if self.__peek is None:
            self.__peek = self.__actual_next_instruction()
        return self.__peek

    def next_instruction(self) -> Instruction:
        if self.__peek is not None:
            next_instruction = self.__peek
            self.__peek = None
            return next_instruction
        return self.__actual_next_instruction()

    def __actual_next_instruction(self) -> Instruction:
        while True:
            if (line := self.file.readline()) == "":
                raise EOFError("End of file")
            try:
                return self.instruction_class(str(line))
            except ValueError:
                pass


def main():
    riscv_reader = FileReader("C:/Users/alexe/Desktop/riscv.txt", Instruction.from_riscv)
    rotor_reader = FileReader("C:/Users/alexe/Desktop/rotoro.txt", Instruction.from_rotor)
    while True:
        try:
            # assert: We are at the same position in both files
            mismatching_instructions = []

            riscv_curr = riscv_reader.next_instruction()
            rotor_curr = rotor_reader.next_instruction()

            while rotor_curr.address > riscv_curr.address:
                mismatching_instructions.append(riscv_curr)
                riscv_curr = riscv_reader.next_instruction()

            if len(mismatching_instructions) > 0:
                # RISC-V had some instructions which Rotor didn't have

                if rotor_curr.address == riscv_curr.address:  # Are we back on track?
                    # Yes => log warning and continue
                    Logger.problem("Found RISC-V instructions without corresponding Rotor instructions:")
                    Logger.print_instruction_array(5, mismatching_instructions)
                    print()

                    continue
                else:
                    # No => seems like whole instruction set is mismatched. Log error and exit
                    Logger.error("Instruction sets are mismatched")
                    Logger.header("RISC-V")
                    Logger.print_instruction_array(5, [*mismatching_instructions, riscv_curr])
                    Logger.header("Rotor")
                    print(rotor_curr)

                    print()
                    Logger.error("Analysis stopped prematurely due to error", prefix="")
                    break

            while riscv_curr.address > rotor_curr.address:
                mismatching_instructions.append(rotor_curr)
                rotor_curr = rotor_reader.next_instruction()

            if len(mismatching_instructions) > 0:
                # Rotor had some instructions which RISC-V didn't have

                if rotor_curr.address == riscv_curr.address:  # Are we back on track?
                    # Yes => log warning and continue
                    Logger.problem("Found Rotor instructions without corresponding RISC-V instructions")
                    Logger.print_instruction_array(5, mismatching_instructions)
                    print()

                    continue
                else:
                    # No => seems like whole instruction set is mismatched. Log error and exit
                    Logger.error("Instruction sets are mismatched")
                    Logger.header("RISC-V")
                    print(riscv_curr)
                    Logger.header("Rotor")
                    Logger.print_instruction_array(5, [*mismatching_instructions, rotor_curr])

                    print()
                    Logger.error("Analysis stopped prematurely due to error", prefix="")
                    break

            # We are ready to check for instruction equality

            if riscv_curr != rotor_curr:
                Logger.problem("Instructions are not equal")
                Logger.inline_header(repr(riscv_curr), "RISC-V - ")
                Logger.inline_header(repr(rotor_curr), "ROTOR  - ")
                print()

        except EOFError:
            break


if __name__ == '__main__':
    main()

