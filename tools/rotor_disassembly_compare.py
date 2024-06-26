#!/usr/bin/env python3

# This script is used to compare objdump outputs of Rotor and RISC-V


import re
import subprocess
from abc import abstractmethod
from typing import Callable
from argparse import ArgumentParser


# noinspection PyClassHasNoInit
class Logger:
    # noinspection PyClassHasNoInit
    class Colors:
        RESET = "\033[0m"
        RED = "\033[31m"
        GREEN = "\033[32m"
        YELLOW = "\033[33m"
        BLUE = "\033[34m"
        PURPLE = "\033[35m"
        CYAN = "\033[36m"
        WHITE = "\033[37m"
        GRAY = "\033[90m"

    @staticmethod
    def debug(message: str, after=""):
        Logger.__log_colored(Logger.Colors.GRAY, message + Logger.Colors.RESET + after)

    @staticmethod
    def info(message: str):
        Logger.__log_colored(Logger.Colors.RESET, message)

    @staticmethod
    def error(message: str, after=""):
        Logger.__log_colored(Logger.Colors.RED, message + Logger.Colors.RESET + after)

    @staticmethod
    def warning(message: str, after=""):
        Logger.__log_colored(Logger.Colors.YELLOW, message + Logger.Colors.RESET + after)

    @staticmethod
    def success(message: str, after=""):
        Logger.__log_colored(Logger.Colors.GREEN, message + Logger.Colors.RESET + after)

    @staticmethod
    def header(message: str, after=""):
        Logger.__log_colored(Logger.Colors.BLUE, message + Logger.Colors.RESET + after)

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
    def __log_colored(color: str, message: str, color_end=Colors.RESET):
        print(f"{color}{message}{color_end}")


class Instruction:
    # noinspection PyClassHasNoInit
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
        return Instruction.__create(instruction, Instruction.Source.RISCV, r"\s+([\da-f]+):\s+[\da-f]+\s+([\w.]*)(?:\s+([\w,()\-]*))?(.*?)(?:\r?\n|$)")

    @staticmethod
    def from_rotor(instruction: str) -> "Instruction":
        return Instruction.__create(instruction, Instruction.Source.ROTOR, r"0x([\da-f]+):\s+([\w.]*)(?:\s+([\w,()\-]*))?(.*?)(?:\r?\n|$)")

    @staticmethod
    def __create(instruction: str, source: str, regex: str):
        match = re.match(regex, instruction, re.IGNORECASE)
        if not match:
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


class CodeReader:
    def __init__(self, instruction_class: Callable[[str], Instruction]):
        self.instruction_class = instruction_class
        self.__peek: Instruction | None = None

    def peek_instruction(self) -> Instruction:
        if self.__peek is None:
            self.__peek = self._actual_next_instruction()
        return self.__peek

    def next_instruction(self) -> Instruction:
        if self.__peek is not None:
            next_instruction = self.__peek
            self.__peek = None
            return next_instruction
        return self._actual_next_instruction()

    @abstractmethod
    def _actual_next_instruction(self) -> Instruction:
        pass


class StdoutReader(CodeReader):
    def __init__(self, stdout: str, instruction_class: Callable[[str], Instruction]):
        super().__init__(instruction_class)
        self.iterator = iter(stdout.splitlines())

    def _actual_next_instruction(self) -> Instruction:
        while True:
            try:
                line = next(self.iterator)
                return self.instruction_class(str(line))
            except StopIteration:
                raise EOFError("End of output")
            except ValueError:
                continue


class FileReader(CodeReader):
    def __init__(self, file_path, instruction_class: Callable[[str], Instruction]):
        super().__init__(instruction_class)
        self.file = open(file_path, "r")

    def _actual_next_instruction(self) -> Instruction:
        while True:
            if (line := self.file.readline()) == "":
                raise EOFError("End of file")
            try:
                return self.instruction_class(str(line))
            except ValueError:
                continue


def parse_args():
    argparser = ArgumentParser()
    argparser.add_argument("-s", "--rotor-path", dest="rotor_path", default="./rotor;./tools/rotor;../rotor", help="Path to the Rotor executable (multiple paths can be provided, first one that exists will be used)")
    argparser.add_argument("-r", "--riscv-path", dest="riscv_path", default="riscv64-unknown-elf-objdump", help="Path to the RISC-V objdump executable")
    argparser.add_argument(dest="in_file", help="Input binary")
    return argparser.parse_args()


def main():
    args = parse_args()

    Logger.debug("Dumping assembly using RISC-V at path " + args.riscv_path)

    try:
        riscv_output = subprocess.run([args.riscv_path, "-d", args.in_file], capture_output=True, text=True)
    except FileNotFoundError:
        Logger.error("RISC-V objdump executable not found")
        return

    if riscv_output.returncode != 0:
        Logger.error("RISC-V objdump failed")
        print(riscv_output.stderr)
        return

    rotor_paths = args.rotor_path.split(";")
    rotor_output = None

    for rotor_path in rotor_paths:
        Logger.debug("Trying to dump assembly using Rotor at path " + rotor_path)

        try:
            rotor_output = subprocess.run([rotor_path, "-l", args.in_file, "-", "0", "-s"], capture_output=True, text=True)
            break
        except FileNotFoundError:
            Logger.debug("Rotor executable not found at path " + rotor_path)
            continue

    if rotor_output is None:
        Logger.error("Rotor executable not found")
        return

    if rotor_output.returncode != 0:
        Logger.error("Rotor failed")
        print(rotor_output.stderr)
        print(rotor_output.stdout)
        return

    riscv_reader = StdoutReader(riscv_output.stdout, Instruction.from_riscv)
    rotor_reader = StdoutReader(rotor_output.stdout, Instruction.from_rotor)

    compare_objdump(riscv_reader, rotor_reader)


def compare_objdump(riscv_reader: CodeReader, rotor_reader: CodeReader):
    at_start = True
    num_missing_instruction_set = 0
    num_mismatched_opcode = 0
    num_mismatched_operands = 0

    Logger.info("Comparing instructions...")

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
                    num_missing_instruction_set += 1
                    Logger.warning("PROBLEM: Found RISC-V instructions without corresponding Rotor instructions:")
                    Logger.print_instruction_array(5, mismatching_instructions)
                    print()

                    continue
                else:
                    # No => seems like whole instruction set is mismatched. Log error and exit
                    Logger.error("ERROR: Instruction sets are mismatched")
                    Logger.header("===== RISC-V =====")
                    Logger.print_instruction_array(5, [*mismatching_instructions, riscv_curr])
                    Logger.header("===== Rotor =====")
                    print(rotor_curr)

                    print()
                    Logger.error("Analysis stopped prematurely due to error")
                    break

            while riscv_curr.address > rotor_curr.address:
                mismatching_instructions.append(rotor_curr)
                rotor_curr = rotor_reader.next_instruction()

            if len(mismatching_instructions) > 0:
                # Rotor had some instructions which RISC-V didn't have

                if rotor_curr.address == riscv_curr.address:  # Are we back on track?
                    # Yes => log warning and continue

                    if at_start:
                        Logger.debug(f"NOTICE: Found erroneously decompiled Rotor instructions potentially outside of .text segment: {hex(mismatching_instructions[0].address)} - {hex(rotor_curr.address)}")
                    else:
                        num_missing_instruction_set += 1
                        Logger.warning("PROBLEM: Found Rotor instructions without corresponding RISC-V instructions")
                        Logger.print_instruction_array(5, mismatching_instructions)
                        print()

                    continue
                else:
                    # No => seems like whole instruction set is mismatched. Log error and exit
                    Logger.error("Instruction sets are mismatched")
                    Logger.header("===== RISC-V =====")
                    print(riscv_curr)
                    Logger.header("===== Rotor =====")
                    Logger.print_instruction_array(5, [*mismatching_instructions, rotor_curr])

                    print()
                    Logger.error("Analysis stopped prematurely due to error")
                    break

            # We are ready to check for instruction equality

            if riscv_curr.instruction != rotor_curr.instruction:
                # Opcode is different, this might indicate an unimplemented instruction or pseudoinstruction, or an unhandled compressed instruction
                num_mismatched_opcode += 1
                Logger.warning("PROBLEM: Instructions are not equal")
                Logger.header("RISC-V - ", repr(riscv_curr))
                Logger.header("ROTOR  - ", repr(rotor_curr))
                print()
            elif riscv_curr != rotor_curr:
                # Opcode is the same but operands are different, this is 100% a bug in Rotor operand printing!
                num_mismatched_operands += 1
                Logger.warning("PROBLEM: Operands are not equal")
                Logger.header("RISC-V - ", repr(riscv_curr))
                Logger.header("ROTOR  - ", repr(rotor_curr))
                print()

            at_start = False

        except EOFError:
            Logger.info("Disassembly comparison finished")

            num_problems = num_missing_instruction_set + num_mismatched_opcode + num_mismatched_operands
            if num_problems == 0:
                Logger.success("No problems found! 🎉")
            else:
                Logger.error(f"Found {num_problems} problems:")
                Logger.error(f"  - Missing instruction sets: {num_missing_instruction_set}")
                Logger.error(f"  - Mismatched instructions: {num_mismatched_opcode}")
                Logger.error(f"  - Mismatched operands with identical instructions: {num_mismatched_operands}")

            break


if __name__ == '__main__':
    main()
