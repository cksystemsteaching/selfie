from bqm_input_checker import InputChecker
from btor2bqm import BTor2BQM

parser = BTor2BQM(15)
print(parser.parse_file(f"../../64symbolic/u.btor2",
                  f"./temp_result/",
                  with_init=True, modify_memory_sort=True))

for i in range(256):
    print(f"{i}: ",InputChecker.run_checker("./temp_result/", i))
