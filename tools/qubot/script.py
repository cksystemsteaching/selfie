from bqm_input_checker import InputChecker
from btor2bqm import BTor2BQM

parser = BTor2BQM(15)
parser.parse_file(f"./btor2_running_example/32bit-example.btor2",
                  f"./temp_result/",
                  with_init=True, modify_memory_sort=True)

for i in range(256):
    print(f"{i}: ",InputChecker.run_checker("./temp_result/", i))
