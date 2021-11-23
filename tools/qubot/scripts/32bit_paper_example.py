from bqm_input_checker import InputChecker
from btor2bqm import BTor2BQM

def run_input_checker(path):
    print(f"running input checker ({path})")
    file = open(f"{path}result.csv", "w")
    file.write("input, bias, error_states\n")
    for i in range(0, 256):
        #print("running input:",i)
        bias, error_states = InputChecker.run_checker(path, i)
        if bias < 0:
            print(f"FAIL: test failed for ({path})")
            return False
        if i != 49:
            if bias == 0:
                print(f"FAIL: {path} non zero energy for input={i}")
                return False
        else:
            if bias != 0:
                print(f"FAIL: {path} gives non zero energy for correct input")
                return False
        string_errors = ""
        for error in error_states:
            if len(string_errors) == 0:
                string_errors = str(error)
            else:
                string_errors += f" {error}"
        file.write(f"{i},{bias},{string_errors}\n")
    file.close()
    return True

btor2files = {
               '32base_mr': 107,
                '32const_mr': 37,
               '32_12bad_mr':107,
                '32_12bad_c_mr': 37,
                '32_12bad': 107,
               '32_12bad_c_lin': 37,
               '32_12bad_c_mmu': 37,
               '32_12bad_c_ram': 37,
               '32_12bad_const': 37,
               '32baseline': 107,
               '32const_lin': 37,
               '32const_mmu': 37,
               '32const_prop': 37,
               '32const_ram': 37,
               '32base_lin': 107,
               '32base_ram': 107,
               '32_12bad_lin':107,
               '32_12bad_mmu': 107,
               '32_12bad_ram': 107,
                '32base_mmu': 107
            }



for btor2file in btor2files.keys():
    parser = BTor2BQM(btor2files[btor2file])
    parser.parse_file(f"./32bit_running_examples/{btor2file}.btor2",
                      f"./32_bit_results/{btor2file}/",
                      with_init=True, modify_memory_sort=True)
    run_input_checker(f"./32_bit_results/{btor2file}/")

