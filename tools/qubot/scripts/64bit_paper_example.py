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
        #print(bias, error_states)
        string_errors = ""
        for error in error_states:
            if len(string_errors) == 0:
                string_errors = str(error)
            else:
                string_errors += f" {error}"
        file.write(f"{i},{bias},{string_errors}\n")
    file.close()
    return True

btor2files = {'12bad': 107,
              '12bad_c_lin': 37,
              '12bad_c_mmu': 37,
              '12bad_c_ram': 37,
              '12bad_const': 37,
              'baseline': 107,
              'const_lin': 37,
              'const_mmu': 37,
              'const_prop': 37,
              'const_ram': 37,
              'base_lin': 107,
              'base_ram': 107,
              '12bad_lin':107,
              '12bad_mmu': 107,
              '12bad_ram': 107,
              'base_mmu': 107,
              'base_mr': 107,
              'const_mr': 37,
              '12bad_mr': 107,
              '12bad_c_mr': 37
            }



for btor2file in btor2files.keys():
    parser = BTor2BQM(btor2files[btor2file])
    parser.parse_file(f"../b64bit_btor2_files/{btor2file}.btor2",
                      f"../paper_results/{btor2file}/",
                      with_init=True, modify_memory_sort=True)
    run_input_checker(f"./paper_results/{btor2file}/")

