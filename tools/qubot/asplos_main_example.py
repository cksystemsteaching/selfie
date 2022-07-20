from bqm_input_checker import InputChecker
from btor2bqm import BTor2BQM
import os

directories = ['../../32fsm', '../../64fsm']
files_106_steps = ['base_ram', 'baseline', 'base_lin', 'base_mmu', 'base_mr', '12bad', '12bad_lin', '12bad_mmu', '12bad_ram', '12bad_mr']
assert(len(files_106_steps) == 10)

statistics_file = open(f"./main_experiment_statistics.csv", "w")
statistics_file.write("architecture,file,logic_variables,time")

for directory in directories:
    assert(len(os.listdir(directory)) == 20)
    directory_name = directory.split("/")[-1]
    c = 0
    for file in os.listdir(directory):
        print(f"{directory_name} - {file.split('.')[0]} ({c+1}/{len(os.listdir(directory))})")
        c+=1
        os.mkdir(f"./main_experiment_outputs/{directory_name}_{file.split('.')[0]}")

        log_file = open(f"./main_experiment_outputs/{directory_name}_{file.split('.')[0]}/log.txt", "w")
        log_file.write("architecture,file,logic_variables,time\n")

        if file.split('.')[0] in files_106_steps:
            print("building model for 106 state transitions")
            parser = BTor2BQM(106)
        else:
            print("building model for 37 state transitions")
            parser = BTor2BQM(37)
        _, total_time, num_variables = parser.parse_file(f"{directory}/{file}",
                          f"./main_experiment_outputs/{directory_name}_{file.split('.')[0]}/",
                          with_init=True, modify_memory_sort=True, log_file=log_file)
        statistics_file.write(f"{directory_name},{file.split('.')[0]},{num_variables},{total_time}\n")
        log_file.write("\n")
        for i in range(256):
            energy, bad_states = InputChecker.run_checker(f'./main_experiment_outputs/{directory_name}_{file.split(".")[0]}/', i)
            if i == 49:
                assert (energy == 0 and len(bad_states) == 1)
            else:
                assert (energy == 2 and len(bad_states) == 0)
            log_file.write(f"test for input {i}: {energy},{bad_states}\n")
        log_file.close()
    print()
statistics_file.close()
