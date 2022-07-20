from bqm_input_checker import InputChecker
from btor2bqm import BTor2BQM
import os

directories = ['../../32symbolic_nomem',
               '../../64symbolic_nomem']
target_files = {
'../../32symbolic_nomem' : ['division-by-zero-3-35.btor2'
    ,'memory-access-fail-1-35.btor2', 'nested-if-else-1-35.btor2',
                'nested-if-else-reverse-1-35.btor2', 'recursive-ackermann-1-35.btor2', 'recursive-factorial-fail-1-35.btor2',
                'recursive-fibonacci-1-10.btor2', 'return-from-loop-1-35.btor2', 'simple-assignment-1-35.btor2',
                'simple-if-else-1-35.btor2', 'simple-if-else-reverse-1-35.btor2', 'simple-if-without-else-1-35.btor2', 'u.btor2'
],
    '../../64symbolic_nomem' : ['division-by-zero-3-35.btor2'
        ,'memory-access-fail-1-35.btor2', 'nested-if-else-1-35.btor2',
                'nested-if-else-reverse-1-35.btor2', 'recursive-ackermann-1-35.btor2', 'recursive-factorial-fail-1-35.btor2',
                'recursive-fibonacci-1-10.btor2', 'return-from-loop-1-35.btor2', 'simple-assignment-1-35.btor2',
                'simple-if-else-1-35.btor2', 'simple-if-else-reverse-1-35.btor2', 'simple-if-without-else-1-35.btor2', 'u.btor2',
                 'invalid-memory-access-fail-2-35.btor2', 'nested-recursion-fail-1-35.btor2'
                          ]

}

timesteps ={
    '../../32symbolic_nomem' : [16
        ,0, 51, 50, 41, 50, 52, 35, 31, 45, 43, 44, 14
    ],
    '../../64symbolic_nomem': [16
        ,0, 51, 50, 38, 35, 35, 35, 31, 45, 43, 44, 14, 19, 31
    ]
}
# assert(len(target_files['../../32symbolic']) == 13-1)
# assert(len(target_files['../../64symbolic']) == 13-1 + 2)

assert(len(target_files['../../32symbolic_nomem']) == len(timesteps['../../32symbolic_nomem']))
assert(len(target_files['../../64symbolic_nomem']) == len(timesteps['../../64symbolic_nomem']))

statistics_file = open(f"./symbolicnomem_experiment_statistics.csv", "w")
statistics_file.write("architecture,file,logic_variables,time\n")

for directory in directories:
    directory_name = directory.split("/")[-1]
    c = 0
    for (index, file) in enumerate(target_files[directory]):
        print(f"{directory_name} - {file.split('.')[0]} ({c+1}/{len(target_files[directory])})")
        c+=1
        os.mkdir(f"./symbolicnomem_experiment_outputs/{directory_name}_{file.split('.')[0]}")

        log_file = open(f"./symbolicnomem_experiment_outputs/{directory_name}_{file.split('.')[0]}/log.txt", "w")
        log_file.write("architecture,file,logic_variables,time\n")


        parser = BTor2BQM(timesteps[directory][index]+1)
        _, total_time, num_variables = parser.parse_file(f"{directory}/{file}",
                          f"./symbolicnomem_experiment_outputs/{directory_name}_{file.split('.')[0]}/",
                          with_init=True, modify_memory_sort=True, log_file=log_file)
        statistics_file.write(f"{directory_name},{file.split('.')[0]},{num_variables},{total_time}\n")
        log_file.write("\n")
        energy_0_found = False
        for i in range(256):
            energy, bad_states = InputChecker.run_checker(f'./symbolicnomem_experiment_outputs/{directory_name}_{file.split(".")[0]}/', i)
            if energy == 0:
                energy_0_found = True
            log_file.write(f"test for input {i}: {energy},{bad_states}\n")

        if not energy_0_found:
            raise Exception("no input causes bad states")
        log_file.close()
    print()
statistics_file.close()
