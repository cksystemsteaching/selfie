btor2files_32 = {
    '32const_mr': 37,'32_12bad_c_mr': 37,'32_12bad_c_lin': 37,'32_12bad_c_mmu': 37,'32_12bad_c_ram': 37,
    '32_12bad_const': 37, '32const_lin': 37, '32const_mmu': 37, '32const_prop': 37, '32const_ram': 37,
}

btor2files_64 = {
    '12bad_c_lin': 37, '12bad_c_mmu': 37, '12bad_c_ram': 37, '12bad_const': 37, 'const_lin': 37,
    'const_mmu': 37, 'const_prop': 37, 'const_ram': 37, 'const_mr': 37, '12bad_c_mr': 37
}


file = open("./qubit_growth.csv", "w")
file.write("file,n,qubits\n")

from btor2bqm import BTor2BQM

for (btor2, timesteps) in btor2files_32.items():
    parser = BTor2BQM(80)
    parser.parse_file(f"./32bit_running_examples/{btor2}.btor2", "./temp/", with_init=True, modify_memory_sort=True, qubit_growth_file=file)

for (btor2, timesteps) in btor2files_64.items():
    parser = BTor2BQM(80)
    parser.parse_file(f"./btor2_running_example/{btor2}.btor2", "./temp/", with_init=True, modify_memory_sort=True, qubit_growth_file=file)
