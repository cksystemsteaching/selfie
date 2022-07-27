import os

directory = "examples/symbolic"

for file in os.listdir(directory):
    path = f"{directory}/{file}"
    file_name = file.split(".")[0]
    heap_allowance = 0
    stack_allowance = 0
    extra_flags = "--constant-propagation --linear-address-space --MMURAM"
    exit_code = os.system(f"./beator -c {path} - 0 --heap-allowance {heap_allowance} --stack-allowance {stack_allowance} {extra_flags}")
    assert(exit_code == 0)
    exit_code = os.system(f"mv {directory}/{file_name}.btor2 64symbolic_nomem/{file_name}.btor2")
    assert(exit_code == 0)