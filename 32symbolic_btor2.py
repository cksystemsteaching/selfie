import os
directory = "examples/symbolic"

output_file = open("32symbolic_btor2.sh", "w")
for file in os.listdir(directory):
    path = f"{directory}/{file}"
    file_name = file.split(".")[0]
    heap_allowance = 4
    stack_allowance = 28
    extra_flags = "--constant-propagation --linear-address-space"
    output_file.write(f"./beator-32 -c {path} - 0 --heap-allowance {heap_allowance} --stack-allowance {stack_allowance} {extra_flags}\n")
    output_file.write(f"mv {directory}/{file_name}.btor2 32symbolic/{file_name}.btor2\n")
    output_file.write("\n")

output_file.close()