from os import listdir
from os.path import isfile, join
path = "./test_files/"
for f in listdir(path):
    if isfile(join(path, f)):
        file_name = f.split(".")[0]
        print(f"python main.py 1 {join(path, f)} ./qasm_files/{file_name}.qasm")