import subprocess
import time
import os
import seaborn as sns
import matplotlib.pyplot as plt
import numpy as np

LEVEL = 8
SWITCH = 8
FORK = 8

TIMEOUT = 200

MODEL_PATH = "cflobvdd64.btor2"



times = np.zeros((SWITCH, FORK))
for i in range(0, SWITCH, 2):
	for j in range(0, FORK, 2):
		try:
			cmnd = f"tools/bitme.py {MODEL_PATH} -array 9 -kmin 0 --check-termination --unroll -propagate 8 --use-CFLOBVDD {j} {i} {LEVEL}"
			strt_time = time.time()
			bitme = subprocess.run(cmnd.split(), capture_output=True, text=True, timeout=TIMEOUT)
			end_time = time.time()
			elapsed_time = end_time-strt_time
			print()
			print(cmnd, " : ", elapsed_time)
			times[i, j] = elapsed_time
		except:
			print(f"error for fork={j} and switch={i}")
			times[i, j] = 0



sns.heatmap(times, annot=True, fmt=".2f", cmap="Blues", vmin=0)
#plt.colorbar(label="Value")
plt.title("Rutime based on switch and fork heights (s)")
plt.xlabel("Fork Height")
plt.ylabel("Switch Height")
plt.tight_layout()
plt.savefig("plot.png")






















"""
./rotor -m64 -c examples/symbolic/cflobvdd.c -o cflobvdd64.m - 1 -o cflobvdd64.btor2

tools/bitme.py cflobvdd64.btor2 -array 9 -kmin 0 --check-termination --unroll -propagate 8 --use-CFLOBVDD 0 1 7
"""