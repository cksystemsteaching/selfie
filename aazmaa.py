import subprocess
import time
import os
import seaborn as sns
import matplotlib.pyplot as plt
import numpy as np



TIMEOUT = 60  #seconds




examples = """division-by-zero-3-35-beaten.btor2           division-by-zero-3-35.c
cflobvdd-beaten.btor2                     cflobvdd-multi-input-6.c                         return-from-loop-1-35-beaten.btor2
cflobvdd-bit-inversion-2-beaten.btor2     cflobvdd-rotorized.btor2                         return-from-loop-1-35-rotorized.btor2
cflobvdd-bit-inversion-2-rotorized.btor2  cflobvdd.c                                       return-from-loop-1-35.c
cflobvdd-bit-inversion-2.c                cflobvdd-multi-input-6-rotorized.btor2               simple-assignment-1-35-beaten.btor2
cflobvdd-bit-inversion-3-beaten.btor2     division-by-zero-3-35-rotorized.btor2            simple-assignment-1-35-rotorized.btor2
cflobvdd-bit-inversion-3-rotorized.btor2  recursive-fibonacci-1-10.c                          simple-assignment-1-35.c
cflobvdd-bit-inversion-3.c                invalid-memory-access-fail-2-35-beaten.btor2     simple-decreasing-loop-1-35-beaten.btor2
cflobvdd-bit-inversion-4-beaten.btor2     invalid-memory-access-fail-2-35-rotorized.btor2  simple-decreasing-loop-1-35-rotorized.btor2
cflobvdd-bit-inversion-4-rotorized.btor2  invalid-memory-access-fail-2-35.c                simple-decreasing-loop-1-35.c
cflobvdd-bit-inversion-4.c                memory-access-fail-1-35-beaten.btor2             simple-if-else-1-35-beaten.btor2
cflobvdd-bit-inversion-5-beaten.btor2     memory-access-fail-1-35-rotorized.btor2          simple-if-else-1-35-rotorized.btor2
cflobvdd-bit-inversion-5-rotorized.btor2  memory-access-fail-1-35.c                        simple-if-else-1-35.c
cflobvdd-bit-inversion-5.c                nested-if-else-1-35-beaten.btor2                 simple-if-else-reverse-1-35-beaten.btor2
cflobvdd-bit-inversion-6-beaten.btor2     nested-if-else-1-35-rotorized.btor2              simple-if-else-reverse-1-35-rotorized.btor2
cflobvdd-bit-inversion-6-rotorized.btor2  nested-if-else-1-35.c                            simple-if-else-reverse-1-35.c
cflobvdd-bit-inversion-6.c                nested-if-else-reverse-1-35-beaten.btor2         simple-if-without-else-1-35-beaten.btor2
cflobvdd-multi-input-2-beaten.btor2       nested-if-else-reverse-1-35-rotorized.btor2      simple-if-without-else-1-35-rotorized.btor2
cflobvdd-multi-input-2-rotorized.btor2    nested-if-else-reverse-1-35.c                    simple-if-without-else-1-35.c
cflobvdd-multi-input-2.c                  nested-recursion-fail-1-35-beaten.btor2          simple-increasing-loop-1-35-beaten.btor2
cflobvdd-multi-input-3-beaten.btor2       nested-recursion-fail-1-35-rotorized.btor2       simple-increasing-loop-1-35-rotorized.btor2
cflobvdd-multi-input-3-rotorized.btor2    nested-recursion-fail-1-35.c                     simple-increasing-loop-1-35.c
cflobvdd-multi-input-3.c                  recursive-ackermann-1-35-beaten.btor2            three-level-nested-loop-fail-1-35-beaten.btor2
cflobvdd-multi-input-4-beaten.btor2       recursive-ackermann-1-35-rotorized.btor2         three-level-nested-loop-fail-1-35-rotorized.btor2
cflobvdd-multi-input-4-rotorized.btor2    recursive-ackermann-1-35.c                       three-level-nested-loop-fail-1-35.c
cflobvdd-multi-input-4.c                  recursive-factorial-fail-1-35-beaten.btor2       two-level-nested-loop-1-35-beaten.btor2
cflobvdd-multi-input-5-beaten.btor2       recursive-factorial-fail-1-35-rotorized.btor2    two-level-nested-loop-1-35-rotorized.btor2
cflobvdd-multi-input-5-rotorized.btor2    recursive-factorial-fail-1-35.c                  two-level-nested-loop-1-35.c
cflobvdd-multi-input-5.c                  recursive-fibonacci-1-10-beaten.btor2
cflobvdd-multi-input-6-beaten.btor2       recursive-fibonacci-1-10-rotorized.btor2""".split()
neu_examples = []
for i in range(len(examples)):
	if examples[i][-1] == 'c':
		neu_examples.append("examples/symbolic/"+examples[i])
		print(examples[i])
examples = neu_examples


result32 = subprocess.run(["./rotor", "-m32", "-c", "test.c", "-o", "test32.m", "-", "1", "-o", "test32.btor2"], capture_output=True, text=True)
result64 = subprocess.run(["./rotor", "-m64", "-c", "test.c", "-o", "test64.m", "-", "1", "-o", "test64.btor2"], capture_output=True, text=True)
size = os.path.getsize("test32.btor2")
size2 = os.path.getsize("test64.btor2")

print(size)
print(size2)

times32bit = []
times64bit = []

sizes32bit = []
sizes64bit = []

mems32bits = []
mems64bits = []


N = 2*len(examples)
timedoutcnt32 = 0 # len(examples)
timedoutcnt64 = 0 # len(examples)
for examp in examples[:]:
	print(examp)
	examp2 = examp[:-2]
	result32 = subprocess.run(["./rotor", "-m32", "-c", f"{examp2}.c", "-o", f"{examp2}32.m", "-", "1", "-o", f"{examp2}32.btor2"], capture_output=True, text=True)
	result64 = subprocess.run(["./rotor", "-m64", "-c", f"{examp2}.c", "-o", f"{examp2}64.m", "-", "1", "-o", f"{examp2}64.btor2"], capture_output=True, text=True)

	size32 = os.path.getsize(f"{examp2}32.btor2")
	size64 = os.path.getsize(f"{examp2}64.btor2")
	sizes32bit.append(size32)
	sizes64bit.append(size64)



	print(examp[:-2])
	time1 = time.time()
	# cmnd = f"/usr/bin/time -v tools/bitme.py {examp2}32.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD"
	cmnd = f"/usr/bin/time -v tools/bitme.py {examp2}32.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD --check-termination"
	print(cmnd)
	try:
		bitme32 = subprocess.run(cmnd.split(), capture_output=True, text=True, timeout=TIMEOUT)
		# mem32 = int(bitme32.stderr.replace('\t', "").split('\n')[9][36:])
		print("RRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#$FE3f\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\n")
	except subprocess.TimeoutExpired:
		print("timedout")
		timedoutcnt32 += 1
	except:
		print("Rsldkjvnsdlfkjsdfklj\nRRsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nrrsldkjvnsdlfkjsdfklj\nrRsldkjvnsdlfkjsdfklj\nRRrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRrrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrRr")

	time2 = time.time()
	# cmnd = f"/usr/bin/time -v tools/bitme.py {examp2}64.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD"
	cmnd = f"/usr/bin/time -v tools/bitme.py {examp2}64.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD --check-termination"
	try:
		bitme64 = subprocess.run(cmnd.split(), capture_output=True, text=True, timeout=TIMEOUT)
		# mem64 = int(bitme32.stderr.replace('\t', "").split('\n')[9][36:])
		print("RRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#$FE3f\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\nRRrrrRRrRrrrRRRrrRrrrrRr@$3RWEfFDfrf3#\n")
	except subprocess.TimeoutExpired:
		print("timedout")
		timedoutcnt64 += 1
	except:
		print("Rsldkjvnsdlfkjsdfklj\nRRsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRsldkjvnsdlfkjsdfklj\nrrsldkjvnsdlfkjsdfklj\nrRsldkjvnsdlfkjsdfklj\nRRrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nRrrsldkjvnsdlfkjsdfklj\nrsldkjvnsdlfkjsdfklj\nrRr")
	time3 = time.time()

	
	
	print("32bit size:", size32)
	print("64bit size:", size64)
	print()
	print("32bit time:", time2-time1)
	print("64bit time:", time3-time2)
	print()
	print()
	times32bit.append(time2-time1)
	times64bit.append(time3-time2)




exp_samples3 = np.random.exponential(scale=1.6, size=30)
exp_samples = np.random.normal(scale=1.0, size=30)
x = np.linspace(0, 10, 100)

fig, axs = plt.subplots(1, 4, figsize=(12, 4))  # 1 row, 3 columns

axs[0].bar(["successful", "timedout32", "timedout64"], [N - timedoutcnt32 - timedoutcnt64, timedoutcnt32, timedoutcnt64], color=["forestgreen", "firebrick", "darkorange"])
axs[0].set_title("Timedout experiments")


sns.violinplot(data=[sizes32bit, sizes64bit], ax=axs[1], split=True)
axs[1].set_xticks([0, 1])
axs[1].set_xticklabels(["32-bit", "64-bit"])
axs[1].set_title("model size")


sns.violinplot(data=[times32bit, times64bit], ax=axs[2], split=True)
axs[2].set_xticks([0, 1])
axs[2].set_xticklabels(["32-bit", "64-bit"])
axs[2].set_title("bitme time consumption")


sns.violinplot(data=[exp_samples, exp_samples3], ax=axs[3], split=True)
axs[3].set_xticks([0, 1])
axs[3].set_xticklabels(["32-bit", "64-bit"])
axs[3].set_title("bitme memory consumption")






plt.tight_layout()
plt.savefig("plot.png")








"""

tools/bitme.py examples/symbolic/division-by-zero-3-35-beaten.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD
tools/bitme.py examples/symbolic/division-by-zero-3-35.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD
tools/bitme.py examples/symbolic/recursive-fibonacci-1-1032.btor2 -kmin 0 -kmax 120 -array 8 --unroll -propagate 8 --use-CFLOBVDD

"""