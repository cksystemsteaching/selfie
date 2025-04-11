import subprocess
import time
import psutil
import logging

logger = logging.getLogger("bt.smt_benchmark")

def run_z3_on_model(model_path):
    start_time = time.time()  # Track start time

    # Running Z3 on the SMT model using subprocess
    process = subprocess.Popen(
        ['z3', model_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )

    stdout, stderr = process.communicate()  # Capture the output and error

    end_time = time.time()  # Track end time
    elapsed_time = end_time - start_time  # Total execution time

    # Return benchmark data, but do not print the full output by default
    return {
        'elapsed_time': elapsed_time,
        'output': stdout.decode(),
        'error': stderr.decode() if stderr else None
    }


def get_memory_usage():
    process = psutil.Process()
    mem_info = process.memory_info()
    return {
        'rss': mem_info.rss,  # Resident Set Size
        'vms': mem_info.vms   # Virtual Memory Size
    }


def benchmark_model(model_path, model_type='smt'):
    logger.info(f"Benchmarking {model_type} model: {model_path}")

    # Step 1: Run Z3 on the model and capture output
    benchmark_data = run_z3_on_model(model_path)

    # Step 2: Get memory usage during the run
    memory_usage = get_memory_usage()

    # Step 3: Output benchmark data
    logger.info(f"Execution time: {benchmark_data['elapsed_time']} seconds")
    logger.info(f"Memory usage (RSS): {memory_usage['rss']} bytes")
    logger.info(f"Memory usage (VMS): {memory_usage['vms']} bytes")
