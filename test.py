from datasets import load_dataset
import json
import subprocess
import time
import psutil

header = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
# Login using e.g. `huggingface-cli login` to access this dataset
ds = load_dataset("Goedel-LM/Lean-workbook-proofs")

proofs = []

for data in ds["train"].select(range(8)):
    proof = data["full_proof"].split(header)[1]
    proofs.append(proof)
    # print(header, proof)

print("done loading")

start_repl_time = time.time()

process = subprocess.Popen(
    ["lake", "env", "../../.lake/build/bin/repl"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,   # Makes it work with strings
    encoding="utf-8"
)

p = psutil.Process(process.pid)

process.stdin.write(json.dumps({"cmd": header}) + "\n\n")
process.stdin.flush()
while True:
    line = process.stdout.readline().strip()
    if not line:
        break

print("loadded header")

for i in range(5):
    start = time.time()

    # # Write input directly to the process
    process.stdin.write(json.dumps({"env": 0, "cmd": proofs[0]}) + "\n\n")
    process.stdin.flush()

    output_lines = []
    while True:
        line = process.stdout.readline().strip()
        if not line:
            break
        output_lines.append(line)

    stdout = "\n".join(output_lines)
    # print(stdout)

    end = time.time()

    # Monitor memory in MB
    mem_info = p.memory_info()
    memory_mb = mem_info.rss / (1024 ** 2)

    print(f"[{i}] Time Cmd: {end - start:.2f}s, Memory: {memory_mb:.2f} MB")

    # ----------------------------------
    start = time.time()

    # # Write input directly to the process
    process.stdin.write(json.dumps({"env": 0, "cmd": proofs[0], "gc": True}) + "\n\n")
    process.stdin.flush()

    output_lines = []
    while True:
        line = process.stdout.readline().strip()
        if not line:
            break
        output_lines.append(line)

    stdout = "\n".join(output_lines)
    # print(stdout)

    end = time.time()

    # Monitor memory in MB
    mem_info = p.memory_info()
    memory_mb = mem_info.rss / (1024 ** 2)

    print(f"[{i}] Time Cmd GC: {end - start:.2f}s, Memory: {memory_mb:.2f} MB")

    # ----------------------------------

    start = time.time()

    # # Write input directly to the process
    process.stdin.write(json.dumps({"env": 0, "cmds": proofs, "mode": "naive",  "timeout": 60000}) + "\n\n")
    process.stdin.flush()

    output_lines = []
    while True:
        line = process.stdout.readline().strip()
        if not line:
            break
        output_lines.append(line)

    stdout = "\n".join(output_lines)
    # print(stdout)

    end = time.time()

    # Monitor memory in MB
    mem_info = p.memory_info()
    memory_mb = mem_info.rss / (1024 ** 2)

    print(f"[{i}] Time Batch: {end - start:.2f}s, Memory: {memory_mb:.2f} MB")

process.stdin.close()
process.wait()
