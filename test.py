from datasets import load_dataset
import json
import subprocess
import time

header = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
# Login using e.g. `huggingface-cli login` to access this dataset
ds = load_dataset("Goedel-LM/Lean-workbook-proofs")

proofs = []

for data in ds["train"].select(range(2000)):
    proof = data["full_proof"].split(header)[1]
    proofs.append(proof)
    print(header, proof)

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

start = time.time()

process.stdin.write(json.dumps({"cmd": header}) + "\n\n")

# # Write input directly to the process
process.stdin.write(json.dumps({"env": 0, "proofs": proofs, "mode": "parrallel", "buckets": 50}) + "\n\n")
process.stdin.flush()

stdout, stderr = process.communicate()

end = time.time()

# Print results
print("STDOUT:", stdout)
print("STDERR:", stderr)

print("time: ", end - start)
