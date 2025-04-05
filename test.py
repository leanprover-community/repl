from datasets import load_dataset
import json
import subprocess
import time

header = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"
# Login using e.g. `huggingface-cli login` to access this dataset
ds = load_dataset("Goedel-LM/Lean-workbook-proofs")

proofs = []

for data in ds["train"].select(range(1000)):
    proof = data["full_proof"].split(header)[1]
    proofs.append(proof)
    print(header, proof)

# batchCmd = { "header": header, "proofs": proofs}
# tmp = json.dumps(batchCmd)

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

# # Write input directly to the process
process.stdin.write(json.dumps({"header" : header, "proofs": proofs}) + "\n")
process.stdin.flush()
# process.stdin.write(json.dumps({ "cmd" : header}) + "\n\n")
# process.stdin.flush()
# for proof in proofs:
#     process.stdin.write(json.dumps({ "cmd" : proof, "env" : 0}) + "\n\n")
#     process.stdin.flush()  # Ensure it's sent immediately

# Read output
stdout, stderr = process.communicate()

# Print results
print("STDOUT:", stdout)
print("STDERR:", stderr)

repl_time = time.time() - start_repl_time
print(f"REPL execution completed in {repl_time:.2f} seconds.")