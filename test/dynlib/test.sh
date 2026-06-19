#!/bin/bash

set -e

REPL_BIN="../../.lake/build/bin/repl"
DYNLIB_PATH="lib/libmylib.so"
INPUT_FILE="success.in"

echo "Running test with dynamic library: $DYNLIB_PATH"

# Create a temp file for output
tmpfile=./dynlib.out

# Run REPL with dynlib and input, dump output to temp file
lake env "$REPL_BIN" --dynlib "$DYNLIB_PATH" < "$INPUT_FILE" > "$tmpfile" 2>&1

cat "$tmpfile"

# Optionally remove temp file (comment out if you want to keep)
# rm "$tmpfile"
