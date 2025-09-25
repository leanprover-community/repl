#!/bin/bash

# Define the paths
IN_DIR="test"
EXPECTED_DIR="test"

# Initialize variables to track failures
failed_tests=()
failure_count=0

lake exe cache get > /dev/null
lake build Mathlib

# Iterate over each .in file in the test directory
for infile in $IN_DIR/*.in; do
    # Extract the base filename without the extension
    base=$(basename "$infile" .in)

    # Define the path for the expected output file
    expectedfile="$EXPECTED_DIR/$base.expected.out"

    # Check if the expected output file exists
    if [[ ! -f $expectedfile ]]; then
        echo "Expected output file $expectedfile does not exist. Skipping $infile."
        continue
    fi

    # Run the command and store its output in a temporary file
    tmpfile=$(mktemp)
    lake env ../../.lake/build/bin/repl < "$infile" > "$tmpfile" 2>&1

    # Compare the output with the expected output
    if diff "$tmpfile" "$expectedfile"; then
        echo "$base: PASSED"
        # Remove the temporary file
        rm "$tmpfile"
    else
        echo "$base: FAILED"
        # Rename the temporary file instead of removing it
        mv "$tmpfile" "${expectedfile/.expected.out/.produced.out}"
        failed_tests+=("$base")
        ((failure_count++))
    fi
done

# Print summary of failures
if [ ${#failed_tests[@]} -ne 0 ]; then
    echo -e "\n=== Mathlib Test Summary ==="
    echo "Failed tests:"
    for test in "${failed_tests[@]}"; do
        echo "✗ $test"
    done
    echo -e "\nTotal: $failure_count failed"
    echo "========================"
    exit 1
fi

exit 0
