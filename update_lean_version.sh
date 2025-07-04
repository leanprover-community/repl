#!/bin/bash

# Script to update Lean version
# Usage: ./update_lean_version.sh <new_version> [--skip-mathlib]
# Example: ./update_lean_version.sh v4.21.0
# Example: ./update_lean_version.sh v4.21.0 --skip-mathlib
#
# When --skip-mathlib is provided, the script will:
# - Skip running lake update in test/Mathlib
# - Comment out Mathlib tests in test.sh

set -e  # Exit immediately if a command exits with a non-zero status

SKIP_MATHLIB=false

if [[ "$#" -lt 1 || "$#" -gt 2 ]]; then
    echo "Usage: $0 <new_version> [--skip-mathlib]"
    echo "Example: $0 v4.21.0"
    echo "Example: $0 v4.21.0 --skip-mathlib"
    exit 1
fi

NEW_VERSION="$1"

if [[ "$#" -eq 2 && "$2" == "--skip-mathlib" ]]; then
    SKIP_MATHLIB=true
    echo "Mathlib tests will be skipped"
fi
echo "Updating Lean version to $NEW_VERSION"

# Update main lean-toolchain
echo "Updating main lean-toolchain..."
echo "leanprover/lean4:$NEW_VERSION" > lean-toolchain

# Update test/Mathlib/lean-toolchain if it exists
if [ -f "test/Mathlib/lean-toolchain" ]; then
    echo "Updating test/Mathlib/lean-toolchain..."
    echo "leanprover/lean4:$NEW_VERSION" > test/Mathlib/lean-toolchain
fi

# Update version in lakefile.toml
if [ -f "test/Mathlib/lakefile.toml" ]; then
    echo "Updating mathlib revision in test/Mathlib/lakefile.toml..."
    sed -i "s/rev = \"v[0-9]\+\.[0-9]\+\.[0-9]\+\(-[a-zA-Z0-9]\+\)*\"/rev = \"$NEW_VERSION\"/" test/Mathlib/lakefile.toml
fi

# Remove .lake folders
echo "Removing .lake folders..."
rm -rf .lake
rm -rf test/Mathlib/.lake

# Run lake update in test/Mathlib if we're not skipping Mathlib
if [ "$SKIP_MATHLIB" = false ] && [ -d "test/Mathlib" ]; then
    echo "Running lake update in test/Mathlib..."
    cd test/Mathlib
    lake update
    cd ../..
fi

# Build the project in the root folder
echo "Building project in root folder..."
lake build

# Modify test.sh based on --skip-mathlib option
echo "Updating test.sh file..."
if [ "$SKIP_MATHLIB" = true ]; then
    # Check if the line has already been marked as SKIPPED
    if grep -q "# Run the Mathlib tests - SKIPPED" test.sh; then
        # Already marked as SKIPPED, no need to change
        echo "Mathlib tests already marked as SKIPPED"
    else
        # Comment out the mathlib test lines if they are not already commented
        sed -i '/^# Run the Mathlib tests/ s/^# Run the Mathlib tests/# Run the Mathlib tests - SKIPPED/' test.sh
        sed -i '/^cp lean-toolchain test\/Mathlib\// s/^/# /' test.sh
        sed -i '/^cd test\/Mathlib\/ && .\/test.sh/ s/^/# /' test.sh
    fi
else
    # Uncomment the mathlib test lines if they are commented
    sed -i 's/^# Run the Mathlib tests - SKIPPED/# Run the Mathlib tests/' test.sh
    sed -i 's/^# cp lean-toolchain test\/Mathlib\//cp lean-toolchain test\/Mathlib\//' test.sh
    sed -i 's/^# cd test\/Mathlib\/ && .\/test.sh/cd test\/Mathlib\/ \&\& .\/test.sh/' test.sh
fi

# Run tests
echo "Running tests..."
lake exe test

echo "Lean version updated successfully to $NEW_VERSION!"
