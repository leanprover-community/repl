#!/usr/bin/env bash

# Script to push stg commits one by one and find the first failing commit

set -e # Exit on error

# Store original state to restore at the end if needed
ORIGINAL_COMMIT=$(git rev-parse --abbrev-ref HEAD)
STG_INITIAL_TOP=$(stg top 2>/dev/null || echo "")

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
NC='\033[0m' # No Color

# Get all unpushed patches
PATCHES=$(stg series | grep '^-' | cut -c 2- || echo "")

if [[ -z "$PATCHES" ]]; then
    echo -e "${YELLOW}No patches to push. All patches are already applied.${NC}"
    exit 0
fi

echo -e "${YELLOW}Found the following unapplied patches:${NC}"
echo "$PATCHES" | nl

# Testing function
run_tests() {
    echo -e "${YELLOW}Running tests...${NC}"
    rm -rf ./.lake >/dev/null 2>&1 || true
    rm -rf ./test/Mathlib/.lake >/dev/null 2>&1 || true
    lake exe test
}

echo -e "${YELLOW}Starting to push patches one by one and test...${NC}"

# Store patches in an array
IFS=$'\n' read -r -d '' -a PATCH_ARRAY < <(echo "$PATCHES" && printf '\0')

# Push each patch and test
for patch in "${PATCH_ARRAY[@]}"; do
    echo -e "${YELLOW}Pushing patch: ${NC}$patch"
    stg push

    # Get current commit hash for reference
    CURRENT_COMMIT=$(git rev-parse HEAD)

    echo -e "${YELLOW}Testing commit: ${NC}$CURRENT_COMMIT (Patch: $patch)"

    if run_tests; then
        echo -e "${GREEN}✓ Tests passed for patch: $patch${NC}"
    else
        echo -e "${RED}✗ Tests failed for patch: $patch${NC}"
        echo -e "${RED}This is the first failing commit:${NC}"
        echo -e "   Commit: $CURRENT_COMMIT"
        echo -e "   Patch:  $patch"

        # Ask user what to do
        echo -e "${YELLOW}What would you like to do?${NC}"
        echo -e "   1) Stop here and keep this patch applied (to fix it)"
        echo -e "   2) Pop this patch and restore original state"
        echo -e "   3) Continue pushing remaining patches anyway"

        read -p "Enter your choice (1-3): " choice

        case $choice in
            1)
                echo -e "${YELLOW}Staying at failing patch for you to fix the issue.${NC}"
                exit 0
                ;;
            2)
                echo -e "${YELLOW}Popping failing patch and restoring original state...${NC}"
                stg pop
                cleanup
                ;;
            3)
                echo -e "${YELLOW}Continuing despite test failure...${NC}"
                ;;
            *)
                echo -e "${RED}Invalid choice. Stopping and restoring original state.${NC}"
                cleanup
                ;;
        esac
    fi
done

echo -e "${GREEN}All patches have been pushed and tested successfully!${NC}"

# Ask if user wants to push to the remote
echo -e "${YELLOW}Would you like to push all commits to the remote? (y/n)${NC}"
read -p "Enter your choice: " push_choice

if [[ "$push_choice" == "y" || "$push_choice" == "Y" ]]; then
    echo -e "${YELLOW}Enter the REPL version to use for tagging:${NC}"
    read -p "REPL version (e.g. 1.2.3): " repl_version

    echo -e "${YELLOW}Tagging and pushing commits to remote using tag_and_push_all.sh...${NC}"
    ./tag_and_push_all.sh origin $(git rev-parse --abbrev-ref HEAD) "$repl_version"
    echo -e "${GREEN}All commits have been tagged and pushed to the remote!${NC}"
else
    echo -e "${YELLOW}Skipping push to remote.${NC}"
fi

exit 0
