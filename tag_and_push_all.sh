#!/bin/bash

set -e  # Exit on error

# Function to display usage
show_usage() {
  echo "Usage: $0 <remote-name> <branch-name> [base-branch]"
  echo "Example: $0 origin v1.X.X"
  echo "Example with base branch: $0 origin v1.X.X master"
  exit 1
}

# Check that we have all required arguments
if [ $# -lt 2 ]; then
  show_usage
fi

REMOTE="$1"
BRANCH="$2"
REPL_VERSION="$2"  # Use the branch name as the REPL version

# Add v prefix to REPL version if not present
if [[ ! "$REPL_VERSION" =~ ^v ]]; then
  REPL_VERSION="v$REPL_VERSION"
fi

BASE_BRANCH="${3:-master}"  # Default to master if not provided

# Function to extract commit name (should match Lean version)
extract_commit_name() {
  local commit=$1
  # Get the first line of the commit message
  local commit_name=$(git log -1 --format=%s "$commit" | tr -d ' ')
  echo "$commit_name"
}

# Function to extract Lean version from lean-toolchain file
extract_lean_version() {
  local commit=$1
  # Get the lean-toolchain content at this commit
  local lean_version=$(git show "$commit:lean-toolchain" 2>/dev/null | grep -oE '[0-9]+\.[0-9]+\.[0-9]+(-[a-zA-Z0-9]+)*' | head -1)

  # If lean-toolchain doesn't exist or doesn't contain a version
  if [ -z "$lean_version" ]; then
    echo "Error: Could not extract Lean version from lean-toolchain file at commit ${commit:0:8}"
    exit 1
  fi

  echo "$lean_version"
}

# Function to validate that commit name matches Lean version
validate_commit_matches_lean_version() {
  local commit=$1
  local commit_name=$(extract_commit_name "$commit")
  local lean_version=$(extract_lean_version "$commit")

  # Strip 'v' prefix if present for comparison
  local commit_name_clean=${commit_name#v}
  local lean_version_clean=${lean_version#v}

  if [[ "$commit_name_clean" != "$lean_version_clean" ]]; then
    echo "Error: Commit name '$commit_name' does not match Lean version '$lean_version' in lean-toolchain file"
    exit 1
  fi

  return 0
}

# Check that we're on the correct branch
CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
if [[ "$CURRENT_BRANCH" != "$BRANCH" ]]; then
  echo "Error: You need to be on branch $BRANCH to run this script."
  exit 1
fi

# Check if branch exists on remote
BRANCH_EXISTS_REMOTE=false
if git ls-remote --exit-code --heads "$REMOTE" "$BRANCH" &>/dev/null; then
  BRANCH_EXISTS_REMOTE=true
fi

# Initialize base branch synchronization variable
BASE_BRANCH_SYNC=true

# Check if base branch exists on remote
if ! git ls-remote --exit-code --heads "$REMOTE" "$BASE_BRANCH" &>/dev/null; then
  echo "Warning: Base branch $BASE_BRANCH doesn't exist on remote $REMOTE."
  echo "Running simulation on local base branch only."
  BASE_BRANCH_SYNC=false
else
  # Check if local base branch is synchronized with remote base branch
  if git rev-parse --verify "$BASE_BRANCH" &>/dev/null; then
    LOCAL_BASE_HEAD=$(git rev-parse "$BASE_BRANCH")
    REMOTE_BASE_HEAD=$(git rev-parse "$REMOTE/$BASE_BRANCH")

    if [[ "$LOCAL_BASE_HEAD" != "$REMOTE_BASE_HEAD" ]]; then
      echo "Warning: Your local base branch is not synchronized with remote $REMOTE/$BASE_BRANCH."
      echo "Running simulation on local base branch only."
      BASE_BRANCH_SYNC=false
    fi
  fi
fi

# For a local-only branch, get all commits since it diverged from the base branch
if [[ "$BRANCH_EXISTS_REMOTE" == "false" ]]; then
  echo "Branch $BRANCH doesn't exist on remote $REMOTE yet."
  echo "Will tag and push all commits since diverging from $BASE_BRANCH."

  # Use local base branch for finding the merge base
  if git rev-parse --verify "$BASE_BRANCH" &>/dev/null; then
    echo "Using local $BASE_BRANCH branch for finding divergence point."
    MERGE_BASE=$(git merge-base "$BRANCH" "$BASE_BRANCH")
  else
    # Try remote base branch if local doesn't exist
    if git ls-remote --exit-code --heads "$REMOTE" "$BASE_BRANCH" &>/dev/null; then
      echo "Using remote $REMOTE/$BASE_BRANCH for finding divergence point."
      MERGE_BASE=$(git merge-base "$BRANCH" "$REMOTE/$BASE_BRANCH")
    else
      MERGE_BASE=""
      echo "Warning: Neither local nor remote base branch $BASE_BRANCH exists."
    fi
  fi

  if [ -z "$MERGE_BASE" ]; then
    echo "Could not find common ancestor with $BASE_BRANCH. Using all commits in the branch."
    COMMITS=$(git rev-list --reverse "$BRANCH")
  else
    COMMITS=$(git rev-list --reverse "$MERGE_BASE..$BRANCH")
  fi
else
  echo "Branch $BRANCH exists on remote. Getting only new commits."
  COMMITS=$(git rev-list --reverse "$REMOTE/$BRANCH..$BRANCH")
fi

# Check if there are any commits to push
if [ -z "$COMMITS" ]; then
  echo "No commits to push in the specified branch."
  exit 0
fi

# Count commits to push
COMMIT_COUNT=$(echo "$COMMITS" | wc -l)
echo "Found $COMMIT_COUNT commits to tag and push."

# Display all commits and their proposed tags
echo -e "\nPreparing to tag the following commits:"
echo "----------------------------------------"
COUNTER=1
for COMMIT in $COMMITS; do
  COMMIT_MSG=$(git log --format=%B -n 1 "$COMMIT" | head -n 1)
  COMMIT_NAME=$(extract_commit_name "$COMMIT")
  LEAN_VERSION=$(extract_lean_version "$COMMIT")

  # Validate commit name matches Lean version
  echo -n "Validating commit ${COMMIT:0:8}... "
  if validate_commit_matches_lean_version "$COMMIT"; then
    echo "OK"
  fi

  # Ensure LEAN_VERSION has proper 'v' prefix for tag naming
  LEAN_VERSION_FOR_TAG="${LEAN_VERSION}"
  # Add v prefix if not present
  if [[ ! "$LEAN_VERSION_FOR_TAG" =~ ^v ]]; then
    LEAN_VERSION_FOR_TAG="v${LEAN_VERSION_FOR_TAG}"
  fi

  # New tag format
  TAG_NAME="${REPL_VERSION}_lean-toolchain-${LEAN_VERSION_FOR_TAG}"

  echo "[$COUNTER/$COMMIT_COUNT] Commit: ${COMMIT:0:8} - $COMMIT_MSG"
  echo "                Tag: $TAG_NAME"
  echo ""

  COUNTER=$((COUNTER+1))
done

# Check if we have any commits to process in simulation mode first
if [ -z "$COMMITS" ]; then
  echo "No new commits to tag. Local branch is synchronized with remote."
  exit 0
fi

# Check if local base branch is not synchronized with remote
if [[ "$BASE_BRANCH_SYNC" == "false" ]]; then
  echo "Aborting: Local base branch is not synchronized with remote."
  echo "Please synchronize your base branch with the remote before pushing tags."
  exit 0
fi

# Ask for confirmation
read -p "Do you want to create these tags and push everything? [y/N] " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
  echo "Operation cancelled."
  exit 0
fi

# Create tags for each commit
TAGS_CREATED=()
echo -e "\nCreating tags:"
echo "---------------"
for COMMIT in $COMMITS; do
  LEAN_VERSION=$(extract_lean_version "$COMMIT")

  # Ensure LEAN_VERSION has proper 'v' prefix for tag naming
  LEAN_VERSION_FOR_TAG="${LEAN_VERSION}"
  # Add v prefix if not present
  if [[ ! "$LEAN_VERSION_FOR_TAG" =~ ^v ]]; then
    LEAN_VERSION_FOR_TAG="v${LEAN_VERSION_FOR_TAG}"
  fi

  TAG_NAME="${REPL_VERSION}_lean-toolchain-${LEAN_VERSION_FOR_TAG}"
  echo "Creating tag $TAG_NAME for commit ${COMMIT:0:8}"

  # Check if tag already exists
  if git rev-parse "$TAG_NAME" >/dev/null 2>&1; then
    echo "Warning: Tag $TAG_NAME already exists. Skipping."
  else
    git tag -a "$TAG_NAME" "$COMMIT" -m "$LEAN_VERSION"
    TAGS_CREATED+=("$TAG_NAME")
  fi
done

# Push the branch
echo -e "\nPushing branch $BRANCH to $REMOTE..."
if ! git ls-remote --exit-code --heads "$REMOTE" "$BRANCH" &>/dev/null; then
  # First time pushing this branch
  git push -u "$REMOTE" "$BRANCH"
else
  git push "$REMOTE" "$BRANCH"
fi

# Push all tags one by one to trigger CI for each tag
if [ ${#TAGS_CREATED[@]} -gt 0 ]; then
  echo -e "\nPushing ${#TAGS_CREATED[@]} tags to $REMOTE one by one to trigger CI for each tag..."
  for TAG in "${TAGS_CREATED[@]}"; do
    echo "Pushing tag $TAG to $REMOTE..."
    git push "$REMOTE" "$TAG"
    # Small delay to ensure CI has time to register each tag separately
    sleep 3
  done
  echo "Done! All tags pushed individually to trigger CI for each."
else
  echo -e "\nNo new tags were created."
fi

echo -e "\nAll commits and tags pushed successfully!"
echo "Setting up tracking branch relationship..."
git branch --set-upstream-to="$REMOTE/$BRANCH" "$BRANCH"
echo "Done! Your local branch is now tracking the remote branch."
