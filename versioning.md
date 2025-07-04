# Stacked Git

1. Duplicate last version branch

```bash
git checkout <branch>
stg branch -C <new_branch>
```

2. Use stacked git to add a new (empty) commit

```bash
stg pop -a
stg new <new_version> -m <new_version>
```

3. Rebase the new branch on master

```bash
stg rebase master
```

4. Update the previous commit by reverting Lean-version specific changes in master

```bash
stg push
git revert --no-commit <commit_id>
```

5. Check changes, keep only changes related to version change to propagate back all new features and bug fixes, then run tests

```bash
lake exe test
```

6. If the tests pass, add the changes

```bash
stg refresh
git revert --abort
```

Redo step 5. for as many missing versions as needed. You can also use `update_lean_version.sh` to update the Lean version in the different places automatically and run the tests.

7. Push commits and test each one

```bash
./find_first_failing_commit.sh
```

This script will:

- Push commits one by one using `stg push`
- Run tests after each push
- Stop at the first commit where tests fail
- Give you options to fix the failing commit, continue anyway, or restore the original state
- Offer to run the `tag_and_push_all.sh` script if all tests pass, which will:
  - Ask you for the REPL version to use for tagging
  - Validate that each commit name matches the Lean version in the lean-toolchain file
  - Tag each commit with a version in the format `v{repl_version}_lean-toolchain-v{lean_version}`
  - Push all commits and tags in a single operation
