[← Report](../README.md)

# Evidence

| File | What it is |
|---|---|
| `statements-diff.txt` | `diff` of the output of `helper-scripts/print_statements.py` on the baseline (commit `adba7e3`, the merge of step 14) and on this branch. Lines starting with `>` are the additions to `src/lang/`; lines starting with `<` are the removed protocol lemmas listed in [`removals.md`](../removals.md). The `c` hunks only change the name counts in the module headers. |
| `assumptions-before.md` | `make assumptions` on the baseline. |
| `assumptions-after.md` | `make assumptions` on this branch. The two files are identical. |

## Re-running

From the repository root, inside the reference image (see the main `README.md`):

```
make -j"$(nproc)"
python3 helper-scripts/print_statements.py > statements-after.txt
python3 helper-scripts/summarise_assumptions.py > assumptions-after.md
```

Then check out the baseline, build it and run the same two scripts into `statements-before.txt` and `assumptions-before.md`, and `diff` the pairs.
