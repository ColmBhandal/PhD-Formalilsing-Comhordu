[← Report](../README.md)

# Evidence

| File | What it is |
|---|---|
| `statements-diff.txt` | `diff` of the output of `helper-scripts/print_statements.py` on the baseline (commit `48eed7b`, the merge of step 16) and on this branch. The `d` hunks are the entries that left `NetAuxBasics`, `EntAuxDefs` and `InterfaceLanguage`, and the deleted `link_ent_outList` in `EntAuxResults`; the `a` hunks are the entries that arrived in `NetworkLanguage`, `EntityLanguage` and `InterfaceLanguage`; the `c` hunks are the users of the moved names in the protocol, whose lines differ only in the module path, plus the name counts in the module headers. A moved entry prints differently on the two sides, because the script imports one module at a time and the baseline's `NetAuxBasics` doesn't re-export the network notations; the next two files settle that. |
| `moved_before.v`, `moved_after.v` | Rocq files that print each moved definition and result with the network notations in scope, on the baseline and on this branch. |
| `moved-statements-before.txt`, `moved-statements-after.txt`, `moved-statements-diff.txt` | Their output, and its `diff`, which is only the module paths, the instance binders `(PNames : ProcNames) (PDefs : ProcDefs)` that the section adds to each statement, the `Arguments` lines that make those binders implicit, and the `@` that Rocq prints before a name that now has implicit arguments. |
| `assumptions-before.md` | `make assumptions` on the baseline: 84 entries. |
| `assumptions-after.md` | `make assumptions` on this branch: 83 entries. `EntAuxResults.link_ent_outList` has left (and is now deleted); nothing has arrived. |

## Re-running

From the repository root, with Rocq 9.2.0 on the `PATH` (see the main `README.md`):

```
make -j"$(nproc)"
python3 helper-scripts/print_statements.py > statements-after.txt
python3 helper-scripts/summarise_assumptions.py > assumptions-after.md
rocq c -q -R src ComhCoq doc/reports/2026-10-16-move-network-notions/evidence/moved_after.v > moved-statements-after.txt
```

Then check out the baseline, build it, and run the same there with `moved_before.v` into the `-before` files, and `diff` the pairs.
