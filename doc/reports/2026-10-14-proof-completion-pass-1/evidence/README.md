# Evidence

[← Proof completion, pass 1](../README.md)

None of this is part of the build.

| Path | What it is |
|---|---|
| `inconsistent-or-contradicting.txt` | The admitted lemmas that are refutable from the model axioms alone, or jointly inconsistent with other admits. Proofs that depend on any of them are held back. |
| `audit/classification.jsonl` | One line per written-up target: audit class, whether it is in the safety cone, users, dependent proofs, root cause and fix. |
| `audit/{net,ent,rest}/*.v` | The auditors' standalone Rocq files: refutations of admitted statements, plus proofs of corrected statements. Each imports the relevant `ComhCoq` module and ends with `Print Assumptions`. The matching `.log` holds the output. |
| `held-back/*.v` | The 25 held-back proofs, in the fan-out harness format: an optional `(* HELPERS *)` section inserted before the target, then a `(* PROOF *)` section replacing its `Admitted`. |
| `fixes/*.v` | Explore-mode files with validated fixes, e.g. `reachableProt_triple_fix` under reachability-based component predicates, and the `noSyncNow` counterexample. These use the fan-out harness format, so the helpers precede the (admitted) target. |
| `conditional/*.md` | Notes on proofs the cloud provers completed that rest on inconsistent lemmas, and where to find them. |

## Re-running an audit file

The audit files were compiled against the **pre-PR** sources, with all targets still admitted, at commit `fc8271f`. Against later sources they may need small adjustments: a lemma that is now proved still has the same statement, so most files work unchanged. From the repository root, after `make`:

```
rocq compile -R src ComhCoq doc/reports/2026-10-14-proof-completion-pass-1/evidence/audit/net/a_bcWaitNet_del_bkwd.v
```

The `Print Assumptions` output should list only `ComhBasics` model axioms and stdlib axioms, plus, for a refutation, the refuted admitted lemma itself.
