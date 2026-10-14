# Unproved lemmas in `ProcEquiv`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

1 lemma here could not be proved as stated, none of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `evalBoolExpFalseTot`

- **Where:** `src/ProcEquiv.v` line 477 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:ill-formed-expression-evaluates-to-false` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Keep only the -> direction (re-proved, model axioms only) or add evalBoolExpFun e <> None.

- **Status:** FALSE (counterexample, machine-checked in the cloud session; refutes the statement from the definitions alone, so admitting it is inconsistent)
- **Intent:** The `false` counterpart of `evalBoolExpTrueTot`: the relational evaluation gives `false` exactly when the total function returns `false`.
- **Failure:**
  - The `->` direction holds and is already proved in the existing script. The `<-` direction fails.
  - `evalBoolExpFunTot` returns `false` both when the evaluation really is false and when `evalBoolExpFun e = None` (an ill-formed expression). `evalBoolExp` has no derivation for ill-formed expressions.
  - Counterexample: `e := bEqual (eVar (var 0)) (eVar (var 0))`.
  - Refutation proved: `~ (forall e, evalBoolExp e false <-> evalBoolExpFunTot e = false)`.
- **Ripple-up:** None; it has no users and is not in the safety cone.
- **Suggested fix:** Pick one:
  - keep only the `->` direction (already proved);
  - add the premise `evalBoolExpFun e <> None ->` to the iff.
