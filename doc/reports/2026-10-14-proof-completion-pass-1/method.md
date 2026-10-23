# Method and trust

[← Proof completion, pass 1](README.md)

## How each proof was checked

- **Isolation.** Each target was proved in a copy of its module, cut off just after the target, and compiled against a frozen build of everything before it. A target could use earlier lemmas, including ones that are still admitted.
- **Rejection rules.** The harness rejected:
  - `Admitted`, `admit`, new axioms and similar escapes;
  - any change to the target's statement;
  - any proof whose `Print Assumptions` included a known-inconsistent lemma.
- **Integration.** All accepted proofs were then spliced into the real sources together, and the whole project was rebuilt from clean. CI does the same build on every pull request.

## How the failures were checked

- Provers backed each write-up with compiled evidence where they could: a counterexample, a refutation, or a proof of a corrected statement. The FALSE-ARGUED verdicts are the ones where that wasn't possible.
- Three independent auditors re-ran the evidence for 93 of the 108 write-ups. They recompiled each refutation against the exact statement and checked its `Print Assumptions`.
  - All of the evidence compiled.
  - The auditors corrected several verdicts, in both directions.
  - Their verdicts are the **Audit** lines in the [lemma write-ups](lemmas/README.md).
- **Not audited:** 15 write-ups from the last two cloud provers (`NARNonFS_currSince` and NAR-small), which arrived after the audit started. They're marked "unaudited" in the index.

## What "proved" means here

A merged proof is proved **relative to the admitted lemmas that remain**. It can't depend on an inconsistent lemma, because the harness rejected those. But it can still depend on admitted lemmas that are false without being inconsistent. Such proofs are valid reductions, and should be read as conditional on those lemmas being fixed. `make assumptions` shows exactly what `safety` still rests on.

## Logistics

- **Parallelism.** Up to 20 local subagents, which is this environment's cap, plus 5 cloud sessions for the overflow. They shared work through a common claim queue, and an idle prover would steal unclaimed work.
- **Interruptions.** The first run was cut short by an account usage limit. It was relaunched the next morning, with an hourly watchdog to recover from any further limits.
