# Proof completion, pass 1

**2026-10-14** · Part of the [Rocq upgrade and proof completion workstream](../../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md)

This was the first agent pass over every unproved result in the development: all 228 `Admitted` lemmas and all 28 `Conjecture`s, 256 targets in total. This page is the five-minute version. The rest of this folder is detail, there for when you need it.

## The short version

- **The upgrade is done.** The project builds on Rocq 9.2.0, no existing proof broke, and CI is green.
- **123 of the 256 targets are now proved**, with their statements untouched. Another 25 proofs exist, but they're held back because they lean on lemmas that turned out to be inconsistent.
- **108 targets can't be proved as written.** Each one has a write-up. Almost all of them come down to about a dozen modelling issues, and each issue has a concrete fix.
- **The big one: `safety` currently proves nothing.** It rests on admitted lemmas that can be refuted from the model axioms alone, so `False` follows from its assumptions. This has been machine-checked.
  - This doesn't mean the protocol is unsafe. It means the formal argument has holes, and they need fixing before the proof counts.

## What I need from you

No statement, definition, model axiom or `Parameter` stub has been changed. These calls are yours:

1. **Complete the component-state predicates** (`overlapState`, `listenerState`). This is the most structural problem, and the proposed fix has already been proved to work. [Details](root-causes-and-fixes.md#1-incomplete-component-state-predicates)
2. **Fix the listener's notification arity.** The listener takes 2 fields on `chanAN`, but notifications carry 3. The thesis has the same mismatch on p.134. [Details](root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis)
3. **Approve the other fixes.** The most common one adds a reachability hypothesis, such as `reachableNet n`, which the callers already have in scope. [All twelve root causes](root-causes-and-fixes.md)
4. **Pick completions for the `Parameter` stubs.** [Suggestions](root-causes-and-fixes.md#parameter-stubs)
5. **Smaller calls:** how to close [gaps in the model axioms](root-causes-and-fixes.md#11-gaps-in-the-model-axioms), whether to package the axioms as a `Module Type`, and whether to prune duplicate and unused lemmas. [Details](root-causes-and-fixes.md#smaller-decisions)

Once these are decided, pass 2 applies them and re-runs the provers. Much of that work is already done and waiting, as held-back and conditional proofs.

## Where to go next

| If you want to… | Read |
|---|---|
| understand why `safety` is vacuous today | [Why `safety` proves nothing yet](why-safety-is-vacuous.md) |
| weigh each root cause and its proposed fix | [Root causes and proposed fixes](root-causes-and-fixes.md) |
| see the numbers, the audit verdicts and the held-back proofs | [Results](results.md) |
| know what this pass changed in the repository | [What changed](what-changed.md) |
| decide how far to trust the results | [Method and trust](method.md) |
| look up a single lemma | [Lemma index](lemmas/README.md), which links to one file per module |
| re-run a counterexample in Rocq | [Evidence](evidence/README.md) |
