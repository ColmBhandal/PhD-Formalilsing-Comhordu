# Unproved lemmas in `NARIncomp`

[← Lemma index](README.md) · [Report summary](../README.md)

2 lemmas here could not be proved as stated, none of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `incomingNet_urgent`

- **Where:** `src/NARIncomp.v` line 30 · **Theorem** · 2015 label: `3` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS (message shape and/or reachability)
- **Intent:** A pending input message forbids a delay.
- **Failure:** `stepIlDel` always lets an input list delay. Urgency can come only from `noSync`, with `listening` accepting `chanInProc v`, and `listening` only inputs 2-element lists. The statement quantifies over arbitrary `v`.
- **Ripple-up:** It is used by `incomp_abort` and `incomp_tfs`, both with `v = [baseMode m', basePosition l']`.
- **Suggested fix:** Restrict `v` to `[baseMode m, basePosition l]`. Proof plan: `link_net_ent_del_bkwd`, then `del_listening_net`, then listening enables `chanInProc ;? [m,l]`, then the interface can output `chanInProc {! v`, which contradicts `noSyncNow`.

## `incomp_incomingNet_abort`

- **Where:** `src/NARIncomp.v` line 91 · **Theorem** · 2015 label: `3` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE as stated (missing case), also BLOCKED-ON-STUB (`nextModeNet`)
- **Intent:** A pending message incompatible with the *next* mode either stays incoming or moves the entity onto `msgAbortPath`.
- **Failure:** `mapMsg` also requires the message to be compatible with the *current* mode. If it is incompatible with both modes, consuming it via `gotMsg` lands in `msgBadPathNet i n'`, which is neither disjunct.
- **Ripple-up:** In the safety cone, via `instant_incomp_abort`, then `incomp_abort`, then `incomp_tfs`, then `safety`.
- **Suggested fix:**
  - Add a third disjunct `\/ msgBadPathNet i n'`. `incomp_abort` still works because `msgBadPathNet_urgent` kills that case; note that lemma is itself admitted and refuted without reachability.
  - Define `nextModeNet` via the mode state of the entity at `i`.
