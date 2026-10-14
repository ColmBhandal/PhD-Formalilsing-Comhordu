# Unproved lemmas in `NARNonFS_currSince`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

6 lemmas here could not be proved as stated, none of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `switchCurr_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 114 · **Theorem** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** unaudited

- **Status:** FALSE (in any model with two or more modes; not refutable inside Rocq because `Mode` is abstract)
- **Intent:** An entity in switchCurr has been `nextSince` its next mode, so `currSinceBase` can pass the timestamp on.
- **Failure:** `forall m, switchCurrStateNet i n -> exists t, nextSince m t i n p` leaves `m` unconstrained. `nextSince m` is only created by `nextSinceBase`, an ovReady m → ovWait m step, and the mode is fixed within each stretch. So for a switchCurr entity whose transition was to `m0`, the statement fails for every `m <> m0`.
- **Ripple-up:** In the safety cone. It is used only by `nonFS_currSince`, where `m` is the current mode of `n'`, which feeds the currSince chain in NARIncomp and NARTop.
- **Suggested fix:** `switchCurrStateNet i n -> exists m t, nextSince m t i n p`. Then in `nonFS_currSince`, identify `m` via `switchCurr_nextSince_nextMode_net`, `switch_states_mState` and a new `currModeNet_unique`. Alternatively add the hypothesis `nextModeNet m i n`.

## `ovWait_nextSince_pending`

- **Where:** `src/NARNonFS_currSince.v` line 31 · **Theorem** · 2015 label: `In the discrete inductive case, we backtrack for cases of the previous state.` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS (ordering and dependencies)
- **Intent:** An entity in ovWait is `pending` or `nextSince m`.
- **Failure:** It is a mutual induction with `ovReady_nextSince_pending`. The delay cases need `pending_urgent`, which is stated later in the file. A scratch proof compiled, but it used `ovWait_prev_net_strong`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, which are all inconsistent as stated.
- **Ripple-up:** `ovWait_zero_nextSince`, then `switchBc_nextSince`, then `switchCurr_nextSince`, then `nonFS_currSince`.
- **Suggested fix:**
  1. Move `pending_urgent` first.
  2. Restate the backtracking lemma for ovWait: the predecessor is ovWait, ovReady (with `x = t`, `y = period`) or init (with `x = t`, `y = 0`).
  3. Restate backward delay preservation with `x+d` and `y+d`, guarded by `d <=` the remaining timer.
  4. Prove both targets by mutual induction on `p`.

## `ovReady_nextSince_pending`

- **Where:** `src/NARNonFS_currSince.v` line 49 · **Theorem** · 2015 label: `Discard base case as initiality contradicts the state predicate` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS. This is the second conjunct of the mutual lemma with `ovWait_nextSince_pending`; see that write-up.

## `pending_urgent`

- **Where:** `src/NARNonFS_currSince.v` line 80 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** A pending entity cannot delay.
- **Plan:** Induction on `pending`.
  - **ovReady case:** contradiction via `del_ovlp`. The delaying overlap is dormant, tfsCurr or ovWait, all of which can input `abort`; ovReady cannot.
  - **ovWait case:** needs `y = 0` for pending ovWait states, plus entity-level urgency of ovWait with `y = 0`.
- **Suggested fix:** The statement is fine. Add `ovWait_pos_urgent : reachableEnt e -> ovWaitStateEnt m t x zeroTime e -> e -ED- d ->> e' -> False`.

## `ovWait_zero_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 90 · **Theorem** · 2015 label: `2` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (needs consistent backtracking and delay lemmas)
- **Intent:** ovWait with `x = 0` implies `nextSince`.
- **Failure:** A `Qed` proof existed, but it used `ovWait_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, both inconsistent as stated. Everything else in it is consistent: for example, init → ovWait never gives `x = 0`, because of `period_positive`. The prover reverted it.
- **Suggested fix:** The statement is fine. It becomes provable once timer-correct versions of the ovWait backtracking and backward-delay lemmas exist.

## `switchBc_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 103 · **Theorem** · 2015 label: `2` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION
- **Intent:** switchBc m implies `nextSince m`.
- **Failure:** A `Qed` proof existed, but it used `reachableProt_triple` (to get the triple shape and `overlapState`, both incomplete) and `ovWait_del_pres`, both inconsistent as stated, plus `ovWait_zero_nextSince`. The prover reverted it.
- **Suggested fix:** The statement is fine. Either:
  - restate `switchBc_prev` without the `overlapState` premise, or complete `overlapState`;
  - and use a timer-correct `ovWait_del_pres` (`ovWait m t x y -d-> ovWait m t (x-d) (y-d)`).
