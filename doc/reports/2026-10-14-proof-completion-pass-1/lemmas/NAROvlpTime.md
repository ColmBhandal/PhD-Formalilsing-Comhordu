# Unproved lemmas in `NAROvlpTime`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

6 lemmas here could not be proved as stated, none of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `nextSince_switchCurr_lower`

- **Where:** `src/NAROvlpTime.v` line 125 · **Theorem** · 2015 label: `1` · **in safety cone:** yes
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

## `pending_urgent`

- **Where:** `src/NAROvlpTime.v` line 28 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE in the current semantics (argued; consistent with w1b-13's machine-checked finding on `noSyncNow`)
- **Intent:** A pending entity (ovWait right after init, or ovReady) cannot delay.
- **Failure:** With `y = 0`, `del 0 (chanPos?..)` can delay, because input prefixes delay (`stepTpIn`), and after init `x = tw + P > 0`. `stepTeDel` only requires `noSync` with the interface and the mode state. The local position read `stepDePosRead` doesn't block a delay, unlike the thesis's noComm clause (Def 4.22).
- **Ripple-up:** It has no users. `NARNonFS_currSince` has a separate lemma of the same name.
- **Suggested fix (semantics):** Add `forall l', ~ discActEnabled p (chanPos ;? [basePosition l'])` to `stepTeDel`/`noSyncNow`, restoring the thesis's rule.

## `pending_time1`

- **Where:** `src/NAROvlpTime.v` line 39 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** In ovWait while pending, `u = tw(m0, m) + P`.
- **Failure:** Induction on `pending` works except the base case. That needs: from `initStateNet m0 i n`, a step `n -a-> n'` and `ovWaitStateNet m u x y i n'`, conclude `exists m1 q, u = waitTime m1 m q +t+ period m`. No lemma gives the value of `t`, and `init_ovWait_track_net` in NARTop only gives `x = t` and `y = 0`.
- **Ripple-up:** `pending_time2`, then `nextSince_ovWait_ovReady_time`, then the `*_lower` lemmas, then `safety`.
- **Suggested fix:** Add a tracking lemma `init_ovWait_track_time_net : initStateNet m i n -> ovWaitStateNet m' t x y i n' -> n -NA- a -NA> n' -> exists m0 q, t = addTime (waitTime m0 m' q) (period m')`.

## `pending_time2`

- **Where:** `src/NAROvlpTime.v` line 52 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

## `nextSince_ovWait_ovReady_time`

- **Where:** `src/NAROvlpTime.v` line 66 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

## `nextSince_switchBc_lower`

- **Where:** `src/NAROvlpTime.v` line 110 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.
