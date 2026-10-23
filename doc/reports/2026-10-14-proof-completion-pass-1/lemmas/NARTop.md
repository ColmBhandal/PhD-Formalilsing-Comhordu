# Unproved lemmas in `NARTop`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

6 lemmas here could not be proved as stated, 3 of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `ovWait_sent`

- **Where:** `src/NARTop.v` line 116 · **Theorem** · 2015 label: `The base case fails because we know all entities are dormant to begin with.` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `incomplete-definition (overlapState/listenerState)`
- **Fix (audit summary):** Add reachableNet n to NetAuxBasics.ovWait_prev_net_strong and fix reachableProt_triple (compReach); then re-run the cloud proof.

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof depends on an admitted lemma that is inconsistent as stated)
- **Intent:** See the in-file comment and `(*Proof: …*)` sketch.
- **Failure:** A complete proof was written in the cloud session, and for `currSince_del_bcWait` it was re-checked here. It rests on admitted lemmas that are inconsistent as stated (`ovWait_prev_net_strong` and/or `reachableProt_triple`, transitively). So it can't be accepted until those statements or definitions are fixed. See CONDITIONAL_PROOFS.md.
- **Ripple-up:** In the safety cone: `ovWait_sent` feeds `nextSince_periodic_sent`, and `currSince_del_bcWait` feeds `currSince_periodic_sent`.
- **Suggested fix:**
  - Add `reachableNet n` to `ovWait_prev_net_strong`.
  - Make the protocol component state predicates reachability-based (`compReach`), so that `reachableProt_triple` becomes provable.
  - Then re-run the proof, which is kept in the cloud-NARTop work dir and diff.

## `currSince_del_bcWait`

- **Where:** `src/NARTop.v` line 280 · **Corollary** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `incomplete-definition (overlapState/listenerState)`
- **Fix (audit summary):** Fix reachableProt_triple (compReach) and currSince_bc_state, then re-run the existing conditional proof.

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof depends on an admitted lemma that is inconsistent as stated)
- **Intent:** See the in-file comment and `(*Proof: …*)` sketch.
- **Failure:** A complete proof was written in the cloud session, and for `currSince_del_bcWait` it was re-checked here. It rests on admitted lemmas that are inconsistent as stated (`ovWait_prev_net_strong` and/or `reachableProt_triple`, transitively). So it can't be accepted until those statements or definitions are fixed. See CONDITIONAL_PROOFS.md.
- **Ripple-up:** In the safety cone: `ovWait_sent` feeds `nextSince_periodic_sent`, and `currSince_del_bcWait` feeds `currSince_periodic_sent`.
- **Suggested fix:**
  - Add `reachableNet n` to `ovWait_prev_net_strong`.
  - Make the protocol component state predicates reachability-based (`compReach`), so that `reachableProt_triple` becomes provable.
  - Then re-run the proof, which is kept in the cloud-NARTop work dir and diff.

## `bcWait_currSince_time`

- **Where:** `src/NARTop.v` line 288 · **Theorem** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** FALSE-ARGUED · root cause: `other:wake-up-corner-case (bcWait m 0 right after switchBc)`
- **Fix (audit summary):** Add 0 < x (the only caller currSince_periodic_sent passes x + d > 0).

- **Status:** FALSE (counterexample, argued trace)
- **Intent:** If the broadcaster is `bcWait m x` while `currSince m t`, then the last broadcast of `m` was `period m - x` ago, and that is at most `t`.
- **Failure:** No axiom relates `period` to `waitTime`. Take `m_prev -mtr-> m` with `W := waitTime m_prev m < period m`. Then this run happens with no time passing:
  1. `init m` → `ovWait(m, W, W, period m)`
  2. after `W`, `chanPause!` → `switchBc m`
  3. `switchBc m` wakes the broadcaster to `bcWait m 0`
  4. `switchCurr` → `switchListen`, which can come before `bcWait m 0`'s zero-timeout `chanPos?`

  `currSinceBase` now gives `currSince m W` with `bcWait m 0`, so the goal `period m <= W` fails. The 2015 sketch's base case "x = period m" overlooks this wake-up state.
- **Ripple-up:** The only user is `currSince_periodic_sent` (`NARTop.v:448`), which feeds `currSince_fst_deliv_suff`, then `pre_del_suff`, then `safety`. The caller always passes `x + d > 0`, so the false corner case never arises there.
- **Suggested fix:** Add `0 < x ->`. With that, the induction's base case is vacuous, and the caller already has `0 < x + d` from `delPos`.

## `init_ovWait_track_net`

- **Where:** `src/NARTop.v` line 104 · **Lemma** · 2015 label: `#lift-track-net` · **in safety cone:** no
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `other:missing-bisimulation-injectivity-infrastructure (not a failure)`
- **Fix (audit summary):** Weaken the conclusion to y = zeroTime (all that ovWait_sent uses) or add an ovWait_bisim_inj helper.

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** A discrete step from `init m` into `ovWait m' t' x y` forces `m = m'`, `x = t'` and `y = 0`.
- **Failure:** It needs injectivity of `ovWait`'s parameters up to bisimilarity, i.e. `ovWait m t x y ~p~ ovWait m' t' x' y' -> ...`, which needs coinductive timed reasoning. The development has no infrastructure for that, and even the sibling tracking lemmas are admitted. (Other provers showed several sibling `*_track_net` lemmas are false because truncated subtraction makes different `t` bisimilar, so check that this one asserts nothing about `t` beyond what is observable.)
- **Ripple-up:** It is used only by `ovWait_sent` (init case), then `nextSince_periodic_sent`, then `currSince_fst_deliv_suff`, then `safety`. Only `y = 0` is consumed.
- **Suggested fix:** Weaken the conclusion to `y = zeroTime`, which is all the caller needs, or add an `ovWait_bisim_inj` helper.

## `tfsBc_not_currSince`

- **Where:** `src/NARTop.v` line 239 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:failSafeSucc-may-be-identity`
- **Fix (audit summary):** Add ~ failSafe m, or model axiom failSafeSucc m <> m (owner approval).

- **Status:** NEEDS-HYPOTHESIS
- **Intent:** An entity in `tfsBc` is not currSince any mode.
- **Failure:** No axiom forbids `failSafeSucc m = m`, or `m -mtr-> m`. Take a fail-safe `F` with `failSafeSucc F = F`. Then `currSince F` survives the whole tfs path through `tfsStart`, `tfsNext F` and `tfsCurr` to `tfsBc`. The 2015 sketch's "mode transition relation is anti-reflexive" is not an axiom.
- **Ripple-up:** It is used only by the intended proof of `currSince_bc_state`; grep finds no direct Rocq users.
- **Suggested fix:** Either:
  - add the model axiom `failSafeSucc m <> m` (needs owner approval), or
  - restate the lemma with `~ failSafe m ->`.

## `currSince_bc_state`

- **Where:** `src/NARTop.v` line 256 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `other:new-transition-wakes-broadcaster-in-new-mode`
- **Fix (audit summary):** Add ~ switchCurrStateNet i n (currSince_del_bcWait then needs net-level switchCurr urgency).

- **Status:** FALSE (counterexample, argued trace)
- **Intent:** While `currSince m` holds, the broadcaster is `bcWait m _` or `bcReady m _`.
- **Failure:** Start a new transition to `m' <> m`: `stepMsInit`, dormant reads mNext, then `init m'`, `ovWait m'`, `ovReady m'`, `switchBc m'`. The current mode stays `m`, so `currSince m` survives. Then `switchBc m'` does `chanWake<m'>!`, and the broadcaster's `chanWake?` branch makes it `bcWait m' 0`. Now `currSince m` holds with broadcaster `bcWait m' 0`, and neither disjunct holds.
- **Ripple-up:** It is used by `currSince_del_bcWait`, then `currSince_periodic_sent`, then on to `safety`. The counterexample state `switchCurr` is urgent, and every current use is under a delay, so those uses avoid it.
- **Suggested fix:** Add `~ switchCurrStateNet i n ->`. The knock-on is that `currSince_del_bcWait` then needs a network-level lemma that switchCurr is urgent.
