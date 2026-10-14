# Unproved lemmas in `NARMisc`

[← Lemma index](README.md) · [Report summary](../README.md)

11 lemmas here could not be proved as stated, 6 of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `switchBc_nextMode_net`

- **Where:** `src/NARMisc.v` line 50 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n (every caller has it in scope); provable once nextModeEnt is defined, plus a net-level switchBc_prev lift.

- **Status:** NEEDS-HYPOTHESIS (`reachableNet n`). The statement as written is refutable from the admitted interface lemmas that agree with the intended definition of the stub; the refutation was checked in Rocq.
- **Intent:** In a reachable network, an entity whose overlap component is in `switchBc m` is mid-transition to `m`, so `nextModeNet m i n`.
- **Failure:** `switchBcStateNet m i n -> nextModeNet m i n` has no reachability premise. `switchBcStateNet` only constrains the software component, so take the unreachable one-entity network
  `n := [ [| nilProc $||$ switchBc m $||$ nilProc, mkPosition 0 0, h, sing m0 |] ]`.
  Here `switchBcStateNet m 0 n` holds (by `bisim_refl`). But `nextMode_ent_ex` and `nextMode_ent_mState` together force `nextModeMState (sing m0) = Some m`, and the left side computes to `None`. Both lemmas hold under the intended stub definition (`nextModeEnt m e` iff the mode state of `e` is `<|_, m, _|>`). Checked in Rocq (`--explore`). `Print Assumptions` lists only `nextMode_ent_ex`, `nextMode_ent_mState`, the stub parameters and model axioms:
  ```coq
  Lemma switchBc_nextMode_net_refute (m m0 : Mode) (h : Interface) :
    (forall m i n, switchBcStateNet m i n -> nextModeNet m i n) -> False.
  Proof.
    intro H.
    set (e := [| nilProc $||$ switchBc m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
    assert (switchBcStateNet m 0 [e]) as IS.
    { econstructor; [ | apply einConsLeft]. constructor. constructor.
      apply ComhCoq.ProcEquiv.bisim_refl. }
    apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
    inversion EIN; subst. unfold e in NM.
    apply nextMode_ent_mState in NM. simpl in NM. discriminate.
  Qed.
  ```
- **Ripple-up:** **In the safety cone.**
  - `NARMisc.nextSince_next` (line 185) uses it as `eapply switchBc_nextMode_net. replace m with x. eassumption. ...`. Here `p : reachableNet n` is in scope, so adding the hypothesis costs one extra subgoal: `eapply switchBc_nextMode_net; [exact p | ]`.
  - My accepted `NARMisc.nextSince_ovWait_modeEq`, in its helper `nextSince_ovWait_modeEq_next`, calls it as `eapply switchBc_nextMode_net; eassumption`. A `reachableNet n0'` hypothesis is in context at that point, so the call keeps working after the fix unchanged.
  - Any proof of `nextSince_switchBc_modeEq` (owned by steal-6) probably calls it too. `p : reachableNet n` is available there.

  Nothing above the cone breaks if the hypothesis is added, because every caller has reachability in scope.
- **Suggested fix:**
  ```coq
  Lemma switchBc_nextMode_net m i n :
    reachableNet n -> switchBcStateNet m i n -> nextModeNet m i n.
  ```
  Proof plan once `nextModeEnt` is defined: induction on `reachableNet`.
  - Base case: contradiction via `initNet_contra`.
  - Discrete step: backtracking shows the previous state was `switchBc m` (IH) or `ovWait m t 0 y` (`ProtAuxResults.switchBc_prev`, lifted to the network). In the second case `ovWaitState_nextMode_net` gives `nextModeNet m i n`, and `nextMode_pres_fwd_net` carries it forward (neither `ovWait` nor `switchBc` is in its excluded set).
  - Delay step: `switchBc` is urgent (`switchBc_urgent`), or use backward delay preservation together with `nextModeNet_del_pres`.

  A net-level `switchBc_prev_net` lift does not exist yet and would be needed.
- **Related finding (admitted interface is inconsistent):** In `EntAuxResults.nextModeEnt_not_stable m1 m2 p l h : nextModeEnt m1 ([|p, l, h, m2|]) -> False`, Rocq infers `m2 : ModeState` (confirmed with `About`), not `m2 : Mode`. So the lemma says `nextModeEnt` never holds for any entity. It contradicts `EntAuxResults.tfsCurr_failSafe`, which has no reachability premise: in a `--explore` check, `tfsCurr_failSafe` and `nextModeEnt_not_stable` together prove `Mode -> Interface -> False`, using the witness entity `[| nilProc $||$ tfsCurr $||$ nilProc, mkPosition 0 0, h, sing m |]`. Fix: annotate `(m2 : Mode)` so the mode state is the stable `sing m2`. `tfsCurr_failSafe` is also false on unreachable entities and needs `reachableEnt e`. My proofs do not use either lemma.

## `switchCurr_nextSince_nextMode_net`

- **Where:** `src/NARMisc.v` line 53 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define nextModeEnt/nextModeNet (lift of nextModeMState) and prove nextMode_pres_fwd_nextSince_net (reachable, nextSince on both sides).

- **Status:** BLOCKED-ON-STUB (`nextModeNet` / `nextModeEnt`). Reduced, and checked in `--explore`, to exactly one missing preservation lemma, which is true under the intended stub definition.
- **Intent:** if entity `i` is `nextSince m` and its overlap component is in `switchCurr` (about to output on `mCurr`), then its mode state still has next mode `m`, i.e. it is `<|m0, m, d|>`.
- **Failure:** The natural proof is induction on `nextSince`. It proves the stronger `nextSince m t i n p -> nextModeNet m i n`, and the `switchCurr` hypothesis is never used.
  - Base: `ovWaitStateNet m t' x y i n'`, so `ovWaitState_nextMode_net` (with reachability `reachNetDisc n n' a p w`) closes it.
  - Delay: `nextModeNet_del_pres` and the IH close it.
  - Discrete step `n -NA- a -NA> n'`, with the IH `nextModeNet m i n` and `nextSinceStateNet i n'`: we must carry `nextModeNet` across the step. The only forward-preservation lemma is `nextMode_pres_fwd_net`, and it requires `~(switchCurrStateNet i n \/ ovAbortStateNet i n \/ tfsCurrStateNet i n)`. In the case `switchCurrStateNet i n` (overlap stays `switchCurr`, since `switchCurr := chanMCurr!switchListen` and `switchListen` is not a `nextSinceState`), the broadcast or listener component, the interface, or another entity can still move. No visible lemma then relates `nextModeNet m i n` to `nextModeNet m i n'`. With `nextModeEnt` opaque, even `nextMode_ent_ex` cannot move from `[|p,l,h,k|]` to `[|p',l',h',k|]`.
  - Going backwards does not help either: every visible lemma that concludes `nextModeNet` is either state-specific (init/ovWait/ovReady/switchBc) or a preservation lemma that excludes `switchCurr`.
- **Caveat (not used):** the visible context is actually inconsistent. `NARMisc.init_nextMode_net` (no `reachableNet` hypothesis) is refuted from `nextMode_ent_ex` + `nextMode_ent_mState`; see `work/NARMisc-1/NARMisc.init_nextMode_net.v`. A vacuous ex-falso proof would therefore type-check. I deliberately did not submit one.
- **Ripple-up:** in the safety cone. Its only user is `NARMisc.nextSince_next` (case 4). That in turn feeds `currSince_curr` (NARMisc:260), `NARIncomp` line 276, and `NARInsuff` lines 342 and 467.
- **Suggested fix:** add to `NetAuxBasics.v`, next to `nextMode_pres_fwd_net`:
  ```coq
  Lemma nextMode_pres_fwd_nextSince_net m i n n' a :
    reachableNet n -> nextModeNet m i n -> nextSinceStateNet i n ->
    nextSinceStateNet i n' -> n -NA- a -NA> n' -> nextModeNet m i n'.
  ```
  (A narrower version that adds the hypothesis `switchCurrStateNet i n` is enough if one also proves that `nextSinceStateNet` is disjoint from `ovAbort` and `tfsCurr`. Those cases then go through `nextMode_pres_fwd_net`.)
  - Why it is true under the intended definition `nextModeNet m i n := exists e, e @ i .: n /\ nextModeEnt m e`, with `nextModeEnt m [|p,l,h,k|] := nextModeMState k = Some m`: in a `nextSinceState` the mode state is a `transState`. It changes only by
    - `stepMsSwitch` (`mCurr @?`, partner is the overlap output `switchCurr -> switchListen`, which leaves `nextSinceState`),
    - `stepMsAbort` (`mStable @?`, partner `ovAbort` or `tfsNext`, which are not `nextSinceState`s),
    - `stepMsInit`, which only applies to a stable mode state.
    The output rules and delay keep `nextModeMState` unchanged.
  - Better still, define the stub as above and prove `nextModeNet` preservation in general for steps whose mode-state action is not `mCurr @?` or `mStable @?`.
- **Partial proof (compiles in --explore, only the missing lemma admitted):** `work/steal-5/NARMisc.switchCurr_nextSince_nextMode_net.v`
  ```coq
  Proof.
    intros NS _. induction NS.
    - eapply ovWaitState_nextMode_net; [exact (reachNetDisc n n' a p w) | eassumption].
    - eapply switchCurr_nextSince_nextMode_net_pres; [exact p | exact IHNS | | exact H | exact w].
      eapply switchCurr_nextSince_nextMode_net_rel_state; eassumption.
    - eapply nextModeNet_del_pres; eassumption.
  Qed.
  ```
  Here `..._rel_state` is a local copy of `nextSince_rel_state`, which is later in the file. `..._pres` is the missing lemma above. With both in place the same script also proves `nextSince_next` outright. Then `switchCurr_nextSince_nextMode_net` could be reordered or derived from it.

## `outgoing_timeout_disc`

- **Where:** `src/NARMisc.v` line 389 · **Theorem** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:message-position-universally-quantified` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Move l into the existential (exists r l, delivered ...); fully proved with model axioms only (outgoing_timeout_disc_fixed); sent_out_del needs a one-line change.

- **Status:** FALSE (counterexample, machine-checked; no admitted lemmas used)
- **Intent:** if entity `i` has payload `v` timed out (stamp 0) in its output queue and the network makes a discrete step, then either `v` is still outgoing with stamp 0, or this step was `i` broadcasting `v`. In the second case `v` was delivered 0 time units ago, from `i`'s own position, to some radius `r`.

- **Failure:** the message position `l : Position` is a **universally quantified parameter** of the theorem. The conclusion asks for `delivered ([-v, l, r-]) …` for *every* `l`. A broadcast always carries the sender's position (`stepDeOut`: `[|p,l,i,k|] -EA- [-v, l, r-]#! ->> …`), and positions do not change on discrete steps. So for any `l` other than entity `i`'s position, the right disjunct can hold only by a stamp-0 delivery of `[-v,l,r-]`, which is impossible.
  Concrete counterexample (for any `m0 : Mode`):
  - Let `e0 := [|procProtocol, (0,0), {li=[]; lo=[<([],0)>]; ln=[]}, sing (failSafeSucc m0)|]`. Then `n := [e0]` is initial (`initialEnt` leaves the interface unconstrained) and so reachable via `p := reachNetInit`.
  - Let `w : [e0] -NA- anOut [-[], (0,0), r-] 0 -NA> [e1]`, where `e1` has an empty output list (`stepDnOutHead`/`stepDeOut`/`stepIntFwdOut`/`stepTlFwdHd`/`stepNlBuff`).
  - Take `v = []`, `i = 0`, `l = (1,0)`. The hypothesis `outgoing [] 0 0 [e0]` holds. The left disjunct fails because `e1`'s output list is empty. The right disjunct fails too: inverting `delivered` on `reachNetDisc … p w` forces either `anOut [-[],(0,0),r-] 0 = anOut [-[],(1,0),r'-] 0`, so `0 = 1`, or a delivery on `reachNetInit`, which has no constructor.

  Verified as `outgoing_timeout_disc_cex : forall m0 : Mode, ~ (<statement universally closed>)` in `NARMisc.outgoing_timeout_disc.v` (HELPERS section, explore check passes). `Print Assumptions` shows only model axioms (`Mode`, `failSafeSucc`, `failSafeSuccFS`, …) and stdlib reals/classical axioms. **No admitted lemma is used.**
- **Ripple-up:** in the safety cone. The only user is `NARMsgPosition.sent_out_del` (line 128, discrete case), which is used by `sent_delivered`, which is used by `NARMsgPosition` line 287 and `NARTop` line 558. `sent_out_del`'s statement is already `exists r l, delivered …`. Its proof gets `l` from inverting `outgoing` and lets `lets` unify the free `l`, so it only *needs* the corrected form below. Nothing up the chain breaks once the statement is fixed.
- **Suggested fix (A, minimal; recommended):** move `l` into the existential, matching `sent_out_del`'s shape:
  ```coq
  Theorem outgoing_timeout_disc (n n' : Network) (a : ActDiscNet) (i : nat)
    (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) :
    outgoing v zeroTime i n ->
    outgoing v zeroTime i n' \/
    exists r l, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
  ```
  **Fully proved** as `outgoing_timeout_disc_fixed`, with `Print Assumptions` showing only model and stdlib axioms. No admitted lemma is used: the proof doesn't even need `link_net_ent_disc_fwd`, because I prove a small forward-existence lemma instead. In `sent_out_del`, replace `ex_flat. right. exists x. exists l. eassumption.` with `ex_flat. right. do 2 eexists. eassumption.` or similar. The discrete step it needs is checked as `outgoing_timeout_disc_user_step`.
  **Alternative (B, stronger):** keep `(l : Position)` but add the hypothesis `inPosNet l i n ->` before `outgoing …`. Also fully proved, as `outgoing_timeout_disc_fixedB`.
- **Partial proof:** the complete development is in `NARMisc.outgoing_timeout_disc.v`, about 150 lines of HELPERS, all `outgoing_timeout_disc_`-prefixed:
  - `_tl_out`: a timed-list output removes only `<(u,0)>`.
  - `_ent_out` and `_ent_nonout`: entity-level output-list preservation.
  - `_mk`: rebuilds `outgoing`.
  - `_fwd`: forward existence of entity `i` across a discrete network step.
  - `_core`: the step is either preserving or `a = anOut [-v, posEnt e, r-] i`.
  - `_fixed`, `_fixedB`, `_user_step`.

  To splice fix A after approval: paste the helpers before the theorem, change the statement as above, and use the body of `outgoing_timeout_disc_fixed` as the proof.

## `notifBadPathNet_urgent`

- **Where:** `src/NARMisc.v` line 412 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n; caller insuff_react has p in scope (fixed proof compiles relative to reachable_net_ent, reachableEnt stub, del_listening).

- **Status:** FALSE (counterexample) — needs `reachableNet n`
- **Intent:** a network in which entity `i` is on the "notify bad" path (listener in `rangeBad` with the current mode, or in `badOvlp`) cannot delay: those states are urgent.
- **Failure:** the statement has no reachability hypothesis (its sibling `notifAbortPathNet_urgent`, directly above it, does have `reachableNet n`). The `rangeBad` case is urgent without reachability (the mode state can always serve `mCurr`). The `badOvlp` case is not: the `bad!` output only blocks delay when something in the entity can synchronise with it. That holds for the real protocol's sender and switch handler in reachable states, but not for arbitrary process terms.
  Counterexample, verified in Rocq via `--explore` and closed under the model axioms only (no admitted lemmas). For any `m : Mode` and any `d`, take the one-entity network `[ [| nilProc $||$ nilProc $||$ badOvlp, origin, mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ]`. Then `notifBadPathNet 0` holds (by `nbpBad` and `bisim_refl`). It also delays by `d` to itself: `badOvlp`'s `bad!` has no partner, so `noSyncNow` holds trivially, and the empty interface and `sing m` delay. Hence `notifBadPathNet_urgent_refuted : forall (m:Mode) (d:Delay), ~ (forall i n n' d, notifBadPathNet i n -> n -ND- d -ND> n' -> False)`. The statement is therefore false whenever `Mode` is inhabited.
- **Ripple-up:** in the safety cone. The only user is `NARInsuff.insuff_react` (NARInsuff.v:634, `contradiction (notifBadPathNet_urgent i n n' d H7 w)`). That proof has `p : reachableNet n` in scope, so the fix costs one extra argument there: `notifBadPathNet_urgent i n n' d p H7 w`.
- **Suggested fix:**
  ```coq
  Lemma notifBadPathNet_urgent i n n' d :
    reachableNet n -> notifBadPathNet i n -> n -ND- d -ND> n' -> False.
  ```
  This is proved in my file as `notifBadPathNet_urgent_fixed`. It compiles, and its assumptions are the model axioms plus `reachable_net_ent`, the `reachableEnt` stub and the admitted `EntAuxResults.del_listening`. It is not in the blacklist. The proof goes through `del_net_ent` to get an entity-level delay, then splits on the two `notifBadPathEnt` cases. In the `rangeBad` case, `chanMCurr ;? [baseMode (currModeMState k)]` is enabled in both the listener and the mode state, which contradicts `noSyncNow`. In the `badOvlp` case, `del_listening` gives `listeningStateEnt e`, and `bisim_dae` on `bad!` (enabled in `badOvlp`) against `listening` yields a `listening` transition on `bad!`, which inversion refutes.
- **Partial proof:** `NARMisc.notifBadPathNet_urgent.v` (in the prover work area, not committed; the audited copy is under [`../evidence/audit/`](../evidence/audit/)) holds the counterexample (`notifBadPathNet_urgent_cex`, `notifBadPathNet_urgent_refuted`) and the fixed proof (`notifBadPathNet_urgent_fixed`). The counterexample is due to an earlier attempt by NARMisc-2. I re-verified it here and made the fixed proof self-contained.

## `bcWait_bktrk_net`

- **Where:** `src/NARMisc.v` line 507 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** FALSE-ARGUED · root cause: `other:sent-on-wrong-network + missing chanWake predecessor case`
- **Fix (audit summary):** Name the step w, put sent on n' with reachNetDisc n n' a p w, and weaken the wake-up disjunct to x = zeroTime; NARTop.bcWait_sent adapts with a simpler script.

- **Status:** FALSE (counterexample, on paper; two independent defects). Not refutable inside Rocq as-is only because `Mode` is an abstract axiom type with no inhabitant/inequality axiom and building a reachable trace needs the whole semantics.
- **Intent:** back-tracking for the broadcast component. If entity `i` is in `bcWait m x` after a discrete step `n -a-> n'`, then before the step it was already `bcWait m x`, or it just woke up (`x = 0`), or it was `bcReady m l` and the step was the broadcast of `[m, l]` (so `x = period m` and the message has just been *sent*).

- **Failure 1 (wrong network in `sent`).** The third disjunct asks for
  `sent [baseMode m, basePosition l] zeroTime i n p`, i.e. sent *in the source network `n`* with history `p`.
  But the `bcReady m l -> bcWait m (period m)` step is itself the output on `chanOutProc` (software `!` synchronised with the interface `?`, an `anTau` network step). `sentBase` therefore yields
  `sent [..] zeroTime i n' (reachNetDisc n n' anTau p w)`: the message is sent in `n'`, not in `n`.
  `sent .. i n p` would need an *earlier* send of exactly `[m,l]` at the same instant, which in general does not exist.
  Counterexample: any reachable trace in which entity `i` enters `bcReady m l` and fires it while no earlier zero-time-ago send of `[m,l]` is recorded in `p`. For example, take the first broadcast after the `switchBc m` wake-up, with the overlap component's last `ovReady` output not at the same instant. Before the step, `bcWait m (period m)` and `sleeping` both fail at `n`, because the component is `bcReady m l`, which is not bisimilar to either: `bcReady` can only output on `chanOutProc`.
  
- **Failure 2 (missing predecessor case).** `bcWait m' x' := chanTrans? sleepingN + <x'>chanPos<vL>? bcReadyN(..) + chanWake<vM>? bcWaitN([vM, 0])`. So `bcWait m' x'` steps on `chanWake ? [m]` (synchronising with the overlap's `switchBc m = chanWake<m>!`) to `bcWait m 0`. This is the normal mode switch while broadcasting in the old mode `m'`: the overlap goes `dormant -> init m -> ovWait m .. -> switchBc m`, while the broadcast component sits in `bcWait m' x'`.
  Then `bcWaitStateNet m 0 i n'` holds, but at `n`:
  - `bcWaitStateNet m 0 i n` is false when `m' <> m` (the mode is observable through the later `chanOutProc [m,_]` output) or when `x' > 0` (`chanPos` is not yet enabled);
  - it is not `sleeping`;
  - it is not `bcReady`.
  
  None of the three disjuncts holds.

- **Ripple-up:** used only in `NARTop.bcWait_sent` (NARTop.v:314), which is in the safety cone (`currSince_periodic_sent` -> ... -> `safety`). There it is used in the discrete case of an induction on `p`. W2 (`x = 0`) is discharged by `0 < x`, and W3 is turned into `sent .. i n' (reachNetDisc ..)` with `constructor` (= `sentDisc`) applied to the bogus `sent .. i n p`. With the fix below, `bcWait_sent` goes through with a *simpler* script, because the base `sent` is delivered directly.

- **Suggested fix:** name the step `w`, put `sent` on `n'`, and weaken the wake-up disjunct to `x = zeroTime`. `x = zeroTime` covers wake-up from both `sleeping` and `bcWait m' x'`, and it is all `bcWait_sent` needs.
  ```coq
  Lemma bcWait_bktrk_net (n n' : Network) (m : Mode) (x : Time)
    (i : nat) (a : ActDiscNet) (p : reachableNet n) (w : n -NA- a -NA> n') :
    bcWaitStateNet m x i n' ->
    bcWaitStateNet m x i n \/ x = zeroTime \/
    (exists l, bcReadyStateNet m l i n /\ x = period m /\
    sent [baseMode m, basePosition l] zeroTime i n' (reachNetDisc n n' a p w)).
  ```
  If the sleeping/bcWait information is wanted, the second disjunct can instead be
  `((sleepingStateNet i n \/ exists m' x', bcWaitStateNet m' x' i n) /\ x = zeroTime)`.
  Corresponding change in `NARTop.bcWait_sent` (discrete case):
  ```coq
  lets BB : bcWait_bktrk_net p s H. decompOr3 BB W1 W2 W3.
  apply IHp in W1. decompEx2 W1 l q V. exists l q. constructor. assumption.
  contradiction (Q W2). invertClearAs2 W3 l L.
  andflat Y. rewrite <- Y1. exists l (Rle_refl x). my_applys_eq Y2. timering.
  ```
  Why the fixed version should be provable: lift a protocol-level back-tracking lemma for the broadcast component, which is missing today; it should be provable with `backtrack_weed`, like `ovWait_prev`:
  ```coq
  p -PA- a -PA> p' -> broadcastState p -> bcWaitState m x p' ->
    bcWaitState m x p \/ x = zeroTime \/
    exists l, bcReadyState m l p /\ x = period m /\ a = chanOutProc ;! [baseMode m, basePosition l].
  ```
  The lemma is: the component either did not move, or it moved by `chanWake?` (from `sleeping` or `bcWait`, giving `x = 0`), or by the `bcReady` output. In the output case, `link_ent_soft_disc`/`procNeq_tau_net` give `a = anTau` plus the interface input on `chanOutProc`, which are exactly the premises of `sentBase`.

- **Partial proof:** none. The statement is false, so no script was attempted.

## `rangeBad_notifBad_net`

- **Where:** `src/NARMisc.v` line 541 · **Lemma** · 2015 label: `#notifBadNetLift #complexNetLift` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `other:missing-currModeNet-hypothesis`
- **Fix (audit summary):** Add currModeNet m i n (proved relative to Conjecture currMode_ent_ex); the single caller notifBad_pres_tfs already has it, same tactic closes it.

- **Status:** NEEDS-HYPOTHESIS (`currModeNet m i n`). The statement is false in every model where `Mode` has two distinct elements. It is not refutable in Rocq without such an assumption, because `Mode` is an abstract axiom type.
- **Intent:** an entity whose listener component is in `rangeBad m` is on the notification-bad path.

- **Failure:** `notifBadPathEnt` has two constructors:
  - `nbpRng p l h k m : rangeBadStateProt m p -> currModeMState k = m -> notifBadPathEnt [|p,l,h,k|]`
  - `nbpBad .. : badOvlpStateProt p -> ..`

  `rangeBad m''` is the listener state that has just received a *foreign* mode `m''` with insufficient range, and is about to read its *own* current mode on `chanMCurr`. It then goes to `badOvlp` only if the two modes are equal (`currEq`). The bad path (`nbpRng`) therefore additionally requires that our current mode is `m`.
  The hypothesis `rangeBadStateNet m i n` says nothing about the mode state `k`. After unfolding (`destruct R as [e E1 E2]; inversion E1; subst; econstructor; [|apply E2]; eapply nbpRng; exact P`), the residual goal is exactly
  ```
  P : rangeBadStateProt m p
  E2 : [|p, l, h, k|] @ i .: n
  ============================
  currModeMState k = m
  ```
  This was verified with `--explore`. Nothing relates `k` to `m`, not even under reachability: the received foreign mode `m''` is arbitrary.
  Counterexample (paper): `n = [ [| q1 $||$ q2 $||$ rangeBad m1, l, h, sing m2 |] ]` with `m1 <> m2`.
  - `rangeBadStateNet m1 0 n` holds via `bisim_refl`.
  - `nbpRng` would need `rangeBad m1 ~p~ rangeBad m2`. That bisimilarity fails: after the input `chanMCurr?[m2]`, the right side reaches `currEq m2 m2`, which can do `chanBad!`; the left side reaches `currEq m2 m1`, which cannot.
  - `nbpBad` would need `rangeBad m1 ~p~ badOvlp`, which fails on `chanBad!`.
  
  Even in reachable networks the situation arises: another entity's message in mode `m1 ≠` our mode, with insufficient range.

- **Ripple-up:** single user `NARInsuff.notifBad_pres_tfs` (NARInsuff.v:407), in the safety cone. The call site is
  `lets RNN : rangeBad_next_net w OR CMN. left. or_flat. eapply rangeBad_notifBad_net; eassumption.`
  The goal is `notifBadPathNet i n'`, with `rangeBadStateNet m i n'` (from `RNN`) and `U0 : currModeNet m i n'` in context. So the strengthened lemma below is a drop-in replacement: the *same* tactic `eapply rangeBad_notifBad_net; eassumption` closes it.
- **Suggested fix:**
  ```coq
  Lemma rangeBad_notifBad_net m i n :
    rangeBadStateNet m i n -> currModeNet m i n -> notifBadPathNet i n.
  Proof.
    intros R C. destruct R as [e E1 E2]. apply currMode_ent_ex in C.
    destruct C as [e' [E2' CM]].
    assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
    inversion E1 as [p l h k P]; subst.
    econstructor; [ | apply E2]. eapply nbpRng. exact P. reflexivity.
  Qed.
  ```
  This exact proof compiles in place, checked as a helper `rangeBad_notifBad_net_fixed` via `check --explore`. It uses only the existing conjecture `currMode_ent_ex` about the `currModeNet` stub. It is the mirror image of the already-proved `notifBadPathNet_cases`.
- **Partial proof:** see `NARMisc.rangeBad_notifBad_net.v` (helper `rangeBad_notifBad_net_fixed` = proof of the fixed statement).

## `init_nextMode_net`

- **Where:** `src/NARMisc.v` line 41 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete (duplicate of NetAuxBasics.init_nextMode_net, no users) or add reachableNet n.

- **Status:** NEEDS-HYPOTHESIS (`reachableNet n`). The statement as written is refutable from the admitted interface lemmas that agree with the intended definition of the stub; the refutation was checked in Rocq.
- **Intent:** In a reachable network, an entity whose overlap component is in `init m` already has `m` as the next mode in its mode state, so `nextModeNet m i n`.
- **Failure:** The statement `initStateNet m i n -> nextModeNet m i n` does not assume `reachableNet n`. `initStateNet` only constrains the software component, so take an unreachable one-entity network whose mode state is stable:
  `n := [ [| nilProc $||$ init m $||$ nilProc, mkPosition 0 0, h, sing m0 |] ]`.
  Then `initStateNet m 0 n` holds (by `bisim_refl`). However:
  - `nextMode_ent_ex` turns `nextModeNet m 0 n` into `nextModeEnt m e` for that entity.
  - `nextMode_ent_mState` turns that into `nextModeMState (sing m0) = Some m`.
  - `nextModeMState (sing m0)` computes to `None`, so `None = Some m` is a contradiction.

  Both interface lemmas hold under the intended stub definition (`nextModeEnt m e` iff the mode state of `e` is `<|_, m, _|>`), so the statement is false under that definition. Checked in Rocq (`--explore`). `Print Assumptions` lists only `nextMode_ent_ex`, `nextMode_ent_mState`, the `nextModeNet`/`nextModeEnt` parameters and model axioms:
  ```coq
  Lemma init_nextMode_net_refute (m m0 : Mode) (h : Interface) :
    (forall m i n, initStateNet m i n -> nextModeNet m i n) -> False.
  Proof.
    intro H.
    set (e := [| nilProc $||$ init m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
    assert (initStateNet m 0 [e]) as IS.
    { econstructor; [ | apply einConsLeft]. constructor. constructor.
      apply ComhCoq.ProcEquiv.bisim_refl. }
    apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
    inversion EIN; subst. unfold e in NM.
    apply nextMode_ent_mState in NM. simpl in NM. discriminate.
  Qed.
  ```
- **Ripple-up:** None. `grep` shows no user of `NARMisc.init_nextMode_net`. The only `init_nextMode_net` that is used is `NetAuxBasics.init_nextMode_net`, inside the commented-out proof of `NetAuxBasics.ovWait_ovReady_nextMode_net`, and that one already has `reachableNet n`. Not in the safety cone.
- **Suggested fix:** This lemma duplicates `NetAuxBasics.init_nextMode_net` without its hypothesis. Either delete it, or restate it as
  ```coq
  Lemma init_nextMode_net m i n :
    reachableNet n -> initStateNet m i n -> nextModeNet m i n.
  ```
  which is then proved by `exact (ComhCoq.NetAuxBasics.init_nextMode_net m i n)`. That version is itself admitted (label 7). It becomes provable once `nextModeEnt` is defined: the previous step is a `dormant -(mNext? m)-> init m` transition, which synchronises with the mode state outputting its next mode `m`.

## `msgBadPathNet_urgent`

- **Where:** `src/NARMisc.v` line 418 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n (proved relative to reachable_net_ent, reachableEnt stub and admitted EntAuxResults.del_listening; write-up warns del_listening may be false in the gotMsg case because position reads are not urgent).

- **Status:** FALSE (counterexample). It needs `reachableNet n`, and it is false whenever `Mode` is inhabited.
- **Intent:** if entity `i` of a network is on the "message bad" path (listener in `gotMsg`/`gotRange` with a possibly-incompatible received mode, or in `badOvlp`), the network cannot delay: those states are urgent.
- **Failure:** the statement has no reachability hypothesis. Its siblings `msgAbortPathNet_urgent` and `notifAbortPathNet_urgent` both carry `reachableNet n`. In the `badOvlp` case the `bad!` output only blocks delay if some component of the same entity can take it, and an arbitrary process term need not have one.
  Counterexample, verified in Rocq (`--explore`; it uses only the model axioms and stdlib, no admitted lemmas). For any `m : Mode` and `d : Delay`, take
  `[ [| nilProc $||$ nilProc $||$ badOvlp, origin, mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ]`.
  Then `msgBadPathNet 0` holds via `mbpBad` and `bisim_refl`. The network also delays by `d`: the only enabled action is `chanBad *!`, whose complement neither the interface nor the mode state can do, so `noSync` holds; the process delays to itself, the empty interface lists delay, and `sing m` delays. The file proves
  `msgBadPathNet_urgent_refute : (forall n n' d i, msgBadPathNet i n -> n -ND- d -ND> n' -> False) -> Mode -> False`.
  This is the same flaw that w1b-01 found in `notifBadPathNet_urgent` (same `badOvlp` witness).
- **Ripple-up:** the only use is `NARIncomp.incomp_tfs` (NARIncomp.v:553), inside a commented-out old proof (`*) Admitted.`). That context has `p : reachableNet n`, so the fixed statement would serve it with one extra argument. Not in the safety cone.
- **Suggested fix:**
  ```coq
  Lemma msgBadPathNet_urgent (n n' : Network) (d : Delay) (i : nat) :
    reachableNet n -> msgBadPathNet i n -> n -ND- d -ND> n' -> False.
  ```
  This is proved in my file as `msgBadPathNet_urgent_fixed`. It compiles, and its assumptions are the model axioms, `reachable_net_ent`, the `reachableEnt` stub and the admitted `EntAuxResults.del_listening` (not blacklisted). The proof takes the entity delay from `del_net_ent`, gets `listeningStateEnt e` from `del_listening`, and refutes each `msgBadPathEnt` case: `gotMsg` enables `chanPos;?[l]`, `gotRange` enables `chanMCurr;?[m]` and `badOvlp` enables `chanBad *!`. `bisim_dae` moves the enabled action to `listening`, which cannot do it (inversion).
- **Caveat for the owner (semantic issue, analysis only):** in the `mbpMsg` (`gotMsg`) case the fixed proof leans on `del_listening`, and I believe `del_listening` (and `gotMsgStateEnt_urgent`) are false in the current entity semantics. `gotMsg` waits on `chanPos<vL>?`, and the position read is the entity rule `stepDePosRead`, which involves neither interface nor mode state. `noSync`/`noSyncNow` (EntityLanguage.v:196-209) only forbid delay when the *interface or mode state* can do the complement. No software component ever outputs on `chanPos`, so `stepTpPar` does not block either. So an entity whose listener sits in `gotMsg` can delay, for example with the broadcaster `sleeping` and the overlap `dormant`, which looks reachable. Fixing this needs a semantic change rather than a new hypothesis: for example, add `forall l', ~discActEnabled p (chanPos ;? [basePosition l'])` (and the same for the delay derivatives `p'`) as a premise of `stepTeDel`, or make position reads urgent in `noSyncNow`. With that change, `del_listening` and `msgBadPathNet_urgent_fixed` become plausible. The `gotRange` and `badOvlp` cases don't depend on this. `gotRange` is urgent even without reachability, because the mode state always offers `chanMCurr .! m`.
- **Partial proof:** `NARMisc.msgBadPathNet_urgent.v` (in the prover work area, not committed; the audited copy is under [`../evidence/audit/`](../evidence/audit/)) contains the counterexample (`msgBadPathNet_urgent_cex`, `msgBadPathNet_urgent_refute`) and the fixed proof (`msgBadPathNet_urgent_fixed`), both compiled.

## `tfsState_not_currSince`

- **Where:** `src/NARMisc.v` line 437 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:failSafeSucc-may-be-identity`
- **Fix (audit summary):** Add ~ failSafe m (incomp_tfs gets it from Main H4); alternatively a model axiom failSafeSucc m <> m.

- **Status:** NEEDS-HYPOTHESIS (`~ failSafe m`). The statement is not derivable from the model axioms: it fails in admissible models where `failSafeSucc m = m` for a fail-safe `m`.
- **Intent:** thesis Listing 7.35: "when a transition to a fail-safe mode is completed, the currSince relation ceases to hold". The overlap component's only way out of the tfs states is `tfsListen --chanUnpause!--> dormant`. Before that, `tfsCurr --chanMCurr!--> tfsBc` installed `failSafeSucc m'` as the current mode, where `m'` is the mode read at `tfsStart`.
- **Failure:** the intuition needs the fail-safe write to actually *change* the current mode away from `m`. The axioms don't guarantee that.
  - Nothing in `ComhBasics.v` forbids `failSafeSucc m = m` or `m -mtr-> m`. The only constraints are `failSafeSuccFS` and `failSafeSucc_successor : m -mtr-> failSafeSucc m`. Take a model in which `m` is fail-safe and `failSafeSucc m = m`.
  - `currSince m` for such an `m` is reachable: `stepDeTest` lets the environment initiate a transition to `m`, and the normal path `dormant -> init m -> ovWait/ovReady (nextSince m) -> switchBc -> switchCurr -> switchListen` (`currSinceBase`) completes it.
  - The listener then goes `badOvlp --chanBad!-->` and the overlap goes `dormant --chanBad?--> tfsStart`. From there: `tfsStart` reads `m`; `tfsNext m` writes next mode `failSafeSucc m = m` (`stepMsInit`); `tfsCurr` waits for the timeout and does `chanMCurr!` (`stepMsSwitch`), so the current mode is still `m`.
  - `currModeNet m` holds at every step, so `currSinceDisc` keeps `currSince m t` alive through `tfsBc` and `tfsListen`. At the `tfsListen -> dormant` step we have `tfsStateNet i n`, `~tfsStateNet i n'` and `currSince m t i n p`, which contradicts the lemma.
  - This can't be exhibited inside Rocq because `Mode`/`failSafeSucc` are abstract axioms, but it shows the goal is independent of them.
  - Within Rocq, the proof goes through except for the `failSafe m` branch. The remaining goal is `TS : tfsStateNet i n, NTS : ~tfsStateNet i n', CS : currSince m t i n p, FS : failSafe m |- False`. No lemma in scope (only `currSince_curr` talks about `currSince`) refutes it.
- **Ripple-up:** `in_safety_cone=False`.
  - Used in the commented-out proof of `NARIncomp.incomp_tfs` (currently `Admitted`). `incomp_tfs` is applied in `Main.safety_aux`, where `H4 : ~ failSafe m2` is available, so the fix can be threaded through.
  - The admitted `NARInsuff.tfs_pres_not_currSince` (second disjunct `forall m' t' p', ~currSince m' t' i n p'`) has the same flaw and needs the same restriction. Its user in `NARInsuff` works under `~ sufficient`/`currSince m` hypotheses; check there whether `~failSafe m` is at hand.
- **Suggested fix (preferred):**
  ```coq
  Lemma tfsState_not_currSince (m : Mode) (t : Time) (i : nat) (n n' : Network)
    (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
    ~ failSafe m -> tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
  ```
  `incomp_tfs` then gets `~ failSafe m` too (Main passes `H4`).
  I proved this fixed version in Rocq (`--explore`, helper `tfsState_not_currSince_fixed`, ends in `Qed`). The proof is `currSince_curr` plus the existing proved `NetAuxBasics.tfs_currMode_disc_pres`, which in turn uses the admitted `tfsListen_failSafe_net` and the fwd-tracking lemmas.
  An alternative is a model axiom `failSafeSucc m <> m`. It is weaker than it looks: you would also need a new invariant that the next mode in `tfsCurr` is exactly `failSafeSucc` of the current mode, and `tfsCurr_failSafe` only says it is fail-safe. So the hypothesis route is preferable.
- **Partial proof:** `NARMisc.tfsState_not_currSince.v` in this directory:
  ```coq
  Lemma tfsState_not_currSince_fixed (m : Mode) (t : Time) (i : nat) (n n' : Network)
    (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
    ~ failSafe m ->
    tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
  Proof.
    intros NFS TS NTS CS. apply NTS.
    eapply tfs_currMode_disc_pres; [exact w | | exact NFS | exact TS].
    eapply currSince_curr. exact CS.
  Qed.
  (* original statement: *)
  Proof.
    intros TS NTS CS.
    destruct (fsDecMode m) as [FS | NFS].
    2: { eapply tfsState_not_currSince_fixed; eassumption. }
    (* stuck: failSafe m branch *)
  Admitted.
  ```

## `msgBad_disc_net`

- **Where:** `src/NARMisc.v` line 445 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `other:msgBadPathEnt-does-not-exclude-tfs-overlap`
- **Fix (audit summary):** Add ~ tfsStateNet i n (or ~tfsStateProt in msgBadPathEnt), or weaken the conclusion with \/ tfsStateNet i n'.

- **Status:** FALSE (counterexample). The key step is verified in Rocq; the path part is argued precisely below. The fix is NEEDS-HYPOTHESIS: add `~ tfsStateNet i n`, or weaken the conclusion.
- **Statement (frozen, `src/NARMisc.v:445`):**
  ```coq
  Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
    (p : reachableNet n) (w : n -NA- a -NA> n') :
    msgBadPathNet i n -> currModeNet m i n ->
    msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w).
  ```
- **Intent:** while the listener handles a possibly incompatible message (`gotMsg` → `gotRange` → `currPincCheck`≈`badOvlp`), any discrete step either keeps it on that path, or is the `chanBad` handshake that starts tfs right now (`tfsBase`, time 0).

### Failure

The proof sketch under the lemma says: *"We can eliminate tfsListen and tfsCurr because ... the definition of msgBadPath dictates that an entity is not tfs."* The current definition does not say that. `msgBadPathEnt` (`EntAuxDefs.v:98`) only constrains the listener component: `gotMsg`/`gotRange` with `possiblyIncompatible`, or `badOvlp`. Nothing excludes the overlap being in `tfsCurr` or `tfsListen`, and both of those accept `chanBad?` and stay where they are:

```
tfsCurr   := chanAbort? tfsCurrN   $+$ chanBad? tfsCurrN   $+$ chanMCurr!tfsBcN
tfsListen := chanAbort? tfsListenN $+$ chanBad? tfsListenN $+$ chanUnpause!dormantN
```

So the `badOvlp` case has a step `w` (the internal τ from `chanBad!`/`chanBad?`) after which:
- the listener is `listening`, so `msgBadPathNet i n'` is false;
- the overlap is still `tfsCurr`/`tfsListen` and was *not* just started. `tfs m zeroTime i n' (reachNetDisc n n' a p w)` can only come from `tfsDisc` back along `p` to the last `tfsStart`. That needs both zero elapsed delay since then **and** `currModeNet m` at that `tfsStart`. `reachableNet` is a `Type`, so `tfs` really is indexed by the concrete path, and proof irrelevance doesn't help.

#### Verified in Rocq (`NARMisc.msgBad_disc_net.v`, `--explore`, rc=0)

`msgBad_disc_net_onestep` proves this for any `P1 l h k`, with `e := [| P1 $||$ tfsListen $||$ badOvlp, l, h, k |]` and `e' := [| P1 $||$ subProcTerm (listsToSub [] []) (liftNameProc tfsListenN) $||$ liftNameProc listeningN, l, h, k |]`:
- `msgBadPathNet 0 [e]`
- `tfsListenStateNet 0 [e]`
- `[e] -NA- anTau -NA> [e']`
- `~ msgBadPathNet 0 [e']`
- `tfsListenStateNet 0 [e']`

The mode state `k` is unchanged. Helpers:
- `msgBad_disc_net_tgt_not`: an entity whose listener is `listening` is never `msgBadPathEnt`. It uses `bisim_dae`. `listening` cannot do `chanPos?`, `chanMCurr?` or `chanBad!`.
- `msgBad_disc_net_tfsListen_unfold`: the derivative is bisimilar to `tfsListen`.

#### Full reachable counterexamples (the path part, argued by hand)

**(A) No delays.** This works in any model with a fail-safe `F` and a proof `p0 : F -mtr-> failSafeSucc F`, where `FS := failSafeSucc F <> F` and `modeTransTime F FS p0 = zeroTime`. Single-entity network, starting at `[[| procProtocol, l, h0, F |]]`, which is initial. All steps are discrete:
1. The environment sends `anIn [-[baseMode M; basePosition l], l, r-]`. Then `chanInProc` takes the listener to `gotMsg M l`.
2. `chanPos` takes it to `gotRange M r0` with `r0 <= 0`.
3. `chanMCurr` reads `F`, giving `currPincCheck F M r0` ≈ `badOvlp`, because `possIncDist F M > 0 >= r0`. This state is `msgBadPath`.
4. `chanBad` syncs with `dormant`. The overlap moves to `tfsStart` and the listener to `listening`.
5. `tfsStart` reads `F` and moves to `tfsNext F`. That writes `FS` (`stepMsInit p0`, timer `0`) and moves to `tfsCurr`. `chanMCurr!` (`stepMsSwitch`) moves to `tfsBc`, and the mode is now `FS`. `chanTrans!` syncs with `sleeping`'s `chanTrans?` and moves to `tfsListen`.
6. Repeat steps 1–3. The listener is now `currPincCheck FS M r0` ≈ `badOvlp`. Call this state `n`. It satisfies `msgBadPathNet 0 n` and `currModeNet FS 0 n` (`currMode_intro`).
7. `w` is the `chanBad` sync with `tfsListen`, as in the verified step. Call the result `n'`.

In `n'`, `~msgBadPathNet 0 n'` (verified). For `tfs FS zeroTime 0 n' (reachNetDisc n n' _ p w)`, invert along `p`. Every state from the end back to the `tfsStart` of step 4 is not `tfsStart`, so `tfsBase` fails and only `tfsDisc` applies. At the `tfsStart` state, `tfsBase` needs `currModeNet FS` while the mode is `F <> FS` (`currMode_ent_ex` and uniqueness). `tfsDisc` needs `tfs` at the previous state, where the overlap is `dormant`. That fails because `tfsDisc` needs `tfsStateNet` there and `tfsBase` needs `tfsStart`. So `tfs` is false, and so is the conclusion.

**(B) With a delay.** This needs only `modeTransTime F FS p0 > 0`. Same start. Reach `tfsCurr` with mode state `<|F, FS, T|>`, `T > 0`. Delay by `d < T`. This is legal: `chanMCurr!` is not enabled before the timeout, and there are no complementary actions among `sleeping`, `tfsCurr` and `listening`, so `noSync` and `stepTpPar` hold. Then repeat steps 1–3 to reach listener ≈ `badOvlp` (state `n`, mode `F`). Then `w` is the `chanBad` sync with `tfsCurr` (`n'`). `~msgBadPathNet 0 n'` holds as before. `tfs F zeroTime 0 n'` would have to pass back through the `reachNetDel` step. There `tfsBase` fails, because the overlap is in `tfsCurr`. `tfsDel` gives time `t +dt+ d > 0 <> zeroTime`. So the conclusion is false again.

The other cases are a second, independent route. In the `gotMsg`/`gotRange` cases, `w` can be the overlap's `tfsCurr → tfsBc` mode switch. That changes `currModeMState` from `m` to `failSafeSucc m`. `possiblyIncompatible` can then fail (`minDistComp fs _ = 0`), and the RHS fails whenever a delay elapsed since `tfsStart`. It does whenever `modeTransTime > 0`.

### Ripple-up

- Not in the safety cone (per `show`).
- The only user is `NARIncomp.instant_incomp_tfs` (`NARIncomp.v:411`, closed with `Qed` relative to this lemma). There, `currSince m t i n p` does **not** exclude the overlap being in `tfsCurr`. `currSince` survives until the `tfsCurr` mode switch, so scenario (B) also looks like a counterexample to `instant_incomp_tfs`: message received at time 0, `0 < t`, the entity already tfs from an earlier event. Through that lemma the issue reaches the (commented-out) proof of `incomp_bad` in `NARIncomp.v`.

### Suggested fix

Either option needs approval, since each changes a statement.

**Option 1: restore the sketch's assumption as a hypothesis.**
```coq
Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  msgBadPathNet i n -> currModeNet m i n -> ~ tfsStateNet i n ->
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w).
```
(Equivalently, add `~ tfsStateProt p` to each `msgBadPathEnt` constructor.) The sketch then goes through:
- `chanBad!` can only meet `dormant`/`ovWait`, both going to `tfsStart`. This gives `tfsBase`, and the internal τ leaves the mode state alone.
- The only mode changer is `chanMCurr!`, from `switchCurr` or `tfsCurr`. `switchCurr` forces the listener `paused` (`paused_switch_net`), which is disjoint from `msgBadPath`. `tfsCurr` is excluded by the new hypothesis.

`instant_incomp_tfs` would then need to case-split on `tfsStateNet i n`.

**Option 2: weaken the conclusion.** This keeps the callers' hypotheses.
```coq
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w) \/ tfsStateNet i n'.
```
This is provable: if the overlap is already tfs while the listener is on `msgBadPath`, then it stays tfs. The only exit is `tfsListen --chanUnpause!--> dormant`, which needs the listener in `listening`/`paused`. `instant_incomp_tfs` and `incomp_bad` would need the same extra disjunct ("already transitioning to fail-safe"), which is arguably the right reading of the thesis.

### Partial proof

None of the target itself. The Rocq file holds the verified counterexample step and the disjointness helpers.

## `tfs_zero_disc_pres`

- **Where:** `src/NARMisc.v` line 453 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:modeTransTime-may-be-zero`
- **Fix (audit summary):** Either add model axiom 0 < modeTransTime m m' p (owner approval) or add hypothesis currSince m' t i n p (only caller has it).

- **Status:** NEEDS-HYPOTHESIS (missing model axiom: mode transition times are positive). False in
  models of the current axioms where `modeTransTime m (failSafeSucc m) _ = 0`.
- **Intent:** while an entity is `tfs m` with elapsed time 0, any discrete step keeps it `tfs m 0`, i.e. a
  fail-safe transition cannot *complete* within the instant it starts.
- **Failure:** `tfs m 0 i n p` is built only by `tfsBase` (`tfsStart`) and `tfsDisc` steps (`tfsDel` adds a
  positive delay, so cannot give time 0). The in-file sketch says a `tfs m 0` entity is in `tfsStart`,
  `tfsNext` or a *delay-guarded* `tfsCurr`. The guard is the mode state: `tfsNext m` does
  `chanMNext<failSafeSucc m>!`, which synchronises with `stepMsInit`, giving mode state
  `<| m, fSucc m, modeTransTime m (fSucc m) pf |>`; `tfsCurr` leaves only by `chanMCurr!`, which synchronises
  with `stepMsSwitch`, enabled only on `<| _, _, zeroTime |>`. Nothing in `ComhBasics.v` says
  `0 < modeTransTime m m' pf` (only `modeTransTime_bound : modeTransTime m m' p <= trans m`; the thesis
  Def. 5.1 doesn't require positivity either). With `modeTransTime m (fSucc m) _ = 0` (consistent with
  all model axioms), the following all-discrete, zero-delay run exists (the thesis's own Examples 5.12/5.13,
  thesis.txt ~l.7015-7050, minus the delay in tfsCurr):
  `ovWait|badOvlp --τ(bad)--> tfsStart` (tfsBase: tfs m 0) `--mCurr<m>?--> tfsNext m --mNext<fSucc m>!-->
  tfsCurr` (mode state `<|m,fSucc m,0|>`) `--mCurr!--> tfsBc --τ(trans)--> tfsListen` (still tfs m 0 by
  tfsDisc) `--τ(unpause, listener in listening)--> dormant`. In the last step `n'` has the overlap in
  `dormant`, so neither `tfsBase` (needs tfsStart) nor `tfsDisc` (needs `tfsStateNet i n'`) can derive
  `tfs m 0 i n' (reachNetDisc ...)` (`tfsDel` has the wrong reachability index). So the conclusion fails.
  Not Rocq-checkable as a concrete counterexample: `Mode` is an abstract axiom type and `currModeNet` (in
  `tfsBase`) an opaque `Parameter`, so no concrete reachable network can be built; the argument is on
  paper against the intended semantics.
- **Ripple-up:** only user: `NARIncomp.instant_incomp_tfs` (NARIncomp.v:414). `show` says
  `in_safety_cone=False`. Related: `NARMisc.tfs_transGuard` relies on `tfsNext_tfs_zero` and
  `modeTransTime_bound` only, so it isn't affected.
- **Suggested fix:** either
  1. *(model axiom, owner approval)* add to `ComhBasics.v`
     `Axiom modeTransTime_pos : forall m m' (p : m -mtr-> m'), 0 < modeTransTime m m' p.`
     Then the lemma should be provable by the in-file sketch, via the strengthened invariant
     `tfs m zeroTime i n p -> tfsStartStateNet i n \/ (exists m', tfsNextStateNet m' i n) \/
      (tfsCurrStateNet i n /\ exists t', transGuard t' i n /\ 0 < t')`,
     proved by induction on `tfs` with net-level fwd-tracking (`tfsStart_next_net`, `tfsNext_next_net`,
     `mState_disc_pres`, `mState_switch_states`). That's sizeable inter-component work (label 4 was optimistic).
  2. *(statement change, cheaper; recommended)* add the hypothesis the only caller already has
     (`H : currSince m t i n p` in `instant_incomp_tfs` at the `apply tfs_zero_disc_pres` line):
     ```
     Lemma tfs_zero_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m m' : Mode)
       (t : Time) (p : reachableNet n) (w : n -NA- a -NA> n') :
       currSince m' t i n p -> tfs m zeroTime i n p ->
       tfs m zeroTime i n' (reachNetDisc n n' a p w).
     ```
     **Rocq-checked** (explore mode, `NARMisc.tfs_zero_disc_pres.fix.v`) relative to admitted
     `tfs_rel_state`, `tfsState_not_currSince` and conjecture `tfsStateNet_dec`:
     ```
     intros CS T. destruct (tfsStateNet_dec i n') as [D|D].
     - apply tfsDisc; assumption.
     - exfalso. eapply (tfsState_not_currSince m' t i n n' p a w);
       [eapply tfs_rel_state; eassumption | exact D | exact CS].
     ```
     Caller change: `eapply tfs_zero_disc_pres; eassumption`.
     Caveat for the owner: `tfsState_not_currSince` can itself fail if `failSafeSucc m = m` is allowed
     (the mode doesn't change at `tfsCurr -> tfsBc`, so `currSince m` survives through the tfs run). It
     needs `failSafeSucc m <> m`, or "m not fail-safe", as a hypothesis. In `instant_incomp_tfs`, m is
     the current mode of an entity that just got an incompatible message, so non-fail-safe is natural there.
- **Partial proof:** none for the statement as given (no positivity axiom to use).
