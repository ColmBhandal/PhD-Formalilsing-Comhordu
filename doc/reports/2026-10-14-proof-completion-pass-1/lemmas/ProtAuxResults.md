# Unproved lemmas in `ProtAuxResults`

[← Lemma index](README.md) · [Report summary](../README.md)

11 lemmas here could not be proved as stated, 3 of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `listening_AN_prot`

- **Where:** `src/ProtAuxResults.v` line 354 · **Lemma** · 2015 label: `C` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `listener-arity` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add length v = 2 (proved) or, better, make listening input 3-tuples [vR, vM'', vL'] to match the interface and require length v = 3; NetAuxBasics.incomingNetNotif_del then needs a notification-shape invariant.

- **Status:** FALSE (counterexample, verified in Rocq)
- **Intent:** a protocol process whose listener component is in the `listening` state can accept an adaptation notification on channel `chanAN`.
- **Failure:** the statement quantifies over an arbitrary tuple `v`, but `listening` only inputs on `chanAN` through the prefix `chanAN$<[vR, vM'']>$? ...`, and `stepDpIn` needs `length v = length [vR; vM''] = 2`. No other component of a protocol process (broadcast: inputs on `chanWake`/`chanTrans`; overlap: on `chanMNext`/`chanAbort`/`chanBad`/...) inputs on `chanAN`, and parallel synchronisation produces only `tauAct`. So for any `v` with `length v <> 2` the conclusion fails.
  Counterexample: `p := procProtocol = sleeping $||$ dormant $||$ listening`, `v := []`. Verified (compiles with `Qed`, explore run):
  ```
  Lemma listening_AN_prot_counterexample :
    listeningStateProt procProtocol /\ ~ discActEnabled procProtocol (chanAN ;? []).
  Proof.
    split.
    - unfold listeningStateProt, procProtocol. constructor. unfold listeningState.
      apply bisim_refl.
    - intro D. inversion D as [q TR]. clear D. unfold procProtocol in TR.
      repeat invert_trans;
      try match goal with [H : length _ = length _ |- _] => simpl in H; inversion H end.
  Qed.
  ```
- **Deeper modelling issue (affects the fix):** notifications that actually reach the notification list have length 3, not 2. `stepIntFwdOut` (InterfaceLanguage.v ~l.310) enqueues `(baseDistance r) :: v` where `v` is the outgoing message, and messages are `[baseMode m, basePosition l]` (`bcReady`/`ovReady` output `chanOutProc$<[m, l]>$!`). NARInsuff.v also uses `incomingNetNotif [baseDistance r, baseMode m, basePosition l] ...`. So with the current `listening` definition the listener can **never** accept a real notification, even with a length hypothesis on `v`.
- **Ripple-up:** in the safety cone. Used in NetAuxBasics.v `incomingNetNotif_del` (lines ~699 and ~707) with an arbitrary `v` taken from `incomingNetNotif v t i n`. That proof breaks if this lemma is false; the user would need a shape invariant on notifications in reachable networks.
- **Suggested fix (two parts):**
  1. Make the listener accept 3-tuples, matching the interface: in SoftwareLanguage.v,
     `Definition listening := chanAN$<[vR, vM'', vL']>$? checkRangeN $([eVar vM'', eVar vR])$ $+$ ...`
     (any third fresh variable, `vL'` is unused in `checkRange`). Then restate
     ```
     Lemma listening_AN_prot p v :
       length v = 3%nat -> listeningStateProt p -> discActEnabled p (chanAN ;? v).
     ```
  2. In `incomingNetNotif_del`, discharge `length v = 3` from a reachability invariant ("every element of every notification list in a reachable network has length 3"), which follows from `stepIntFwdOut` plus the fact that a protocol process only outputs `[m, l]` on `chanOutProc` (`bc_outProc_out`, `ovlp_outProc_out`, `listener_outProc_out_not`).
  With the current `listening` definition, the analogous statement with `length v = 2%nat` is provable (checked, `Qed`):
  ```
  Lemma listening_AN_prot_fixed p v :
    length v = 2%nat -> listeningStateProt p -> discActEnabled p (chanAN ;? v).
  Proof.
    intros L LS. inversion LS as [p1 p2 p3 Q]; subst.
    apply daeParR; apply daeParR.
    eapply bisim_dae; [apply bisim_symm; apply Q | ]. unfold listening.
    apply daeSumL; apply daeSumL; apply daeSumL. apply dae_inPfx. simpl. rewrite L. reflexivity.
  Qed.
  ```
  The same script proves the 3-variable version after fix 1 (with `3%nat`).

## `ovWait_del_pres`

- **Where:** `src/ProtAuxResults.v` line 658 · **Lemma** · 2015 label: `#delay-pres` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:timers-count-down-under-delay` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude exists x' y', ovWaitState m t x' y' p' (proved, model axioms only, enough for del_pres_nextSinceState), or the quantitative minusTime version (proved).

- **Status:** FALSE (counterexample, verified in Rocq). Corrected statements are proved (see below).
- **Intent:** A delay keeps the overlap-waiting process in the `ovWait` state for the same mode `m` and time `t`. Thesis Remark 5.10 / p.~6390ff: `ovWait(m',t,t')` after a delay is the same sum with both timers decremented, e.g. `ovWait(m',21,9) --9--> ... + ε(0)chanPos?... + ε(3)cPause!...`.
- **Failure:** `ovWait m t x y` contains two timeouts, `$<y>$chanPos?...` and `$<x>$chanPause!switchBcN(m)`. A delay `d` counts both down (`stepTpDelSub` gives `$<x-d>$`, and `stepTpDelAdd` lets the delay run past expiry into the continuation). So `p'` is (bisimilar to) `ovWait m t (x-d) (y-d)`, truncated at 0, never to `ovWait m t x y`.
  Concrete counterexample, for every `m t d`: `x = y = d`, `p = ovWait m t d d`. Then `p -PD- d -PD> p'` with `p' = ... + $<0>$chanPos?... + $<0>$chanPause!...`. `p'` can do `outAct chanPause [m]` immediately via `stepDpTimeOut`, but `ovWait m t d d` cannot, because its timer is `d > 0`. So `~ p' ~p~ ovWait m t d d`. Lemmas `ovWait_del_pres_cex` and `ovWait_del_pres_refuted` in `ProtAuxResults.ovWait_del_pres.v` prove this; they compile in `--explore` and rest only on model axioms and the stdlib classical axioms.
- **Ripple-up:** The only user is `ProtAuxResults.del_pres_nextSinceState` (line 680, proved, `lets AUX : ovWait_del_pres H U0. eapply nexsOvwSt`). That is used by `NARMisc.v:166`. The target is in the safety cone. `del_pres_nextSinceState` only needs *some* `ovWaitState m t x' y' p'`, so nothing up the chain breaks under the existential fix below. Related: `NetAuxBasics.ovWait_del_pres_net` (line 1026, an iff with the *same* `x y` across a network delay) is false for the same reason. It is used in NARMisc's commented-out `(*R*)` proof (line 494). `ovWait_del_pres_bkwd_net_strong` already has the correct `x +dt+ d` shape.
- **Suggested fix:** replace the statement with either of the following (both proved, `Qed`, in the HELPERS of my `.v` file):
  ```coq
  (* minimal: sufficient for del_pres_nextSinceState, holds for every d *)
  Lemma ovWait_del_pres m t x y p p' d :
    ovWaitState m t x y p -> p -PD- d -PD> p' ->
    exists x' y', ovWaitState m t x' y' p'.
  (* quantitative, for delays within both timers *)
  Lemma ovWait_del_pres_strong (m : Mode) (t x y : Time) (p p' : ProcTerm) (d : Delay)
    (Hx : d <= x) (Hy : d <= y) :
    ovWaitState m t x y p -> p -PD- d -PD> p' ->
    ovWaitState m t (minusTime x d Hx) (minusTime y d Hy) p'.
  ```
  The existential version needs one helper, `$<0>$ q ~p~ q` (`ovWait_del_pres_zero_bisim`). It covers the case where a timer is overrun: `$<x>$P -d-> P` via `stepTpDelAdd` when `d > x`, and `P ~ $<0>$P`. With that and `choice_bisim_context`, the delayed term is bisimilar to `ovWait m t x' y'`. To drop it into `del_pres_nextSinceState`, change its first bullet to `destruct (ovWait_del_pres H U0) as [x' [y' AUX]]. eapply nexsOvwSt; eassumption.` (checked as `ovWait_del_pres_user_ok`).
- **Partial proof:** the whole of `ProtAuxResults.ovWait_del_pres.v` (in the prover work area, not committed; the audited copy is under [`../evidence/audit/`](../evidence/audit/)) HELPERS. The helpers are `ovWait_del_pres_zero_bisim`, `ovWait_del_pres_timer_aux`, `ovWait_del_pres_fixed` (existential), `ovWait_del_pres_timer_aux2`, `ovWait_del_pres_strong` and `ovWait_del_pres_user_ok`. The counterexample is by the earlier prover ProtAuxResults-3, and I re-verified it.

## `reachableProt_triple`

- **Where:** `src/ProtAuxResults.v` line 843 · **Theorem** · 2015 label: `Need support lemmas: disc pres & del pres for ovlp, broadcast, listener state components.` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `incomplete-definition (overlapState/listenerState)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Define broadcastState/overlapState/listenerState as closure of sleeping/dormant/listening under component steps (compReach); reachableProt_triple then holds (reachableProt_triple_fix proved, model axioms only); consumers must be re-proved by induction on compReach.

- **Status:** FALSE (counterexample). The negation can be proved from the model axioms alone, so **the admitted lemma is inconsistent**. Add it to the blacklist: any proof that uses it, directly or through the `reachprot`, `urgency_pre_tac*` or `reach_net_prot_tac` tactics, is vacuous.

- **Intent:** every process reachable from `procProtocol` (`sleeping || dormant || listening`) through the process-level semantics has the form `p1 || p2 || p3`, where p1 is a broadcast-component state, p2 an overlap-component state and p3 a listener-component state. Users invert `protocolState` to get `broadcastState p1`, `overlapState p2` and `listenerState p3`, and pass these to the brute-force lemmas (`bc_outProc_out`, `listen_mCurr_out_not`, `link_reach_triple_tau`, ...).

- **Failure:** three independent counterexamples, all compiled in `--explore` mode in `ProtAuxResults.reachableProt_triple.v` (this dir, HELPERS section). `Print Assumptions` shows only model axioms plus stdlib classical/FE/PI, and no admitted lemma.
  1. **`overlapState` is incomplete.** Its definition says `(*INCOMPLETE- Need to add constructors for ALL the overlap states.*)` and has only `dormant` and `ovWait`. The step `procProtocol -PA- chanBad ;? [] -PA> sleeping $||$ tfsStartN $||$ listening` takes dormant's `chanBad? tfsStartN` branch. `tfsStartN` is not bisimilar to `dormant` or to any `ovWait m t x y`, because both of those can do `chanAbort ;? []` and `tfsStart` can only input on `chanMCurr`. Lemmas: `reachableProt_triple_cex_step`, `reachableProt_triple_cex_not_ovlp`, `reachableProt_triple_cex`, and
     ```
     Lemma reachableProt_triple_false : ~ (forall p, reachableProt p -> protocolState p).
     ```
     This is the statement under review, refuted.
  2. **`listenerState` is incomplete.** It has no `paused`, `gotMsg` or `gotRange`. The step `procProtocol -PA- chanPause ;? [] -PA> sleeping $||$ dormant $||$ pausedN` leads to `pausedN`, which is bisimilar to none of the 6 listener states: each of those has an enabled action that `paused` (which only does `chanUnpause?`) lacks. Lemmas: `reachableProt_triple_cex2_not_list`, `reachableProt_triple_cex2`.
  3. **Typing gap, which no completion with named states fixes.** At process level, inputs are unconstrained (`stepDpParL/R` with `inAct` and any `list BaseType` of the right length). So an ill-typed value can be input. Listening inputs `chanAN ;? [baseTime 0; baseTime 0]`, giving `checkRangeN([0,0])`. Both of its guards (`bSufficient` and its negation) evaluate to `false` through `evalBoolExpFunTot` (`None ↦ false`), so this state has **no discrete transitions at all** (`reachableProt_triple_stuck_dead`). Every named listener state with `Mode`/`Distance`/`Position` parameters has an enabled discrete action, so the stuck state is bisimilar to none of them (`reachableProt_triple_cex3`). The same holds for any completed `listenerState` built from named states. Similar ill-typed inputs on `chanWake`, `chanMNext` or `chanMCurr` give broadcast and overlap states with ill-formed parameters. Those break `broadcastState`, even though its 3 constructors are complete by name (argued by hand, not mechanised).

- **Ripple-up:** in the safety cone. Direct users: `NARMsgPosition.sent_pos_bound`, `NARNonFS_currSince.nonFS_currSince`. Through `reach_net_prot_tac` (NetAuxBasics): `NARIncomp.msgAbort_not_nextSince` and `NARInsuff.notifAbort_not_nextSince`. Through `reachprot` and `urgency_pre_tac*` (EntAuxResults): `tfsStartStateEnt_urgent`, `tfsListen_urgent`, `tfsNext_urgent`, `bcReady_urgent`, `ovAbort_urgent`, `tfsBc_urgent`, `switchBc_urgent`, `swithcCurr_urgent`, `switchListen_urgent` and the other `*_urgent` lemmas. Accepted wave-1 proofs whose files mention these names, so their `.ok` needs re-auditing with `Print Assumptions`: `EntAuxResults-2/{abortOvlpStateEnt_urgent, del_listening_pre, del_ovlp}`, `NARInsuff/notifAbort_not_nextSince`, `w1b-20/NetAuxBasics.del_listening_net`. Because the lemma is refutable, everything proved from it is vacuous. Its downstream uses are sound only once `protocolState` is redefined as below.

- **Suggested fix (definition change; needs owner approval):** define the component predicates as closure under the component-level semantics instead of as finite lists of named states:
  ```
  Inductive compReach (p0 : ProcTerm) : ProcTerm -> Prop :=
    | crBase : compReach p0 p0
    | crDisc p p' a : compReach p0 p -> p -PA- a -PA> p' -> compReach p0 p'
    | crDel  p p' d : compReach p0 p -> p -PD- d -PD> p' -> compReach p0 p'.
  Definition broadcastState := compReach sleeping.
  Definition overlapState   := compReach dormant.
  Definition listenerState  := compReach listening.
  (* protocolState unchanged *)
  ```
  With this, `reachableProt_triple` is **proved** (the validated form is `reachableProt_triple_fix` in my `.v`: induction on `reachableProt`, inverting par/sync disc steps and `stepTpPar` delays; about 15 lines). The brute-force consumers (`bc_outProc_out`, `ovlp_outProc_out`, `prot_outProc_in_not`, `bc_mCurr_out_not`, `listen_mCurr_out_not`, `listener_outProc_out_not`, `link_reach_triple_tau`, ...) then become induction-on-`compReach` tracking lemmas. They should stay true because they constrain only which actions a reachable component can do, and ill-typed values cannot produce well-typed outputs such as `[baseMode m, basePosition l]`. Their conclusions about named states (for example `bcReadyState m l p`) still need well-typed matching, which follows from the output's values.
  Alternative: keep the named predicates but (a) add every missing constructor (`init`, `ovReady`, `switchBc/Curr/Listen`, `ovAbort`, `tfs*` for overlap; `paused`, `gotMsg`, `gotRange` for listener) **and** (b) restrict `reachableProt` to well-typed inputs, or state the lemma only for software components of reachable networks. (b) is needed because of counterexample 3. This is a larger change.

- **Partial proof:** none for the stated lemma, which is impossible. See the `.v` for the counterexamples and the validated replacement (`reachableProt_triple_fix`).

## `currOK_listening_track`

- **Where:** `src/ProtAuxResults.v` line 377 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:nextEq-else-branch-returns-to-listening (plus untyped-input)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude a = chanMStable *? \/ exists v, a = chanMNext ;? [v] /\ v <> baseMode m (proved, model axioms only).

- **Status:** FALSE (counterexample checked in Rocq; needs one `m : Mode`). A corrected statement is **proved** in the same file.
- **Intent:** the listener goes from `currOK m` back to `listening` only by reading `chanMStable` from the mode state, i.e. when there is no pending mode transition.
- **Failure:** `currOK m'' = chanMStable? listeningN $+$ chanMNext<vM'>? nextEqN[vM', m'']` and `nextEq m' m'' = (m' =b= m'') $> abortOvlpN $+$ !~(m' =b= m'') $> listeningN`.
  - Conditionals are not steps in this semantics, so `nextEq v m ~p~ listening` whenever `v <> baseMode m`. The `ProcEquiv.if_then_bisim_false` lemma gives exactly this.
  - So `currOK m -(chanMNext ;? [v])-> nextEqN[v, m]`, and the derivative is in `listeningState`, with action `<> chanMStable *?`.
  - The thesis (`thesis.txt` l. 6724, Ch. 5: "Otherwise the process effectively returns to the listening state which is essentially the 'else' branch of the process nextEq") describes exactly this path, so it is intended protocol behaviour. Only the lemma is wrong.
  - Rocq evidence (`ProtAuxResults.currOK_listening_track.v`, --explore, all `Qed`; `Print Assumptions` shows only model axioms and stdlib axioms, **no admitted lemmas**):
    - `currOK_listening_track_cex_gen m v : v <> baseMode m -> exists p p', currOKState m p /\ listeningState p' /\ p -PA- chanMNext ;? [v] -PA> p'`
    - `currOK_listening_track_cex_modes m m' : m' <> m -> …`. This is the protocol-realistic instance: the next mode differs from the notified mode.
    - `currOK_listening_track_cex m : ~ (statement)`, using `v := baseTime zeroTime`, so a single Mode suffices.
- **Ripple-up:**
  - Not in the safety cone itself.
  - Its only users are in the **commented-out** old proof of `NARInsuff.notifAbort_not_nextSince` (NARInsuff.v:249, 255, 272; that theorem is an `R` target **in the safety cone**). There it eliminated LEP sub-cases by `inversion` on `a = chanMStable *?`. Whoever re-proves `notifAbort_not_nextSince` must not rely on the false statement.
  - In that context the bad case is harmless. `napCuok` gives `currOKStateProt m' p` with `nextModeMState k = Some m'`. A `chanMNext` read synchronised with the mode state reads `m'` itself (`stepMsOutNext`), so `v = baseMode m'`, which the corrected lemma excludes.
  - A synchronisation of the listener's `chanMNext` input with an **overlap** output on `chanMNext` (`tfsNext` outputs `chanMNext<eFailSafeSucc m>`) is a separate case the user must discharge with state reasoning. The original lemma papered over it.
- **Suggested fix:** weaken the conclusion to the honest disjunction:
  ```coq
  Lemma currOK_listening_track m p p' a : currOKState m p ->
    listeningState p' -> p -PA- a -PA> p' ->
    a = (chanMStable *?) \/ exists v, a = chanMNext ;? [v] /\ v <> baseMode m.
  ```
  This is **proved** as `currOK_listening_track_fixed` (Qed, no admitted dependencies). The proof inverts the matching step of `currOK m`. In the `v = baseMode m` case it shows `nextEq m m` can output `chanAbort` while `listening` cannot, which contradicts bisimilarity via `bisim_dae`. The fixed proof can be spliced in verbatim once the statement change is approved; it needs only the helper `currOK_listening_track_listening_no_abort`.
- **Partial proof:** see above. Everything in the HELPERS is demonstration-only until the statement is changed.

## `rangeBad_next`

- **Where:** `src/ProtAuxResults.v` line 522 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `untyped-input`
- **Fix (audit summary):** Recommended tracking form: p -PA- chanMCurr ;? [baseMode m] -PA> p' -> rangeBadState m'' p -> currEqState m m'' p' (proved, model axioms only); minimal alternative adds (exists m0, m0 <> m'') (proved).

- **Status:** NEEDS-HYPOTHESIS. Independent of the model axioms: it is equivalent to "every mode has a distinct other mode", which fails in the one-mode model. Proved in Rocq in both directions, see below.
- **Intent:** forward tracking for the listener. From `rangeBad m''`, the only discrete step is reading the current mode `m` on `chanMCurr`, after which the listener is in `currEq m m''`. That state is the conditional `m = m'' ? badOvlp : currOK m''`.
- **Failure:**
  - `rangeBad m'' = chanMCurr<vM>? currEqN(vM, m'')` accepts **any** base value `v` (`stepDpIn` only checks list length), not just modes. For a non-mode `v`, e.g. `baseTime 0`, `bEqual` still evaluates to `Some false` (it compares any base values with `eqDecBase`). So the derivative is `currEqN(v, m'') ~ currOKN(m'')`.
  - That process is `~ currEq m m''` exactly when `m <> m''`. `currEq m'' m'' ~ badOvlp` can output `chanBad`, and `currOK` cannot.
  - So the conclusion `exists m, currEqState m m'' p'` needs a mode other than `m''`. Nothing in `ComhBasics.v` provides one. All model axioms hold with `Mode := unit`: `failSafe := True`, `failSafeSucc := id`, `modeTransRel := fun _ _ => True`, all times and distances 0 or 1, and `period`/`msgLatency`/`adaptNotif`/`speedMax := 1`. In that model the lemma is false.

  Machine-checked in `ProtAuxResults.rangeBad_next.v` (HELPERS, `--explore`, assumptions: model axioms + trusted stdlib only):
  - `rangeBad_next_needs_two_modes : (<target statement>) -> forall m'' : Mode, exists m, m <> m''`.
- **Ripple-up:** used in `NARInsuff.notifAbort_not_nextSince` (line ~212, the rangeBad case). The proof there continues with `currEq_cond_false` and `EntAuxResults.currEq_mode` to tie the existential `m` to the mode state's current mode. The existential form loses exactly that information, so the user needs the *tracking* form below anyway. In the safety cone (per `show`). Related: `NetAuxBasics.rangeBad_next_net` (NetAuxBasics-2 write-up) proposes a prot-level `rangeBad_track`; `rangeBad_next_track` below is that lemma, proved.
- **Suggested fix (recommended, proved):** state the tracking form, which pins `m` to the value read.
  ```coq
  Theorem rangeBad_next (p p' : ProcTerm) (m m'' : Mode) :
    p -PA- chanMCurr ;? [baseMode m] -PA> p' -> rangeBadState m'' p ->
    currEqState m m'' p'.
  ```
  It is proved as `rangeBad_next_track`. In a reachable entity the only `chanMCurr` value the listener can read is `baseMode (currModeMState k)` (`stepDeCurrRead`; see the NetAuxBasics-2 note on excluding internal mCurr syncs). So the caller gets `currEqState (currModeMState k) m'' p'` directly, which is what `notifAbort_not_nextSince` then needs for `currEq_cond_false`.
  Supporting lemma, also proved: `rangeBad_next_inv : rangeBad m'' -PA- a -PA> q -> exists b, a = chanMCurr ;? [b] /\ q ~p~ currEq (eBase b) m''`. It shows that every step is an mCurr read.
  **Minimal-diff alternative (proved):** keep the conclusion and add `(exists m0, m0 <> m'') ->` as a hypothesis (`rangeBad_next_two_modes`). The alternative of adding a model axiom "at least two modes" changes the trust base and needs owner approval. Either way the existential still doesn't link `m` to the read value, so the tracking form is preferable.
- **Partial proof:** everything is in the HELPERS of `ProtAuxResults.rangeBad_next.v`:
  - `rangeBad_next_app_bisim`: `n $(l)$ ~ body[l]`.
  - `rangeBad_next_inv`, `rangeBad_next_track` and `rangeBad_next_isMode`.
  - `rangeBad_next_currOK`, `rangeBad_next_nonmode` and `rangeBad_next_two_modes`.
  - `rangeBad_next_needs_two_modes`.
  The target's own PROOF stays `Admitted`.
- **Note for siblings (unchecked):** other "input then conditional" fwd-tracking lemmas with an existential over a typed parameter and **no** fallback disjunct (e.g. `gotMessage_next`) may have the same ill-typed-input issue. I have not checked them. `currOK_next` escaped it only because its `\/ listeningState p'` disjunct absorbs non-mode reads.

## `gotMessage_next`

- **Where:** `src/ProtAuxResults.v` line 526 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `eSubtract-vs-bPossInc-typing` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Definition fix: let bPossInc accept a nonneg third argument (evalBaseNonnegFun), then restate for a chanPos ;? [basePosition l'] read with the canonical range. Needs owner approval.

- **Status:** FALSE (counterexample, checked in Rocq, no admitted lemmas used). The root cause is BLOCKED-ON-DEFINITION, a type mismatch in the expression language. **This is a modelling bug that affects reachable behaviour, not just this lemma.**
- **Intent:** a listener in `gotMsg m'' l` (it has received a message `[m'', l]`) reads its own position on `chanPos` and moves to `gotRange m'' r`, where `r = |l' - l| - speedMax*msgLatency`.
- **Failure:**
  - **The type bug.** `gotMsg m'' l' := chanPos<vL>? gotRangeN([m'', (|vL, l'|) (-) speedMax (.) msgLatency])` passes the range as an `eSubtract` expression. Both `evalExpFun` and `evalExp` (`evalSub`) evaluate `eSubtract` to a `baseNonneg _`, never to a `baseDistance _`. But `evalBoolExpFun (bPossInc e1 e2 e3)` (and `evalBoolExp`'s `bevalPossInc`) only fires when `e3` evaluates to `Some (baseDistance d)`. So in `currPincCheck m m'' r := !~bPossInc m m'' r $> currCompN.. $+$ bPossInc m m'' r $> badOvlpN` **both guards evaluate to `None` and hence `false` (`evalBoolExpFunTot`)**. The process is stuck (it can only idle via `stepTpIfFalse`). By contrast, `gotRange m'' r` with a genuine `r : Distance` (coerced to `eBase (baseDistance r)`) always has exactly one guard true after reading a mode on `chanMCurr`: `chanBad!` via `badOvlp` if `possIncBool` holds, `chanMStable?` via `currComp` otherwise.
  - **Counterexample, honest input.** Take `p := gotMsg m l` (so `gotMsgState m l p` by `bisim_refl`), `a := chanPos ;? [basePosition l]`, and `p'` its `stepDpIn` derivative. Suppose `p' ~p~ gotRange m r`. `gotRange m r` inputs `chanMCurr;?[m]` to `currPincCheckN [m, m, r]`, which can act. The matching derivative of `p'` is `currPincCheckN [m, m, (|l,l|) (-) speedMax (.) msgLatency]`, which has no discrete transition (lemmas `gotMessage_next_cx_none` and `_none2`: `evalBoolExpFun (bPossInc x y (eSubtract e1 e2)) = None` for **all** `x y e1 e2`). That is a contradiction.
  - The HELPERS of `ProtAuxResults.gotMessage_next.v` contain `gotMessage_next_cx (m) (l) : exists p p' a, p -PA- a -PA> p' /\ gotMsgState m l p /\ ~ exists r, gotRangeState m r p'` and `gotMessage_next_false : (statement) -> forall m l, False`. They compile under `--explore`. `Print Assumptions` shows only model axioms plus `proof_irrelevance`, `functional_extensionality_dep` and `ClassicalDedekindReals`.
  - **Second independent problem (as w1b-06 also noted):** at process level `a` can be `chanPos ;? [v]` for any single value `v`, e.g. `baseMode _`. Then `eDist` fails to evaluate, giving the same stuck derivative. So even after fixing the type bug, the statement needs the action restricted to a position input.
- **Consequence beyond this lemma (for the owner):** in the current model every listener that processes an incoming message (`listening -> gotMsg -> gotRange -> currPincCheck`) gets **permanently stuck** at `currPincCheck`. It never reaches `badOvlp` (so it never signals `chanBad` to start a fail-safe transition), and it never returns to `listening`. The admitted lemmas that describe the message-handling path (`gotMessage_next`, `gotMsg_gotRange_track_ent`, `msgAbortPath`/`msgBadPath` tracking, `incomp_tfs`, ...) therefore don't describe the actual semantics. Arguments in the safety chain that rely on incompatible messages triggering `tfs` rest on false lemmas until this is fixed. `nextPincCheck` has the same `bPossInc` issue with the same `r`.
- **Ripple-up:** `in_safety_cone=False` per `show`. Used in `NARIncomp.v:131` (inside the `msgAbortPathNet` preservation proof, case `gotMsg`), together with `gotMsg_gotRange_track_ent`, which is also false (see `w1b-06`).
- **Suggested fix (definition, needs owner approval):** let `bPossInc` accept any nonneg-valued third argument, as timers already do through `evalExpFunTime`/`evalBaseNonnegFun`. In `LanguageFoundations.v`:
  ```coq
  | bPossInc e1 e2 e3 =>
    match (evalExpFun e1), (evalExpFun e2), (evalExpFun e3) with
    | Some (baseMode m1), Some (baseMode m2), Some b3 =>
      option_map (fun d => possIncBool m1 m2 (mkDistance d)) (evalBaseNonnegFun b3)
    | _, _, _ => None
    end
  ```
  The relation needs the matching change: `bevalPossInc : evalExp e1 m1 -> evalExp e2 m2 -> evalExp e3 b -> b \_/ d -> evalBoolExp (bPossInc e1 e2 e3) (possIncBool m1 m2 (mkDistance d))`. Then restate the lemma for a position read with the canonical range:
  ```coq
  Theorem gotMessage_next (p p' : ProcTerm) (m'' : Mode) (l l' : Position) :
    p -PA- chanPos ;? [basePosition l'] -PA> p' -> gotMsgState m'' l p ->
    gotRangeState m'' (mkDistance (dist2d l' l -nn- speedMax *nn* msgLatency)) p'.
  ```
  The existential form `exists r, gotRangeState m'' r p'` is also fine under that action restriction. Why provable: by `bisim_disc_match`, `gotMsg` is the only source, and its derivative is `gotRangeN [m'', E]` with `E` evaluating to the same nonneg as the literal. A cofix bisimulation "up to expression evaluation" over the finite derivative set `gotRange -> currPincCheck -> {currComp -> nextPincCheck -> {listening, abortOvlp}, badOvlp}` closes it. The user in `NARIncomp` gets `a = chanPos;?[basePosition l]` from the entity step (`stepDePosRead`, with reachability excluding other `chanPos` writers).
- **Partial proof:** none for the target. The verified counterexample is in the `.v` file.

## `gotRange_next`

- **Where:** `src/ProtAuxResults.v` line 531 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Expose the action: exists b, a = chanMCurr ;? [b] /\ (forall m, b = baseMode m -> currPincCheckState m m'' r p') (writer proved it with copied helpers).

- **Status:** FALSE (counterexample, machine-checked). **The statement implies `Mode -> False`**, so it is inconsistent with the model axioms whenever `Mode` is inhabited. Add it to the known-inconsistent list.
- **Intent:** a listener in `gotRange m'' r` reads the current mode `m` on `chanMCurr` and moves to `currPincCheck m m'' r`.
- **Failure:** `gotRange m'' r = chanMCurr<vM>? currPincCheckN [vM, m'', r]`. `stepDpIn` accepts **any** base value of the right arity, so `gotRange m'' r -PA- chanMCurr ;? [baseTime zeroTime] -PA> currPincCheckN $([zeroTime, m'', r])$`. In that derivative both guards, `!~bPossInc zeroTime m'' r` and `bPossInc zeroTime m'' r`, fail to evaluate because the first argument is not a mode. `evalBoolExpFunTot` maps both to `false`, so the derivative has **no discrete step**. For every genuine `m : Mode`, `currPincCheck m m'' r` does have a discrete step: `chanBad *!` via `badOvlp` if `possIncBool m m'' r = true`, else `chanMStable *?` via `currComp`. So no `m` makes the two bisimilar.
  Checked in Rocq (`--explore`, rc=0, HELPERS of `ProtAuxResults.gotRange_next.v`). It uses no admitted lemma, and `Print Assumptions` shows only model axioms, proof irrelevance, functional extensionality and the stdlib reals axioms:
  - `gotRange_next_inert` (the ill-typed derivative is stuck)
  - `gotRange_next_step` (`currPincCheck m m'' r` always steps)
  - `gotRange_next_refuted : (target statement) -> Mode -> False`
  This is the same defect w1b-06 found for `currComp_next`. Their note already predicted it for `gotRange_next` and `gotMessage_next`.
- **Ripple-up:** not in the safety cone. One user: `NARIncomp.v:155` (`msgAbort_not_nextSince`, case 2 "gotRange"). That `Qed` proof therefore rests on an inconsistent assumption, though there the step comes from an entity transition. The listener's `chanMCurr` input can only synchronise with the mode state (`stepDeCurrRead`, value `baseMode m`). Process-internal `chanMCurr` outputs (`switchCurr`, `tfsCurr`) carry `[]`, so the arity check blocks them. Nothing true is lost by restricting the lemma.
- **Suggested fix:** expose the action, and conclude only for well-typed values:
  ```coq
  Theorem gotRange_next (p p' : ProcTerm)
    (a : DiscAct) (m'' : Mode) (r : Distance) :
    p -PA- a -PA> p' -> gotRangeState m'' r p ->
    exists b, a = chanMCurr ;? [b] /\
    (forall m, b = baseMode m -> currPincCheckState m m'' r p').
  ```
  **This corrected statement is proved** (`gotRange_next_fixed` in the same HELPERS, compiled at the target's position). It reuses the forward-tracking helpers of ProtAuxResults-1's accepted `currOK_next`, copied under the prefix `gotRange_next_cp_`. At `NARIncomp.v:155` the user then gets `a = chanMCurr ;? [b]`. Inverting the entity step (`stepDeCurrRead`) gives `b = baseMode m` with `m = currModeMState k`, which is exactly what `gotRange_currPincCheck_track_ent` is later used for. An alternative with the same strength adds the hypothesis `forall b, a = chanMCurr ;? [b] -> exists m, b = baseMode m` and keeps the old conclusion.
- **Partial proof:** the proof of the fixed statement (`gotRange_next_fixed`) is in the `.v`. If the owner approves the restated lemma, it can be spliced with its helpers. Its body:
  ```coq
  intros TR CS. unfold gotRangeState in CS. unfold gotRange in CS.
  gotRange_next_cp_fwd_pre.
  all: eexists; split; [reflexivity | ]; intros m0 Eb; subst;
    unfold currPincCheckState; eapply bisim_trans; [eassumption | ];
    gotRange_next_cp_unfold_app; apply bisim_refl.
  ```

## `currComp_next`

- **Where:** `src/ProtAuxResults.v` line 536 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis (forall v, a = chanMNext ;? v -> exists m, v = [baseMode m]) or expose the action in the conclusion; caller discharges it from stepDeNextRead.

- **Status:** FALSE (counterexample, Rocq-checked). The statement implies `False` given any `m'' : Mode` and
  `r : Distance`, so this admitted lemma is **inconsistent with the model axioms** whenever `Mode` is inhabited.
  Add it to the known-inconsistent list.
- **Intent:** a listener in `currComp m'' r` steps either to `listening` (on `chanMStable?`) or to
  `nextPincCheck m m'' r` (on `chanMNext?[m]`).
- **Failure:** `currComp m'' r = chanMStable? listeningN $+$ chanMNext<vM'>? nextPincCheckN [vM', m'', r]`, and
  `stepDpIn` accepts **any** base value of the right arity, e.g. `chanMNext ;? [baseTime zeroTime]`. The derivative
  `nextPincCheckN [zeroTime, m'', r]` is **stuck**. Both guards `!~bPossInc ..` and `bPossInc ..` fail to evaluate
  (first argument not a mode), so `evalBoolExpFunTot` gives `false` for both. Every `nextPincCheck m m'' r` with
  `m : Mode` has a discrete action (`chanAbort *!` if `possIncBool m m'' r = true`, else `listening`'s `chanPause ;? []`),
  and so does `listening`. So neither disjunct holds. Checked in Rocq (`--explore`, rc=0; full script in the `.v`):
  ```
  Lemma currComp_next_cex (m'' : Mode) (r : Distance) :
    (forall p p' a, p -PA- a -PA> p' -> currCompState m'' r p ->
       (exists m, nextPincCheckState m m'' r p') \/ listeningState p') -> False.
  ```
  Helpers: `currComp_next_stuck` (derivative has no discrete step), `currComp_next_bisim_act`,
  `currComp_next_listening_act`.
- **Ripple-up:** not in the safety cone. One user: `NARIncomp.v:177` (`msgAbort_not_nextSince`). There the step
  comes from an entity transition where the mode state outputs `chanMNext .! m` (`stepDeNextRead`), so the input is
  always `[baseMode m]`. Nothing true is lost by restricting the lemma.
- **Same defect elsewhere (not my targets, likely the same verdict):** `gotRange_next` (input `chanMCurr ;? [b]`
  with `b` not a mode makes `currPincCheckN` stuck) and `gotMessage_next` (input `chanPos ;? [b]` with `b` not a
  position gives an ill-typed distance, so `currPincCheck` gets stuck one step later). Every `*_next` forward-tracking lemma
  whose continuation guards on a `bPossInc`/`bSufficient` of the input value should be checked for this.
- **Suggested fix:** restrict the input to well-typed values. Either add a hypothesis
  ```
  Theorem currComp_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (r : Distance) :
    p -PA- a -PA> p' -> currCompState m'' r p ->
    (forall v, a = chanMNext ;? v -> exists m, v = [baseMode m]) ->
    (exists m, nextPincCheckState m m'' r p') \/ listeningState p'.
  ```
  or make the conclusion carry the action:
  `(exists m, a = chanMNext ;? [baseMode m] /\ nextPincCheckState m m'' r p') \/ (a = chanMStable *? /\ listeningState p') \/ (exists b, a = chanMNext ;? [b] /\ forall m, b <> baseMode m)`.
  Both are provable by the forward-tracking idiom used for `currOK_next` (bisim to `currComp`, invert its steps,
  unfold `nextPincCheckN`/`listeningN` with an app-unfolding bisim lemma). At `NARIncomp.v:177`, the extra hypothesis is
  discharged from the entity step (`stepDeNextRead` gives `chanMNext ;? [baseMode m]`).

## `tfsStart_next`

- **Where:** `src/ProtAuxResults.v` line 550 · **Lemma** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Restrict to a mode read: p -PA- chanMCurr ;? [baseMode m] -PA> p' -> tfsStartState p -> tfsNextState m p' (proved, model axioms only).

- **Status:** FALSE (counterexample, machine-checked). **The lemma is inconsistent with the model axioms alone: it proves `False` without any hypothesis, not even an inhabited `Mode`.**
- **Intent:** From `tfsStart = chanMCurr$<vM>$? tfsNextN $(eVar vM)$`, any discrete step leads to `tfsNext m` for the mode `m` that was read.
- **Failure:** `stepDpIn` lets a process input **any** `BaseType` list of the right length, not only modes. Take `tfsStart -PA- chanMCurr ;? [baseTime zeroTime] -PA> p'`, where `p' = tfsNextN $([eBase (baseTime 0)])$`. Its body is `chanMNext$<eFailSafeSucc (baseTime 0)>$! … $+$ chanMStable! …`.

  For every `m : Mode`, `tfsNext m` can do `chanMNext ;! [baseMode (failSafeSucc m)]` (`tfsNext_mNext_out`). `p'` cannot, because `evalExp (eFailSafeSucc (eBase (baseTime 0))) _` has no derivation. So `~ p' ~p~ tfsNext m`.

  Verified as `tfsStart_next_cex : ~ (statement)` in `w1b-15/ProtAuxResults.tfsStart_next.v` (`Qed`). `Print Assumptions` lists only model-axiom declarations and stdlib classical/FE/PI.
- **Ripple-up (important):**
  - `EntAuxResults.tfsStart_next_ent` (**in safety cone**) is also **FALSE** for unreachable entities. Counterexample, verified in `w1b-15/EntAuxResults.tfsStart_next_ent.cex.v`, lemma `tfsStart_next_ent_cex (k : ModeState) : ~ (statement)`, `Qed`, model axioms only:
    - The entity is `[| chanMCurr$<[baseTime 0]>$! nilProc $||$ tfsStart $||$ nilProc, origin, emptyIface, k |]`.
    - The broadcaster slot syncs a *time* into the overlap component (`stepDpSyncLR`, `stepDeProcTau`).
    - The result is neither `tfsStartStateEnt` nor `tfsNextStateEnt m` for any `m`.
  - **steal-2 has `EntAuxResults.tfsStart_next_ent.ok`, and its proof calls `tfsStart_next`. That proof must be rejected.** `ProtAuxResults.tfsStart_next` and `EntAuxResults.tfsStart_next_ent` should both go into `blacklist_hard.txt`.
  - Further up: `NetAuxBasics.tfsStart_next_net` (Qed, by `fwd_track_net_tac tfsStart_next_ent`) and `NetAuxBasics.tfs_currMode_disc_pres` (uses `tfsStart_next_net`; no reachability hypothesis). Both inherit the problem. The same entity, placed in a network with `currMode_intro`, falsifies them (not separately machine-checked).
- **Suggested fix:**
  - Prot level, restricting to reading a mode:
    ```coq
    Lemma tfsStart_next (p p' : ProcTerm) (m : Mode) :
      p -PA- chanMCurr ;? [baseMode m] -PA> p' -> tfsStartState p -> tfsNextState m p'.
    ```
    **Proved** (as `tfsStart_next_fixed`, `Qed`, no admitted dependencies; model axioms and stdlib only) in `w1b-15/ProtAuxResults.tfsStart_next.v`, together with the helper `tfsStart_next_app_bisim` (`n $( l )$ ~p~ body[l/xs]`).
    - Alternative that keeps the original shape: `(exists m, a = chanMCurr ;? [baseMode m] /\ tfsNextState m p') \/ (exists b, a = chanMCurr ;? [b] /\ forall m, b <> baseMode m)`.
  - Entity level: add `reachableEnt e ->` (stub) to `tfsStart_next_ent`, and `reachableNet n ->` to `tfsStart_next_net` and `tfs_currMode_disc_pres`. Under reachability, the broadcaster and listener never output on `chanMCurr` (`bc_mCurr_out_not`, `listen_mCurr_out_not`). The only way to the overlap's `chanMCurr` input is then `stepDeCurrRead` with the mode state's `chanMCurr .! m`, which carries a mode, and the fixed prot lemma applies. This is BLOCKED-ON-STUB (`reachableEnt`) until the stub is defined.
- **Partial proof:** `tfsStart_next_cex`, `tfsStart_next_app_bisim` and `tfsStart_next_fixed` are in `w1b-15/ProtAuxResults.tfsStart_next.v`.

## `paused_switch`

- **Where:** `src/ProtAuxResults.v` line 834 · **Theorem** · 2015 label: `5` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:reachableProt-allows-unsynchronised-internal-actions` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Definition change: restrict reachableProt steps to entity-visible actions (internal channels only via tau), or delete and prove paused_switch_net directly by induction on reachableNet.

- **Status:** FALSE (counterexample, verified in Rocq; uses no admitted lemmas)
- **Intent:** in a reachable protocol process `p1 | p2 | p3`, the listener `p3` is `paused` exactly when the overlap `p2` is in a switch state (`switchBc m`, `switchCurr` or `switchListen`). Pausing and unpausing happen only through the synchronisations `ovWait --chanPause!--> switchBc` ∥ `listening --chanPause?--> paused` and `switchListen --chanUnpause!--> dormant` ∥ `paused --chanUnpause?--> listening`.
- **Failure:** `reachableProt` (ProtAuxDefs.v:240) is closed under **every** process step `p -PA- a -PA> p'`, including unsynchronised half-actions on the protocol's internal channels. The parallel rules `stepDpParL`/`stepDpParR` let a single component input or output on its own. So the listener can take `chanPause?` alone, without any synchronisation:
  `procProtocol = sleeping | dormant | listening  --chanPause *?-->  sleeping | dormant | pausedN`.
  This target is reachable, and `pausedN ~p~ paused`, so `pausedStateProt` holds. But `dormant` enables `chanAbort *?`, which no switch state (`switchBc`, `switchCurr`, `switchListen`) can match, so `~ switchStateProt`. The script compiles at the target's position with `--explore`. It is adapted from ProtAuxResults-3's draft, with the `S` Ltac-binding bug fixed. The helper tactics `paused_switch_inv`/`paused_switch_noact` (a copy of `link_reach_triple_tau_noact`) are in `w1b-09/ProtAuxResults.paused_switch.v`.
  ```coq
  Lemma paused_switch_reach : reachableProt (sleeping $||$ dormant $||$ pausedN).
  Proof.
    eapply reachprDisc; [apply reachprBase | ].
    unfold procProtocol. apply stepDpParR. apply stepDpParR.
    unfold listening. apply stepDpChoiceL. apply stepDpChoiceR.
    instantiate (1 := chanPause *?). apply stepDpIn. reflexivity.
  Qed.
  (* + paused_switch_pausedN : pausedN ~p~ paused   (unfold app via def)
     + ~ switchStateProt (... dormant ...)   (dormant enables chanAbort*?, no switch state does) *)
  Lemma paused_switch_refuted :
    ~ (forall p, reachableProt p -> (pausedStateProt p <-> switchStateProt p)).
  ```
  The converse direction fails in the same way: an unsynchronised `chanPause!` by `ovWait` reaches `switchBc` while the listener is still `listening`.
- **Ripple-up:**
  - In-file: used by `EntAuxResults.switchListen_urgent` (EntAuxResults.v:364).
  - **Safety cone (important):** `NetAuxBasics.paused_switch_net` (in the safety cone) was accepted in wave 1 (`NetAuxBasics-2/NetAuxBasics.paused_switch_net.v`) with a proof that is just `link_net_prot_reach` + `paused_switch`. If that proof is spliced, the safety cone rests on this **false** lemma. `paused_switch_net` is used by NARIncomp.v:394 and NARInsuff.v:68, 463-464.
  - `paused_switch_net` itself is plausibly **true**. At entity level, internal-channel half-actions cannot fire: `stepDiscEnt` lifts only `tau` and the entity-interface channels. The information is lost in the projection `reachableNet → reachableProt`.
- **Suggested fix (definition change, needs owner approval):** restrict `reachableProt` to process steps that the entity semantics can actually lift. Internal channels (`chanPause`, `chanUnpause`, `chanAbort`, `chanBad`, `chanWake`, `chanTrans`) must synchronise.
  ```coq
  Inductive entVisibleAct : DiscAct -> Prop :=
    | evTau : entVisibleAct tauAct
    | evOutProc v : entVisibleAct (chanOutProc ;! v)
    | evInProc v : entVisibleAct (chanInProc ;? v)
    | evAN v : entVisibleAct (chanAN ;? v)
    | evStableIn : entVisibleAct (chanMStable *?)
    | evStableOut : entVisibleAct (chanMStable *!)   (* if WRITE-STBL is added, see below *)
    | evCurrOut : entVisibleAct (chanMCurr *!)
    | evCurrIn v : entVisibleAct (chanMCurr ;? v)
    | evNextOut v : entVisibleAct (chanMNext ;! v)
    | evNextIn v : entVisibleAct (chanMNext ;? v)
    | evPosIn v : entVisibleAct (chanPos ;? v).
  Inductive reachableProt : ProcTerm -> Prop :=
    | reachprBase : reachableProt procProtocol
    | reachprDisc (p p' : ProcTerm) (a : DiscAct) : reachableProt p ->
      entVisibleAct a -> p -PA- a -PA> p' -> reachableProt p'
    | reachprDel (p p' : ProcTerm) (d : Delay) : reachableProt p ->
      p -PD- d -PD> p' -> reachableProt p'.
  ```
  `link_net_prot_reach` / `reachable_ent_prot` stay provable, since every `stepDiscEnt` rule moves the process with one of these actions or leaves it fixed. With this definition `paused_switch` is a routine induction on `reachableProt`. The invariant is the biconditional itself. `chanPause`/`chanUnpause` now only occur inside `tau` synchronisations between overlap and listener, and the `tfsListen --chanUnpause!--> dormant` ∥ `listening --chanUnpause?--> listening` sync keeps both sides non-switch/non-paused.
  - Alternative that leaves `reachableProt` alone: delete `paused_switch` and prove `paused_switch_net` directly by induction on `reachableNet`, through an entity-level `paused_switch_ent` under `reachableEnt`.
- **Side note:** the entity semantics also lacks the thesis WRITE-STBL rule; see `w1b-09/EntAuxResults.ovAbort_unstable.fail.md`. Separately, `reachableProt_triple` (ProtAuxResults.v:843) concludes `protocolState`, whose `overlapState` only covers `dormant`/`ovWait` ("INCOMPLETE" comment, ProtAuxDefs.v:126), so it is false for reachable `init`/`ovReady`/… states, with or without this fix.
- **Partial proof:** none for the target (it is false). The counterexample is in `w1b-09/ProtAuxResults.paused_switch.v` (HELPERS).

## `gotMsg_state`

- **Where:** `src/ProtAuxResults.v` line 922 · **Lemma** · 2015 label: `6` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:missing-protocolState-hypothesis (p unconstrained)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add protocolState p (or reachableProt p); writer proved this fixed form in explore mode (not re-checked here); user incomp_incomingNet_bad then needs reachableNet n.

- **Status:** FALSE (counterexample) / NEEDS-HYPOTHESIS (`protocolState p`)
- **Intent:** if a *protocol* process `p` inputs `[m, l]` on `chanInProc`, then its
  listener component ends up in `gotMsgState m l`, i.e. `gotMsgStateProt m l p'`.
  The source comment already says: "NEEDS TO BE EDITED! PROTOCOL PROCESS HYPOTHESIS
  DOESN'T LOOK LIKE IT'S THERE."
- **Failure:** `p` is unconstrained. Take
  `p := chanInProc $<[vM'', vL']>$? nilProc`. By `stepDpIn`,
  `p -PA- chanInProc;? [baseMode m, basePosition l] -PA> nilProc`, because
  `subProcTerm _ nilProc = nilProc`. But `gotMsgStateProt m l nilProc` needs
  `nilProc = p1 $||$ p2 $||$ p3`, so it fails. This was checked in Rocq (`--explore`, compiles with `Qed`):
  ```coq
  Lemma gotMsg_state_cex m l : ~ (forall p p',
    p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p').
  Proof.
    intro H.
    assert (TR : (chanInProc $<[vM'', vL']>$? nilProc) -PA-
      chanInProc;? [baseMode m, basePosition l] -PA> nilProc).
    { change nilProc with (subProcTerm (listsToSub [vM'', vL']
        (listBaselistExp [baseMode m, basePosition l])) nilProc) at 2.
      constructor. reflexivity. }
    specialize (H _ _ TR). inversion H.
  Qed.
  ```
  So the statement is false for every `m`, `l`. It can't be refuted outright in Rocq only
  because `Mode` is an abstract `Axiom` type that might be empty.
- **Ripple-up:** used only in `NARIncomp.incomp_incomingNet_bad` (line 77, which ends in `Qed`).
  That lemma is used by `NARIncomp.instant_incomp_tfs` (line 407). `show` reports
  `in_safety_cone=False` for `gotMsg_state`. At the use site, `Q0` is the software transition
  of entity `i` in network `n`. `incomp_incomingNet_bad` has no reachability hypothesis,
  so the corrected lemma can't be applied there without one more premise.
- **Suggested fix:**
  ```coq
  Lemma gotMsg_state p p' m l : protocolState p ->
    p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p'.
  ```
  (`reachableProt p ->` would also do, via `reachableProt_triple`.) **This corrected version is
  proved** (`--explore`, `Qed`). It uses the HELPERS of my accepted proofs of
  `prot_outProc_in_not` and `ovlp_abort_in`. Those are the Ltacs `prot_outProc_in_not_*` and the lemmas
  `ovlp_abort_in_bisim_step` and `ovlp_abort_in_appbisim`:
  ```coq
  Proof.
    intros PS TR. inversion PS as [p1 p2 p3 BS OS LS]; subst; clear PS.
    inversion TR; subst; clear TR.
    - inversion BS; prot_outProc_in_not_contra.
    - match goal with [V : p2 $||$ p3 -PA- _ -PA> _ |- _] =>
        inversion V; subst; clear V end.
      + inversion OS; prot_outProc_in_not_contra.
      + unfold gotMsgStateProt. constructor.
        inversion LS as [B|m0 B|m0 B|B|B|m0 r B]; prot_outProc_in_not_unfold;
          try prot_outProc_in_not_contra.
        match goal with [V : p3 -PA- _ -PA> _ |- _] =>
          destruct (ovlp_abort_in_bisim_step _ _ _ _ B V) as [q'' [TQ BQ]] end.
        unfold listening in TQ. prot_outProc_in_not_inv.
        eapply bisim_trans; [exact BQ | ].
        eapply bisim_trans; [apply ovlp_abort_in_appbisim | ].
        simpl. remove_resets. remove_updates. apply bisim_refl.
  Qed.
  ```
  The user needs a matching change. Add `reachableNet n ->` to
  `incomp_incomingNet_bad`. In its proof, get `protocolState p` from
  `reachableProt_triple (link_net_prot_reach rn H)`, where `H` is the entity-in-network
  hypothesis, and pass it to `gotMsg_state`. The only caller is `instant_incomp_tfs`, inside the
  `receivedDisc` case of `dependent induction`. There the pre-state reachability proof
  `p : reachableNet n` is in scope, so it can pass it.
- **Partial proof:** see `ProtAuxResults.gotMsg_state.v` in this directory. Its HELPERS
  contain both the counterexample and the corrected lemma. The target itself is left `Admitted`.
