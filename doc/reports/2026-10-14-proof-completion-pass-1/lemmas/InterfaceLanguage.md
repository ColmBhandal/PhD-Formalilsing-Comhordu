# Unproved lemmas in `InterfaceLanguage`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

3 lemmas here could not be proved as stated, none of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `inList_received_in`

- **Where:** `src/InterfaceLanguage.v` line 361 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `typo (copy-paste from outList_received_in: stepIlBuff stamps zeroTime, not msgLatency)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude <(v, zeroTime)> _: inList l' (proved, model axioms only), or delete the conjecture (no users).

- **Status:** FALSE (counterexample)
- **Intent:** after an input list buffers `v` (rule `stepIlBuff`), `v` is in the list with its initial timestamp.
- **Failure:** `stepIlBuff` stamps the new element with `zeroTime`, not `msgLatency`
  (the statement was copy-pasted from `outList_received_in`, where `stepOlBuff` does use `msgLatency`).
  The lift case is vacuous (timed lists have no input rule), so `l' = mkInputList (<(v, zeroTime)> :: inList l)`.
  Counterexample: `l := mkInputList []`, `v := []`, `l' := mkInputList [<([], zeroTime)>]` via `stepIlBuff [] []`.
  The conclusion needs `<([], zeroTime)> = <([], msgLatency)>`, i.e. `0 = msgLatency`, which contradicts `msgLatency_positive`.
  Rocq check (compiles, `--explore`): `inList_received_in_false : ~ (forall l l' v, l -il- v ?? -il> l' -> <(v, msgLatency)> _: inList l')`
  in `InterfaceLanguage.inList_received_in.counterexample.v`.
- **Ripple-up:** no users anywhere in the frozen sources (`grep -n inList_received_in *.v` hits only the declaration). Not in the safety cone. Nothing breaks.
- **Suggested fix:**
  ```coq
  Lemma inList_received_in : forall (l l' : InputList) (v : list BaseType),
    l -il- v ?? -il> l' -> <(v, zeroTime)> _: inList l'.
  Proof.
    intros l l' v H. inversion H; subst.
    - simpl. left. reflexivity.
    - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
  Qed.
  ```
  This proof is checked (as `inList_received_in_fixed`) in the counterexample file. Alternatively, delete the conjecture, since nothing uses it.

## `notifList_received_in`

- **Where:** `src/InterfaceLanguage.v` line 365 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `typo (copy-paste: stepNlBuff stamps adaptNotif, not msgLatency)`
- **Fix (audit summary):** Conclude <(v, adaptNotif)> _: notifList l' (proved), or delete (no users).

- **Status:** FALSE in the intended model (independent of the axioms). NEEDS-HYPOTHESIS `msgLatency = adaptNotif` if kept as stated.
- **Intent:** after a notification list buffers `v` (rule `stepNlBuff`), `v` is in the list with its initial timestamp.
- **Failure:** `stepNlBuff` stamps the new element with `adaptNotif`, not `msgLatency` (copy-paste from `outList_received_in`).
  The other `stepNotifList` rules carry delay actions, and the lift case is vacuous (timed lists have no input rule), so
  `l' = mkNotifList (<(v, adaptNotif)> :: notifList l)`.
  Proved in Rocq (`--explore`, compiles): `notifList_received_in_iff : (statement) <-> msgLatency = adaptNotif`
  in `InterfaceLanguage.notifList_received_in.counterexample.v`. The `->` direction instantiates `l := mkNotifList []`, `v := []`.
  The only axioms constraining `msgLatency` and `adaptNotif` are `msgLatency_positive` and `adaptNotif_positive`
  (checked: `grep` over all `Axiom`/`Parameter`/`Conjecture` declarations). So e.g. `msgLatency = 1`, `adaptNotif = 2`
  is consistent with the model, and the statement is unprovable.
- **Ripple-up:** no users anywhere in the frozen sources. Not in the safety cone. Nothing breaks.
- **Suggested fix:**
  ```coq
  Lemma notifList_received_in : forall (l l' : NotifList) (v : list BaseType),
    l -nl- v ?? -nl> l' -> <(v, adaptNotif)> _: notifList l'.
  Proof.
    intros l l' v H. inversion H; subst.
    - simpl. left. reflexivity.
    - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
  Qed.
  ```
  This proof is checked (as `notifList_received_in_fixed`) in the counterexample file. Alternatively, delete the conjecture, since nothing uses it.

## `inList_pres_input`

- **Where:** `src/InterfaceLanguage.v` line 371 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:missing-non-delay-hypothesis (stepIlDel empties any input list)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis (forall d, a <> atlDel d); fixed lemma and the unchanged user inList_inter_pres_input re-proved (model axioms only).

- **Status:** FALSE (counterexample)
- **Intent:** a timed-out message `<(v, zeroTime)>` in an input list survives any step except the output of `v` itself.
- **Failure:** the rule `stepIlDel : forall l d, l -il- d -il> mkInputList []` lets *any* input list (including one that holds a
  timed-out message) delay and drop everything. The conclusion's left disjunct is then `In _ []` (false), and the right one,
  `atlDel d = v !!`, is a constructor clash.
  Counterexample: `v := []`, `l := mkInputList [<([], zeroTime)>]`, `l' := mkInputList []`, `a := atlDel (mkDelay (mkposreal 1 Rlt_0_1))`.
  Rocq check (compiles, `--explore`): `inList_pres_input_false` in `InterfaceLanguage.inList_pres_input.counterexample.v`.
  The other cases are fine. Buffering conses onto the list. A lifted timed-list delay is impossible when there is a zero
  timestamp (it needs `0 = t' + d` with `d > 0`). A lifted output either removes `<(v,0)>` itself (`a = v!!`) or preserves it.
- **Ripple-up:** used only in the proof of `inList_inter_pres_input` (InterfaceLanguage.v:395/397). That lemma already
  assumes `forall d, a <> aiDel d` and only invokes this lemma on the `?? ` and `!!` input-list steps, so the delay case never
  arises there. `inList_inter_pres_input` is used in NARIncomp.v:64,71. Not in the safety cone.
- **Suggested fix:** add a non-delay hypothesis:
  ```coq
  Lemma inList_pres_input v l l' a :
    (forall d, a <> atlDel d) ->
    <( v, zeroTime )> _: inList l -> l -il- a -il> l' ->
    <( v, zeroTime )> _: inList l' \/ a = v !!.
  ```
  The counterexample file checks a full proof of this (`inList_pres_input_fixed`, with helper `inList_pres_input_tl_out`).
  It also re-proves `inList_inter_pres_input` with its statement unchanged on top of the fixed lemma (`inList_pres_input_user_check`).
  So the only change needed upstream is the proof of `inList_inter_pres_input`: build the non-delay side condition with
  `assert (ND : forall d, act <> atlDel d) by (intros dd EE; discriminate EE)` and pass `ND` first.
- **Partial proof:** see `InterfaceLanguage.inList_pres_input.counterexample.v` (all helpers compile; target left `Admitted`).
