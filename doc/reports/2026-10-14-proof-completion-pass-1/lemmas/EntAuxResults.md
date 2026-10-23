# Unproved lemmas in `EntAuxResults`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

21 lemmas here could not be proved as stated, 4 of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `tfsBc_failSafe`

- **Where:** `src/EntAuxResults.v` line 69 · **Lemma** · 2015 label: `C` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Add hypothesis reachableEnt e (available at NARNonFS_currSince.v:176 via reachable_net_ent); define reachableEnt; and also forbid internal sync on mode-state channels, else the reachable version still fails (see notes).

- **Status:** NEEDS-HYPOTHESIS (unprovable as stated; with the missing hypothesis it becomes BLOCKED-ON-STUB `reachableEnt`)
- **Intent:** in a *reachable* entity whose overlap component is in the `tfsBc` state
  (`chanTrans!tfsListenN`), the mode state's current mode is fail-safe: the preceding
  `tfsCurr` state wrote the fail-safe successor out on `chanMCurr`.
- **Failure:** the statement has no reachability hypothesis, so `e` may be any entity whose
  process is `nilProc $||$ tfsBc $||$ nilProc`, with an arbitrary mode state `sing m`. So the
  lemma implies that *every* mode is fail-safe (given any `Position` and `Interface`).
  Verified in Rocq (compiles in `--explore`; see `EntAuxResults.tfsBc_failSafe.v` HELPERS):
  ```
  Lemma tfsBc_failSafe_cex :
    (forall e, tfsBcStateEnt e -> failSafe (currModeEnt e)) ->
    Position -> Interface -> forall m : Mode, failSafe m.
  Proof.
    intros H l h m.
    apply (H ([| nilProc $||$ tfsBc $||$ nilProc, l, h, sing m |])).
    unfold tfsBcStateEnt, tfsBcStateProt. constructor. constructor.
    unfold tfsBcState. apply ProcEquiv.bisim_refl.
  Qed.
  ```
  The model axioms in `ComhBasics.v` don't force all modes to be fail-safe. For example, `Mode := bool`,
  `failSafe := (fun b => b = true)`, `failSafeSucc := fun _ => true` and `modeTransRel := fun _ _ => True`
  satisfy `fsDecMode`, `failSafeSucc*` and `minDistCompFS`. So the statement is not provable, and in any intended
  model (one with a non-fail-safe mode) it is false. If it were made true, every mode would be fail-safe, `minDistComp`
  would be identically 0, and `safety` would become vacuous.
- **Ripple-up:** in the safety cone. One user: `NARNonFS_currSince.v:176` (`nonFS_currSince`), which
  applies it to `[|p', l', h', k'|]`, the entity `i` in the reachable network `n'` after a step.
  The `(*CHANGE: ... Add reachability of entity as a hypothesis*)` comment above the lemma already
  records this. At the use site, `reachableEnt [|p',l',h',k'|]` is available via
  `reachable_net_ent` (NetAuxBasics.v:745) from `reachableNetDisc ... n'` and `e' @ i .: n'` (H4).
- **Suggested fix:**
  ```
  Lemma tfsBc_failSafe (e : Entity) :
    reachableEnt e -> tfsBcStateEnt e -> failSafe (currModeEnt e).
  ```
  At the use site, insert `eapply reachable_net_ent; [econstructor; eassumption | eassumption]`
  (or equivalent) before `apply TF`.
  The fixed statement is still BLOCKED-ON-STUB while `reachableEnt` is an opaque `Parameter`.
  It becomes provable with `reachableEnt e := exists n i, reachableNet n /\ e @ i .: n`
  (equivalently, an inductive closure of initial entities under `-EA->`/delays). Proof: induct on reachability with the
  invariant "tfsCurr ⇒ nextModeEnt (failSafeSucc _) e" (cf. `tfsCurr_failSafe`) together with
  "tfsBc ⇒ failSafe (currModeEnt e)". The only entry into `tfsBc` is the `chanMCurr!` output from `tfsCurr`,
  which synchronises with the mode state's `stepDeCurrWrite` and sets the current mode to that fail-safe next mode.
  `tfsBc` itself only does `chanTrans!`, which leaves the current mode unchanged.
- **Partial proof:** none beyond the counterexample.

## `bcReady_pos`

- **Where:** `src/EntAuxResults.v` line 102 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define inPosEnt (e.g. inductive with witness [|p,l,h,k|], or posEnt e = l) and reachableEnt; prove posEnt e = l by reachability induction using a new process lemma bcReady_prev and bcReady urgency.

- **Status:** BLOCKED-ON-STUB (`inPosEnt`, EntAuxDefs.v:149; also `reachableEnt`, EntAuxDefs.v:143)
- **Intent:** if a reachable entity's broadcast component is ready to output `(m, l)` (state `bcReady m l`), then the entity is at position `l`. The value `l` was read from `chanPos`, and the state is urgent, so it cannot have moved since.
- **Failure:** the goal is `inPosEnt l e`, and `inPosEnt` is an opaque `Parameter`. No definition, axiom, lemma or conjecture visible at this point (or anywhere else in the project) has `inPosEnt` as a conclusion. It only appears as the conclusion of this lemma and `ovReady_pos`, and as a hypothesis of `NetAuxBasics.inPos_ent_net`. The hypothesis `reachableEnt e` is also an opaque `Parameter`, and nothing visible derives `False` from it or from `bcReadyStateEnt m l e`. Interpreting `inPosEnt := fun _ _ => False` and `reachableEnt := fun _ => True` is consistent with every visible assumption, and makes the statement false for any entity whose process is `bcReady m l` in parallel with anything. So no proof exists while the stubs are opaque.
- **Ripple-up:** in the safety cone. Its only user is `NARMsgPosition.v:244`, in the base case of the "sent message carries the sender's position" result. There it is combined with `inPos_ent_net` and `inPos_unique` to show that the broadcast position equals the sender's position. `ovReady_pos` (EntAuxResults.v:110) is the twin lemma for the overlap component and is blocked the same way.
- **Suggested fix (stub definitions; the statement stays as it is):**
  ```coq
  (* EntAuxDefs.v, replacing the Parameter; analogous to the nextModeEnt idea *)
  Inductive inPosEnt (l : Position) : Entity -> Prop :=
    | ipeWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
      inPosEnt l ([|p, l, h, k|]).
  (* or: Definition inPosEnt l e := posEnt e = l. *)

  (* moved below initialEnt *)
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  These match the definitions proposed in `NetAuxBasics.inPos_ent_net.fail.md` and `NetAuxBasics.reachable_net_ent.fail.md`.
- **Proof plan under these definitions** (not mechanised; the stubs can't be replaced from a proof file):
  Prove `posEnt e = l` by induction on `reachableEnt e`.
  1. *Init:* `initialProc p` puts the broadcast component in `sleeping`, not `bcReady`. Use inversion and the bisimulation-contradiction tactics (`bisim_contra`).
  2. *Discrete step* `e -EA- a ->> e'`: discrete entity steps never change the position (every `stepDiscEnt` rule keeps `l`). If the broadcast component of `e` was already `bcReady m l`, apply the IH. Otherwise it moved into `bcReady m l`. Here a missing process-level backtracking lemma is needed, in the style of `ovReady_prev` (ProtAuxResults.v:433):
     `bcReady_prev : p -PA- a -PA> p' -> broadcastState p -> bcReadyState m l p' -> bcWaitState m zeroTime p /\ a = chanPos ;? [basePosition l]`
     (`bcWait` = `... + $<x>$chanPos<vL>? bcReady(m, vL) + ...`, SoftwareLanguage.v:133). Lifted through the parallel triple, an input on `chanPos` can only be matched by `stepDePosRead`, because no component outputs on `chanPos`. That rule forces the value read to be the entity's position, so `l = posEnt e = posEnt e'`.
  3. *Delay step* `e -ED- d ->> e'` (with `d > 0`, since `Delay` is a `posreal`): a delay of the broadcast component cannot enter `bcReady` from another state (an output prefix only idles in itself), so `e` was already in `bcReady m l`. Then `bcReady_urgent` (EntAuxResults.v:273, which needs `reachableEnt e` and is proved via `reachable_ent_prot`) gives `False`. The urgency lemma sits *below* this one in the file, so either move `bcReady_pos` below the urgency section or inline the `noSyncNow_tac` / `bcReady_outProc_out` argument.
  Finally, `posEnt e = l` gives `inPosEnt l e` by `destruct e; simpl in *; subst; constructor`.
- **Partial proof:** none. The goal `inPosEnt l e` has no introduction rule while it is a `Parameter`.

## `ovReady_pos`

- **Where:** `src/EntAuxResults.v` line 110 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Same as bcReady_pos: define inPosEnt and reachableEnt; also add an ovReady_urgent / ovReady_outProc_out lemma (missing today) and an ovReady backtracking helper.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`, EntAuxDefs.v:143; `inPosEnt`, EntAuxDefs.v:149)
- **Intent:** if a reachable entity's overlap component is in `ovReady m t l` (about to output `chanOutProc![m, l]`), then the entity is currently at position `l`.
- **Failure:** the conclusion `inPosEnt l e` is an opaque `Parameter`. The only visible statements that conclude `inPosEnt` are `bcReady_pos` (just above, also admitted) and this target. `bcReady_pos` needs `bcReadyStateEnt m l e`, which cannot be derived from `ovReadyStateEnt m t l e`: the broadcast and overlap components are independent parts of the `parTriple`. Interpreting `inPosEnt := fun _ _ => False` and `reachableEnt := fun _ => True` is consistent with every visible assumption, and it makes the statement false for any entity whose overlap component is in `ovReady`. So it can't be proved while the stubs are opaque.
- **Ripple-up:** in the safety cone. It is used at NARMsgPosition.v:254 (`lets OP : ovReady_pos H4 H9. eapply inPos_ent_net in OP.`) to show that the position in an overlap-component broadcast equals the sender's position. It has the same role as `bcReady_pos` at NARMsgPosition.v:246.
- **Suggested fix (stub definitions; statement unchanged):**
  ```coq
  Inductive inPosEnt (l : Position) : Entity -> Prop :=
    | ipeWitness p h k : inPosEnt l ([|p, l, h, k|]).
  (* reachableEnt: reflexive-transitive closure of initialEnt under -EA- / -ED-,
     declared after initialEnt; see NetAuxBasics.reachable_net_ent.fail.md *)
  ```
- **Proof plan under those definitions:** induct on `reachableEnt` with the invariant `forall m t l, ovReadyStateEnt m t l e -> posEnt e = l`.
  - *Init:* `initialProc p` puts the overlap component in `dormant`, so `ovReady` is impossible (state disjointness).
  - *Discrete step `e -EA- a ->> e'`:* the entity position is unchanged by every discrete rule. If `e'` is in `ovReady m t l`, then either the overlap component did not move, so `e` was already in `ovReady m t l` and the IH applies, or it moved. If it moved, `ovReady_prev` (ProtAuxResults.v:433, admitted) gives that `e` was in `ovWait m t x 0`, and the only `ovWait -> ovReady` action is `chanPos ;? [basePosition l']`. At the entity level that can only be synchronised by `stepDePosRead`, which forces `l' = posEnt e = posEnt e'`. A lifted helper is needed for this, analogous to `ovReady_ovWait_track_ent`.
  - *Delay step `e -ED- d ->> e'`:* this needs an urgency lemma `ovReady_urgent : reachableEnt e -> ovReadyStateEnt m t l e -> e -ED- d ->> e' -> False`, proved like `bcReady_urgent` (EntAuxResults.v:272): `ovReady` enables `chanOutProc ;! [m, l]` and the interface always accepts it. It also needs time-backtracking of `ovReady` (`ovReady` is a pure output prefix, so the predecessor under delay is also `ovReady m t l`). No `ovReady_urgent` exists in the frozen sources yet, and there is no `ovReady_outProc_out` lemma either; it would have to be added next to `bcReady_outProc_out`.
  - The comment's "disc_pre_pos [salvaged]" refers to this position-preservation fact for discrete steps. It is not present in the frozen sources.
- **Partial proof:** none. Nothing can be stated about `inPosEnt` until the stub is filled.

## `link_ent_outList`

- **Where:** `src/EntAuxResults.v` line 573 · **Lemma** · 2015 label: `5` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:wrong-step-relation (input disjunct uses -tl- ?? which has no rules; buffering is -ol- ??)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Change the input disjunct to lo -ol- v ?? -ol> lo' and InterfaceLanguage.outList_in_input_pres's premise accordingly; both fixed statements are proved with model+stdlib axioms only (link_ent_outList_fixed, link_ent_outList_input_pres_fixed).

- **Status:** FALSE (counterexample, verified in Rocq)
- **Intent:** a discrete entity step either leaves the output list `lo` unchanged, or the output list changes by buffering one message (input) or by forwarding one message (output).
- **Failure:** the input disjunct is stated at the *timed-list* level, `outList lo -tl- v ?? -tl> outList lo'`. But `stepTimedList` has no input rule at all: its rules are `stepTlFwdHd`/`stepTlFwd` (outputs `v !!`) and `stepTlDelEmp`/`stepTlDel` (delays). Buffering happens only at the output-list level (`stepOlBuff : mkOutputList l -ol- v?? -ol> mkOutputList (<(v, msgLatency)> :: l)`). So the `??` disjunct can never hold. The entity rule `stepDeIOProcInter` (the software outputs on `chanOutProc` and the interface buffers through `stepIntBuffOut`/`stepOlBuff`) makes `lo' = <(v,msgLatency)> :: lo`. Then `lo <> lo'`, there is no `??` timed-list step, and a `!!` step can't lengthen a list.
  Concrete instance (no reachability hypothesis is needed, since the lemma has none): `p = chanOutProc $<[]>$! nilProc`, `p' = nilProc`, `lo = mkOutputList []`, `lo' = mkOutputList [<([], msgLatency)>]`, `b = aeTau`, with `l, k, li, ln` arbitrary and kept. Lemmas `link_ent_outList_cex` and `link_ent_outList_false` below compile (checked with `--explore`, rc=0).
- **Ripple-up:** it's used only in `NetAuxBasics.outgoing_disc_pres` (line 632), which is in the safety cone and is used by `NARMsgPosition` line 56. That proof then calls `InterfaceLanguage.outList_in_input_pres` (Admitted, label 6) on the `??` disjunct. `outList_in_input_pres` has the same flawed `-tl- u ??` premise, so it is vacuously true and can't serve a corrected statement unchanged. `outgoing_disc_pres` itself is true: buffering only prepends, so membership is preserved. Only its support lemmas are mis-stated.
- **Suggested fix (option A, recommended: two statement changes and no proof-script change in `outgoing_disc_pres`):**
  ```coq
  Lemma link_ent_outList p p' l l' k k' li li' lo lo' ln ln' b :
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, lo -ol- v ?? -ol> lo'
    \/ outList lo -tl- v !! -tl> outList lo'.

  (* InterfaceLanguage.v *)
  Lemma outList_in_input_pres v u t lo lo' :
    <( v, t )> _: outList lo -> lo -ol- u ?? -ol> lo' ->
    <( v, t )> _: outList lo'.
  ```
  Both are proved below (`link_ent_outList_fixed`, `link_ent_outList_input_pres_fixed`; they compile). The script of `outgoing_disc_pres` (`lets LEO : link_ent_outList LE1. ... eapply outList_in_input_pres; eassumption.`) should type-check unchanged with them (checked by reading the script, not compiled), because the `??` hypothesis now has exactly the type the new `outList_in_input_pres` expects.
  *Option B:* keep `outList_in_input_pres` and phrase the input disjunct as `outList lo' = <(v, msgLatency)> :: outList lo`. The `??` branch of `outgoing_disc_pres` then becomes `rewrite ...; right; assumption` instead of the `outList_in_input_pres` call.
- **Partial proof / evidence:**
  ```coq
  Lemma link_ent_outList_cex (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
    [|chanOutProc $<[]>$! nilProc, l, {| li := li; lo := mkOutputList []; ln := ln |}, k|]
      -EA- aeTau ->>
    [|nilProc, l, {| li := li; lo := mkOutputList [<([], msgLatency)>]; ln := ln |}, k|] /\
    ~ (mkOutputList [] = mkOutputList [<([], msgLatency)>] \/ exists v,
       outList (mkOutputList []) -tl- v ?? -tl> outList (mkOutputList [<([], msgLatency)>])
    \/ outList (mkOutputList []) -tl- v !! -tl> outList (mkOutputList [<([], msgLatency)>])).
  Proof.
    split.
    - eapply stepDeIOProcInter with (v := []).
      + constructor. constructor.
      + constructor. constructor.
    - intros [E | [v [T | T]]].
      + inversion E.
      + inversion T.
      + inversion T.
  Qed.

  Lemma link_ent_outList_false (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
    ~ (forall p p' l l' k k' li li' lo lo' ln ln' b,
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, outList lo -tl- v ?? -tl> outList lo'
    \/ outList lo -tl- v !! -tl> outList lo').
  Proof.
    intros H. destruct (link_ent_outList_cex l k li ln) as [S N].
    apply N. eapply H. exact S.
  Qed.

  Lemma link_ent_outList_fixed p p' l l' k k' li li' lo lo' ln ln' b :
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, lo -ol- v ?? -ol> lo'
    \/ outList lo -tl- v !! -tl> outList lo'.
  Proof.
    intros S. inversion S; subst; try (left; reflexivity).
    - right. match goal with [V : _ -i- chanOutProc {? _ -i> _ |- _] =>
        inversion V; subst end. eexists. left. eassumption.
    - match goal with [V : _ -i- chanInProc {! _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - match goal with [V : _ -i- chanAN {! _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - match goal with [V : _ -i- chanIOEnv {? _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - right. match goal with [V : _ -i- chanIOEnv _! _ !_ _ -i> _ |- _] =>
        inversion V; subst end.
      match goal with [V : _ -ol- _ !! -ol> _ |- _] => inversion V; subst end.
      eexists. right. eassumption.
  Qed.

  Lemma link_ent_outList_input_pres_fixed v u t lo lo' :
    <( v, t )> _: outList lo -> lo -ol- u ?? -ol> lo' ->
    <( v, t )> _: outList lo'.
  Proof.
    intros I S. inversion S; subst.
    - simpl. right. exact I.
    - match goal with [V : _ -tl- _ ?? -tl> _ |- _] => inversion V end.
  Qed.
  ```
  Once the statement is corrected, the body of `link_ent_outList_fixed` is the proof. It uses only model and stdlib axioms.

## `reachable_ent_prot`

- **Where:** `src/EntAuxResults.v` line 25 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt (EntAuxDefs.v:143) as the inductive closure of initialEnt under -EA-/-ED- (declared after initialEnt); then the proof is a 3-case induction (compiled against a local copy).

- **Status:** BLOCKED-ON-STUB (reachableEnt)
- **Intent:** The process component of a reachable entity is a reachable protocol term.
- **Failure:** `reachableEnt : Entity -> Prop` is an opaque `Parameter` (EntAuxDefs.v:143). No lemma in scope eliminates `reachableEnt`; it only ever appears as a hypothesis. The explore check confirms the goal is `H : reachableEnt ([|p, l, h, k|]) |- reachableProt p` with nothing usable. The source comment at EntAuxResults.v:24 already says "Requires reachableEnt to be defined before it is proved."
- **Ripple-up:** Not in the safety cone. Its only user is `Ltac urgency_pre_tac` (EntAuxResults.v:141), which every `urgency_pre_tac2*` call builds on, i.e. the entity-level urgency lemmas (`*_ent_del` / `..._ED_...` family at EntAuxResults.v:200-410). It is true under the intended definition.
- **Suggested fix (stub definition):** use the reflexive-transitive closure of `initialEnt` under entity transitions, as the "Idea" comment at EntAuxDefs.v:144 says. This is the same definition proposed in `NetAuxBasics.reachable_net_ent.fail.md`:
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' d : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  `initialEnt` is defined after the stub (EntAuxDefs.v:154), so the stub must move below it.
- **Proof under that definition** (compiled against the frozen build with a local, prefixed copy of the inductive; see `EntAuxResults.reachable_ent_prot.v` HELPERS, explore rc=0). Induct over the generalised entity:
  ```coq
  Lemma reachable_ent_prot_aux e : reachableEnt e -> reachableProt (procEnt e).
  Proof.
    induction 1 as [e I | e e' a R IH S | e e' d R IH S].
    - inversion I as [p l h k IP FS]; subst. inversion IP; subst. simpl. constructor.
    - inversion S; subst; simpl in *; try assumption; eapply reachprDisc; eassumption.
    - inversion S; subst; simpl in *. eapply reachprDel; eassumption.
  Qed.
  (* target *)
  Proof. intro R. apply (reachable_ent_prot_aux _ R). Qed.
  ```
  The case split is this: an initial entity's process is `procProtocol` (`reachprBase`); entity discrete steps either leave the process unchanged or take a process step `p -PA- a -PA> p'` (`reachprDisc`); entity delays take a process delay (`reachprDel`).

## `nextModeEnt_not_stable`

- **Where:** `src/EntAuxResults.v` line 28 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `typo` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Annotate (m2 : Mode) so the 4th field is sing m2, and define the nextModeEnt stub (inductive on <|m,m2,t|>); the fixed lemma is then `intro H; inversion H` (compiled as nextModeEnt_not_stable_fixed on a local copy).

- **Status:** FALSE (for the intended definition of the stub) and BLOCKED-ON-STUB (`nextModeEnt`, EntAuxDefs.v:146). It is on the harness's known-inconsistent list.
- **Intent:** an entity whose mode state is a *stable* mode `sing m2` has no next mode. The comment says "immediate once nextModeEnt is defined".
- **Failure:** `m2` has no type annotation. It sits in the 4th field of `mkEntity`, so Rocq infers `m2 : ModeState`, not `Mode`; `--explore` confirms this (`m2 : ModeState` in the context). Every entity has the form `[|p, l, h, k|]`, so the statement as written is equivalent to `forall m e, ~ nextModeEnt m e`, which says the relation is empty. The helper `nextModeEnt_not_stable_equiv` proves this equivalence in the explore file.
  - While the stub is an opaque `Parameter`, the statement can't be proved: `nextModeEnt := fun _ _ => True` is a model of the context that refutes it.
  - For the intended definition (EntAuxDefs.v:147: "one constructor, in which the entity has mode state <m, m', d>"), it is **false**. Instantiate `m2 := <| m, m, zeroTime |>` with any `m : Mode`. `nextModeEnt_not_stable_cex` checks this in Rocq against a local copy of the intended definition.
  - It is also inconsistent with the admitted `tfsCurr_failSafe` (EntAuxResults.v:58, `tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m`), and with `nextEq_mode` whenever a `nextEqStateEnt` entity exists.
- **Ripple-up:** not in the safety cone. `grep -n nextModeEnt_not_stable frozen/*.v` finds no users, only its own definition. Fixing it or deleting it breaks nothing.
- **Suggested fix:** annotate `m2` as a stable mode (one character of intent, `(m2 : Mode)`):
  ```coq
  Lemma nextModeEnt_not_stable m1 (m2 : Mode) p l h :
    nextModeEnt m1 ([|p, l, h, m2|]) -> False.
  ```
  (The coercion `sing` then makes the 4th field `sing m2`.) Together with the stub completion
  ```coq
  Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
    | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
  ```
  the fixed statement is proved by `intro H; inversion H.` (checked as `nextModeEnt_not_stable_fixed`). Without completing the stub, the fixed statement also follows from the admitted `nextMode_ent_mState` (EntAuxResults.v:487): `nextModeMState (sing m2) = None <> Some m1`. That only works if the lemma is moved after `nextMode_ent_mState`, or `nextMode_ent_mState` is moved before it.
  - Note for the lead: `NetAuxBasics-6/NetAuxBasics.nextMode_ent_ex.fail.md` claims `nextModeEnt_not_stable` becomes a one-line inversion once the stub is defined. That holds only for the `(m2 : Mode)` version, not for the statement as written.
- **Partial proof:** see `EntAuxResults.nextModeEnt_not_stable.v` (HELPERS are demonstrations only, not for splicing).

## `tfsNext_prev_ent`

- **Where:** `src/EntAuxResults.v` line 42 · **Lemma** · 2015 label: `#back-track-lift-ent` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis reachableEnt e (and reachableNet n in NetAuxBasics.tfsNext_prev_net); prove by reachability once reachableEnt is defined.

- **Status:** FALSE (counterexample). Also NEEDS-HYPOTHESIS `reachableEnt e`.
- **Intent:** this lifts `ProtAuxResults.tfsNext_prev` to entities. If an entity's overlap component is in `tfsNext m` after a discrete step, then before the step it was either already in `tfsNext m`, or in `tfsStart`. Thesis: tfsStart --chanCurr?m--> tfsNext(m), with self-loops on tfsNext(m).
- **Failure:** the statement has no reachability or shape hypothesis on the pre-state `e`, so `e`'s process can be any `ProcTerm`. The process-level original `tfsNext_prev` assumes `overlapState p`, and the entity lift dropped that hypothesis. Counterexample, checked in Rocq (`--explore`, helper `tfsNext_prev_ent_cex` ends in `Qed`, uses only constructors and `ProcEquiv.bisim_refl`):
  - `q := nilProc $||$ tfsNext m $||$ nilProc`
  - `e  := [| outPrefix chanMCurr [] q, l, h, <|m, m, zeroTime|> |]`
  - `e' := [| q, l, h, sing m |]`
  - `e -EA- aeTau ->> e'` by `stepDeCurrWrite`, a mode-state current write.
  - `tfsNextStateEnt m e'` holds because the middle component is literally `tfsNext m`.
  - `e`'s process is an `outPrefix`, not a `_ $||$ _ $||$ _`, so `liftOverlap` fails on it and neither disjunct holds.
  So the lemma implies `forall (m : Mode) (l : Position) (h : Interface), False`.
- **Ripple-up:** `in_safety_cone=False`. The only user is `NetAuxBasics.tfsNext_prev_net` (proved from this lemma, no reachability hypothesis), which is false by the same counterexample lifted to a one-entity network. That in turn is used only in the commented-out `(*R*)` proof of `NARMisc.tfsNext_tfs_zero`. That proof inducts on `p : reachableNet n`, so a reachability hypothesis is available where it is needed. Nothing in the `safety` cone breaks.
- **Suggested fix:**
  ```coq
  Lemma tfsNext_prev_ent m e e' a : reachableEnt e -> tfsNextStateEnt m e' ->
    e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
  ```
  The same fix applies upstream: `tfsNext_prev_net m i n n' a : reachableNet n -> tfsNextStateNet m i n' -> n -NA- a -NA> n' -> ...`. Its proof gets `reachableEnt` from `reachable_net_ent`.
  I proved the fixed statement in Rocq relative to the existing admitted lemmas (helper `tfsNext_prev_ent_fixed`, compiles with `Qed`). It uses `reachable_ent_prot` (admitted, stub `reachableEnt`), `reachableProt_triple` (admitted), `link_ent_soft_disc` (admitted), `link_par_triple_discW_2` (admitted) and `tfsNext_prev` (proved). It does not use any known-inconsistent lemma.
- **Partial proof:** see `EntAuxResults.tfsNext_prev_ent.v` in this directory (HELPERS: counterexample + fixed version):
  ```coq
  Lemma tfsNext_prev_ent_fixed m e e' a : reachableEnt e -> tfsNextStateEnt m e' ->
    e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
  Proof.
    intros RE TN S.
    inversion TN as [p' l' h' k' TP]; subst.
    inversion TP as [q1 q2 q3 TQ]; subst.
    destruct e as [p l h k].
    lets RP : reachable_ent_prot RE.
    lets PS : reachableProt_triple RP.
    inversion PS as [p1 p2 p3 B O L]; subst.
    lets LE : link_ent_soft_disc S.
    destruct LE as [EQ | [b ST]].
    - left. rewrite EQ. constructor. exact TP.
    - lets W : link_par_triple_discW_2 ST.
      destruct W as [EQ2 | [b' ST2]].
      + subst. left. constructor. constructor. assumption.
      + right. constructor. constructor.
        eapply tfsNext_prev; eassumption.
  Qed.
  ```

## `currEq_mode`

- **Where:** `src/EntAuxResults.v` line 50 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Replace by a transition-local lemma (rangeBad m'' --chanMCurr<m>?--> step synchronises with stepMsOutCurr*, so m = currModeMState k); adding reachableEnt alone is not enough (see notes).

- **Status:** NEEDS-HYPOTHESIS (`reachableEnt e`), and then BLOCKED-ON-STUB (`reachableEnt`). Not refutable from the model axioms, but unprovable: it implies that `Mode` is a subsingleton.
- **Intent:** if the listener of an entity is in the `currEq m m''` state (it has just read the current mode `m` from the mode state on `chanMCurr` in `rangeBad m''`), then `m` is the entity's current mode.
- **Failure:** `currEqStateEnt m m'' e` constrains only the process term of `e` (`liftProcEnt (liftListen (fun p => p ~p~ currEq m m''))`). It says nothing about the mode state `k`, and `currModeEnt e = currModeMState k`. So for any `m1 m2 : Mode`, the entity
  `[| nilProc $||$ nilProc $||$ currEq m1 m1, mkPosition 0 0, mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil), sing m2 |]`
  satisfies `currEqStateEnt m1 m1 e` and has `currModeEnt e = m2`. Verified in Rocq (`--explore`, see `EntAuxResults.currEq_mode.v`):
  ```
  Lemma currEq_mode_cex :
    (forall m m'' e, currEqStateEnt m m'' e -> m = currModeEnt e) ->
    forall m1 m2 : Mode, m1 = m2.
  Proof.
    intros H m1 m2.
    apply (H m1 m1 ([| nilProc $||$ nilProc $||$ currEq m1 m1,
                       mkPosition 0%R 0%R, mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil), sing m2 |])).
    unfold currEqStateEnt, currEqStateProt. constructor. constructor.
    unfold currEqState. apply ProcEquiv.bisim_refl.
  Qed.
  ```
  `Mode` is an abstract `Axiom`, and the axioms don't force two distinct modes, so the statement is not refutable. But it is unprovable: a model with `Mode := bool` refutes it.
- **Ripple-up:** `grep -n currEq_mode` finds only `NARInsuff.v:220`, inside the commented-out old proof of `notifAbort_not_nextSince` (labelled `R`, currently `Admitted`). In that proof the entity comes from a reachable network (`rn : reachableNet n`). Not in the safety cone, so nothing live breaks.
- **Suggested fix:**
  ```
  Lemma currEq_mode m m'' e : reachableEnt e ->
    currEqStateEnt m m'' e -> m = currModeEnt e.
  ```
  This is still blocked while `reachableEnt` (EntAuxDefs.v:143) is an opaque `Parameter`. With `reachableEnt e` defined inductively as "reachable from an initial entity `[| initial protocol term, l, h, sing m0 |]` by entity discrete/delay steps (`-EA-`, delays)", the proof is an induction on reachability with an invariant of the form "listener in `currEq m m''` ⇒ `currModeMState k = m`". Base case: the initial listener is not in `currEq`. Step: the listener enters `currEq m m''` only via `rangeBad m''` reading `chanMCurr<vM>?`, which synchronises with `stepMsOutCurrSing`/`stepMsOutCurrTrans` and so reads exactly `currModeMState k`. **Caveat for the owner:** the invariant must also survive interleaved steps of the other two components while the listener sits in `currEq`. The only actions that change `currModeMState` are `chanMCurr @?` (`stepMsSwitch`, from `switchCurr`/`tfsCurr` outputs) and `chanMStable @?` (abort, which keeps the current mode). So the invariant must be strengthened to rule out the overlap/broadcast components emitting `chanMCurr!` while the listener is in `currEq`. On the `switchBc` path this holds because the listener is paused first (`chanPause!`). The `tfsCurr` path needs a separate argument. This strengthening is the real content of the proof once the stub is filled.
- **Partial proof:** none for the target itself. The counterexample helper above compiles.

## `ovAbort_unstable`

- **Where:** `src/EntAuxResults.v` line 53 · **Lemma** · 2015 label: `#inter-component` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt (inductive closure of initialEnt); prove by reachability induction with the strengthened overlap-band invariant from the write-up. Separately consider adding the missing WRITE-STBL entity rule (definition change).

- **Status:** BLOCKED-ON-STUB (`reachableEnt`, EntAuxDefs.v:143)
- **Intent:** if the overlap component of a reachable entity is in `ovAbort` (= `chanMStable!dormant`, about to abort the pending mode switch), then the entity's mode state is a transition state `<| m, m', t |>`. In other words, there is always a pending transition for `ovAbort` to abort (thesis §"overlap component": "Aborting a transition is achieved by the process ovAbort via an output on chanStable").
- **Failure:** the only hypothesis that could constrain `mstEnt e` is `reachableEnt e`, and that is an opaque `Parameter`. Nothing visible before the target concludes anything about the mode state from `reachableEnt`. The visible facts are `reachable_ent_prot` (admitted, which only gives `reachableProt p`) and `currEq_mode`, which is about the listener. `ovAbortStateEnt e` only constrains the process component (`liftProcEnt (liftOverlap ovAbortState)`).
  Reading `reachableEnt := fun _ => True` is consistent with every visible assumption, and under it the statement is false. **Verified in Rocq (explore check, compiled at the target's position):**
  ```coq
  Lemma ovAbort_unstable_cm (m : Mode) (p1 p3 : ProcTerm) (l : Position) (h : Interface) :
    ovAbortStateEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |]) /\
    ~ unstable (mstEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |])).
  Proof.
    split.
    - unfold ovAbortStateEnt, ovAbortStateProt. constructor. constructor.
      unfold ovAbortState. apply ComhCoq.ProcEquiv.bisim_refl.
    - simpl. intro U. inversion U.
  Qed.
  ```
  So the target cannot be proved while `reachableEnt` stays opaque.
- **Ripple-up:** **not** in the safety cone. Its only user is `ovAbort_urgent` (EntAuxResults.v:287-290, `lets OUS : ovAbort_unstable U U0`), and `grep -n ovAbort_urgent` finds no users of that lemma. Nothing above it breaks.
- **Suggested fix (stub definition; statement unchanged):** the reflexive-transitive closure of `initialEnt`, as in `NetAuxBasics.reachable_net_ent.fail.md`. Move the stub below `initialEnt` (EntAuxDefs.v:156):
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' d : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
- **Proof plan under that definition:** induct on `reachableEnt` with the strengthened invariant
  `Inv e := (exists m', initStateEnt m' e) \/ (exists m t x y, ovWaitStateEnt m t x y e) \/ (exists m t l, ovReadyStateEnt m t l e) \/ ovAbortStateEnt e \/ (exists m, switchBcStateEnt m e) \/ switchCurrStateEnt e  ->  unstable (mstEnt e)`.
  The overlap component must sit in one of these states throughout a pending switch.
  - *Init:* `initialProc` puts the overlap component in `dormant`, which is disjoint from all six states.
  - *Entering the band:* the only way in is `dormant --chanMNext<m'>?--> init m'`. At entity level that synchronises via `stepDeNextRead` with `k -ms- chanMNext .! m'`, and only `stepMsOutNext` provides that, so `k` is `<|m,m',t|>`. All other in-band moves (`init→ovWait→ovReady→ovWait`, `ovWait --chanAbort?--> ovAbort`, `ovWait --chanPause!--> switchBc`, `switchBc→switchCurr`) are process-internal taus, so they leave `k` unchanged. The backtracking lemmas needed are `ovlp_abort_in` (ProtAuxResults.v:905, admitted) for `ovAbort`, plus analogous `*_prev` facts for the other states.
  - *Mode state changes while in the band:* (i) delays keep a transition state a transition state (`stepMsDelTout`/`DelGuard`/`Timeout`); (ii) `stepDeTest`/`stepMsInit` only fire from a stable `k`; (iii) `stepMsSwitch` needs a process output `chanMCurr *!` (`stepDeCurrWrite`). Only `switchCurr` and `tfsCurr` emit that, and both are overlap states, so it can only happen as the exit `switchCurr → switchListen`, which leaves the band. (iv) `stepMsAbort` (`chanMStable @?`): see the finding below. It is currently unreachable, so it cannot break the invariant. Under a corrected semantics only `ovAbort → dormant` emits it, which also leaves the band. `bc_mStable_out_not` and `ovlp_mStable_out_not` (ProtAuxResults.v:914-918) cover the other components. The listener (`currOK`/`currComp`) only *inputs* `chanMStable`, via `stepDeRdStbl`, which needs a stable `k`, so it never fires in the band.
  - The target then follows from `Inv` applied to its `ovAbort` disjunct.
- **Side finding (definition discrepancy, worth a separate report):** `stepDiscEnt` (EntityLanguage.v:127-185) has **no WRITE-STBL rule**. The thesis (§4 entity semantics, around thesis.txt:5477) has `P --chanStable!--> P'`, `K --chanStable?--> K'` ⟹ `⟨P,l,I,K⟩ --τ--> ⟨P',l,I,K'⟩`. The Rocq code only has `stepDeRdStbl` (process *input*, mode-state *output*). As a result, the `ovAbort` output `chanMStable *!` and the `tfsNext` self-loop `chanMStable!` can never synchronise with the mode state's `stepMsAbort` (`<|m,m',t|> -ms- chanMStable @? -ms> m`), so an entity in `ovAbort` can never take its discrete step. `ovAbort_urgent` then forbids it from delaying. Proposed addition (needs owner approval: it is a definition change):
  ```coq
  | stepDeWrStbl : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState),
    p -PA- chanMStable *! -PA> p' -> k -ms- chanMStable @? -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  ```
  The proof plan above holds with or without this rule.
- **Partial proof:** none for the target itself (`introz U.` leaves `U : reachableEnt e`, `U0 : ovAbortStateEnt e` ⊢ `unstable (mstEnt e)`, with no usable facts about `U`). The counter-model helper above compiles.

## `tfsCurr_failSafe`

- **Where:** `src/EntAuxResults.v` line 58 · **Lemma** · 2015 label: `#inter-component` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableEnt e, drop the unused (m : Mode) parameter, define nextModeEnt; additionally forbid process-internal synchronisation on chanMNext/chanMCurr/chanMStable, otherwise even the reachable version is false.

- **Status:** BLOCKED-ON-STUB (`nextModeEnt`), plus NEEDS-HYPOTHESIS (`reachableEnt e`, itself a stub). There is also a modelling issue: the statement is still false for reachable entities under the intended definition, because overlap and listener can synchronise internally on `chanMNext`.
- **Statement (frozen, `src/EntAuxResults.v:58`):**
  ```coq
  Lemma tfsCurr_failSafe (e : Entity) (m : Mode) :
    tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m.
  ```
  (The parameter `m` is unused. The existential shadows it.)
- **Intent:** when the overlap component is in `tfsCurr`, it has just written `failSafeSucc m` to the mode state on `chanMNext`. So the mode state is `<| m, failSafeSucc m, t |>`, and its next mode is fail-safe.

### Failure

1. **Opaque stub.** `nextModeEnt : Mode -> Entity -> Prop` is a `Parameter` (`EntAuxDefs.v:146`). Before the target, only one lemma in scope mentions it: `nextModeEnt_not_stable`, which is an elimination lemma and is on the harness's forbidden (inconsistent) list. `NetAuxBasics.v:906` is not imported here. Nothing in scope can introduce `nextModeEnt`. Instantiating it as `fun _ _ => False` refutes the statement, because `tfsCurrStateEnt` is inhabited. So it can't be proved while the stub is opaque.

2. **False under the intended definition when there is no reachability hypothesis** (verified in Rocq). Take the definition from the stub's comment:
   ```coq
   Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
     | nme p l h m t : nextModeEnt m' ([| p, l, h, <| m, m', t |> |]).
   ```
   The entity `[| nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m |]` is in `tfsCurrStateEnt` and has a stable mode state, so it has no next mode. This is `tfsCurr_failSafe_cex` in `EntAuxResults.tfsCurr_failSafe.v`, which compiles.

3. **Still false for reachable entities: internal `chanMNext` synchronisation** (the step is verified in Rocq; the reachability path is argued informally because `reachableEnt` is a stub). `tfsNext m` offers `chanMNext<failSafeSucc m>!`. The listener states `currOK m''` and `currComp m'' r` offer `chanMNext<vM'>?`. The process-level `$||$` allows `stepDpSyncLR` between them, and `stepDeProcTau` lifts that to an entity τ-step that **does not touch the mode state**. The overlap then reaches `tfsCurr` with mode state `sing m`. Two lemmas in the `.v` file establish this:
   - `tfsCurr_failSafe_bypass` proves `[| nilProc $||$ tfsNext m $||$ currOK m'', l, h, sing m |] -EA- aeTau ->> [| nilProc $||$ liftNameProc tfsCurrN $||$ q3, l, h, sing m |]`, and that the target is in `tfsCurrStateEnt`.
   - `tfsCurr_failSafe_unfold` proves `liftNameProc tfsCurrN ~p~ tfsCurr`.

   A plausible trace from `initialEnt` reaches the source state, starting from `[| sleeping $||$ dormant $||$ listening, l, h, m0 |]`:
   1. The listener takes an `chanAN` notification with mode `m0` and an insufficient range, then reads `chanMCurr` and reaches `currEq m0 m0`, then `badOvlp`.
   2. `chanBad!` synchronises with `dormant`'s `chanBad?`. The overlap moves to `tfsStart` and the listener to `listening`.
   3. The overlap reads `chanMCurr`. It is now in `tfsNext m0`.
   4. The listener takes another notification with mode `m'' <> m0` and an insufficient range, and reaches `currOK m''`. The `gotMsg`→`currComp` path also works.
   5. The internal `chanMNext` sync moves the overlap to `tfsCurr` while the mode state is still `sing m0`.

   With any definition of `nextModeEnt` that reads the mode state, the conclusion fails at this point.

### Ripple-up

- Not in the safety cone (per `show`).
- The only consumer is the planned proof of `EntAuxResults.tfsBc_failSafe` (line 69, label `C`, currently `introz U. Admitted.`). The proof sketch comment says to backtrack to `tfsCurr` and then apply this lemma. `tfsBc_failSafe` is used in `NARNonFS_currSince.v:176`. The planned proof route of `tfsBc_failSafe` via this lemma breaks. `tfsBc_failSafe` itself may survive. In the bypassed state, `tfsCurr`'s `chanMCurr!` is an empty output that needs `stepMsSwitch` on a *transitional* mode state, so the overlap can't reach `tfsBc` from mode state `sing m0` (barring a similar internal capture).

### Suggested fix

1. Define the stub as its comment describes (inductive on `<| m, m', t |>`, as above). Define `reachableEnt` as the reflexive-transitive closure of `initialEnt` under the entity transitions.
2. Add reachability and drop the unused parameter. This requires approval, because it changes the statement:
   ```coq
   Lemma tfsCurr_failSafe (e : Entity) :
     reachableEnt e -> tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m.
   ```
3. **And** stop processes from capturing mode-state channels internally. Either:
   - restrict `stepDpSync*` (or `stepDeProcTau`) so the channels `chanMNext`, `chanMCurr`, `chanMStable` never synchronise between process components; or
   - give the listener separate read channels from the overlap's write channels.

   Without (3), the statement in (2) is still false, by the trace above.

With (1)–(3), the proof is a reachability induction with this invariant: overlap in `tfsCurr` → mode state is `<| m, failSafeSucc m, t |>`. Entry happens only via `stepDeNextWrite` from `tfsNext` (`stepMsInit` with `failSafeSucc_successor`). While in `tfsCurr`, only the overlap could abort or switch the mode state (`chanMStable!`/`chanMCurr!`), the listener only reads it, and delays keep the transitional shape. `failSafeSuccFS` then gives `failSafe`.

### Partial proof

See `EntAuxResults.tfsCurr_failSafe.v` in this directory, copied from `EntAuxResults-1` and re-verified with `--explore` (rc=0). Its HELPERS hold the compiled demonstrations `tfsCurr_failSafe_nextModeEnt`, `tfsCurr_failSafe_cex`, `tfsCurr_failSafe_unfold` and `tfsCurr_failSafe_bypass`. The PROOF section is `Admitted`.

## `tfsNext_currMode`

- **Where:** `src/EntAuxResults.v` line 78 · **Lemma** · 2015 label: `Proof: Induction on reachableEnt.` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `bisim-state-param-tracking`
- **Fix (audit summary):** Restate as failSafeSucc (currModeEnt e) = failSafeSucc m (all tfsNext_urgent needs: k0 -mtr-> failSafeSucc m), with reachableEnt defined; or track the literal overlap derivative instead of a bisimulation class.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`)
- **Intent:** in a reachable entity whose overlap component is in `tfsNext m`, the mode state's current mode is `m`. The overlap entered `tfsNext m` by reading `m` on `chanMCurr` from `tfsStart`, and nothing can change the current mode while it stays there.
- **Failure:** `reachableEnt` is an opaque `Parameter` (EntAuxDefs.v:143). The only fact about it visible before the target is the admitted `reachable_ent_prot : reachableEnt [|p,l,h,k|] -> reachableProt p`, which says nothing about the mode state `k`. `tfsNextStateEnt m e` (`liftProcEnt (liftOverlap (tfsNextState m))`) constrains only the process. So the statement is independent of the current context. Take the interpretation `reachableEnt [|p,l,h,k|] := reachableProt p`, which satisfies `reachable_ent_prot`, and the entity `[| p, l, h, sing m1 |]` where `p` is a reachable protocol term with its overlap in `tfsNext m2` and `m1 <> m2`. That entity satisfies both hypotheses and refutes the conclusion. No proof can exist until the stub is defined.
- **Ripple-up:** not in the safety cone. Its only user is `EntAuxResults.tfsNext_urgent` (EntAuxResults.v:251), which is used by `NARMisc.v:363`. `NetAuxBasics.tfsNext_currModeNet_eq`'s suggested fix (see NetAuxBasics-6's fail note) also relies on it. The statement is true under the intended definition, so nothing breaks up the chain once `reachableEnt` is defined.
- **Suggested fix (definition of the stub, as its comment says: reflexive-transitive closure of `initialEnt`):**
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  (`initialEnt` must be moved above it, or the definition placed after `initialEnt`.)
  **Proof plan under this definition** (no strengthened invariant needed). Induct on `reachableEnt e`.
  1. *Init:* `initialProc p` forces `p = procProtocol`, whose overlap is `dormant`, not `tfsNext`. Contradiction.
  2. *Discrete step `e -EA- a ->> e'`:* `tfsNext_prev_ent` gives `tfsNextStateEnt m e \/ tfsStartStateEnt e`.
     - Previous state `tfsStart`: only `tfsStart`'s `chanMCurr<vM>?` input leads to `tfsNext`, so the entity step is `stepDeCurrRead` with `k -ms- chanMCurr .! m' -ms> k'`. Both `stepMsOutCurrSing` and `stepMsOutCurrTrans` force `m' = currModeMState k = currModeMState k'`, and the new overlap state is `tfsNext m'`, so `m = m'`.
     - Previous state `tfsNext m`: by IH `currModeEnt e = m`. By `curr_switch_mState`, the current mode can change only through `chanMCurr @?`, that is, entity rule `stepDeCurrWrite`. That rule needs the process to output `chanMCurr *!`, which only `switchCurr`/`tfsCurr` (overlap) can do, and the overlap is in `tfsNext`. Every other entity rule leaves `k` unchanged or moves it by an MState step that keeps the first component (`stepMsAbort`, `stepMsInit` via `stepDeTest`/`stepDeNextWrite`, the outputs). So `currModeEnt e' = m`.
  3. *Delay step:* every `stepMsDel*`/`stepMsTimeout` rule keeps the first component of the mode state. The process is still `tfsNext m`, by delay preservation of the overlap state or by urgency.
  A process-level lemma "`tfsNextStateProt m p -> ~ p -PA- chanMCurr *! -PA> p'`" is the only new ingredient beyond existing tracking lemmas.
- **Partial proof:** none. The target is not provable while `reachableEnt` is opaque.

## `switchCurr_mState`

- **Where:** `src/EntAuxResults.v` line 92 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt; prove with the strengthened init/ovWait/ovReady/switchBc invariant (d <= x etc.) from the write-up.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`)
- **Intent:** in a reachable entity whose overlap component is in `switchCurr`, the mode state is mid-transition and its timer has run out: `mstEnt e = <| m, m', zeroTime |>`. Thesis Listing 7.27 gives the same property as "next mode is m'". Its purpose is urgency: `<|m,m',0|>` is exactly the mode state that can input `chanMCurr @?` (`stepMsSwitch`, `mst_tout_mCurr_in`), which matches the `chanMCurr *!` output of `switchCurr`. That is how `swithcCurr_urgent` (EntAuxResults.v:342) uses it.
- **Failure:** `reachableEnt` is an opaque `Parameter` (EntAuxDefs.v:143). `Print reachableEnt` gives `*** [ reachableEnt : Entity -> Prop ]`. After `intros R S; inversion S`, the explore check shows this goal:
  ```
  R : reachableEnt ([|p, l, h, k|])   SP : switchCurrStateProt p
  ============================
  exists m m', mstEnt ([|p, l, h, k|]) = <| m, m', zeroTime |>
  ```
  The goal is about the mode-state component `k`. In scope, the facts that eliminate `reachableEnt` are all admitted:
  - `reachable_ent_prot` (process only, says nothing about `k`);
  - `ovAbort_unstable` and `tfsNext_currMode`, whose hypotheses need the overlap component in `ovAbort`/`tfsNext`, which is disjoint from `switchCurr`.

  So the statement is independent of the context. Consider the interpretation
  `reachableEnt [|p,l,h,k|] := reachableProt p /\ (ovAbortStateProt p -> unstable k) /\ (forall m, tfsNextStateProt m p -> currModeMState k = m)`.
  It satisfies all three admitted facts. It also admits `[| p, l, h, sing m |]` with `p` a reachable protocol term whose overlap is in `switchCurr`. Such a `p` exists: `reachableProt` lets the process take `chanMNext?`/`chanMCurr?`/`chanPause!`/`chanWake!` steps alone, without a mode-state partner. That entity refutes the conclusion. No proof can exist until the stub is defined.
- **Ripple-up:** not in the safety cone (`show`: `in_safety_cone=False`). Its only user is `EntAuxResults.swithcCurr_urgent` (EntAuxResults.v:347, `lets SMS : switchCurr_mState U U0`), which has no further textual users in the frozen sources. The `NARNonFS_currSince.v:180` site builds a `switchCurrStateEnt` but doesn't call this lemma. The statement is true under the intended definition (below), so nothing breaks up the chain once the stub is filled.
- **Suggested fix:** define the stub as in the sibling notes (`w1b-11/EntAuxResults.reachable_ent_prot.fail.md`, `w1b-05/EntAuxResults.tfsNext_currMode.fail.md`), i.e. the reflexive-transitive closure of `initialEnt`. The stub must move below `initialEnt`:
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  The statement itself needs no change.

  **Proof plan under that definition.** Unlike `tfsNext_currMode`, direct induction is too weak. The 2015 comment says this needs a strengthened invariant covering the whole overlap "transition" path, proved by one induction on `reachableEnt`. Writing `k = mstEnt e`, `p = procEnt e`:
  ```
  Inv(e) :=
     (initStateProt m' p             -> exists m d, k = <|m, m', d|> /\ d <= modeTransTime m m' _)
  /\ (ovWaitStateProt m' t x y p     -> exists m d, k = <|m, m', d|> /\ d <= x /\ d <= t - period m' + y)
  /\ (ovReadyStateProt m' t l p      -> exists m d, k = <|m, m', d|> /\ d <= t - period m')
  /\ (switchBcStateProt m' p         -> exists m, k = <|m, m', zeroTime|>)
  /\ (switchCurrStateProt p          -> exists m m', k = <|m, m', zeroTime|>)
  ```
  The target is the last conjunct. Cases:
  1. *Init:* `procProtocol`'s overlap is `dormant`, so every conjunct is vacuous.
  2. *Entering `init m'`:* only via `dormant`'s `chanMNext<vM'>?`. This syncs with the mode state's `stepMsOutNext`, which needs `k = <|m, m', d|>`. That `d` came from `stepMsInit` (`= modeTransTime m m' p`) and has only decreased since (`stepMsDel*`/`stepMsTimeout`). Carrying `d <= modeTransTime` in the `dormant` case needs one more conjunct: dormant with a transitional `k` has `d <= modeTransTime`. The same invariant holds for every transitional `k`, and can be kept as a separate global conjunct.
  3. *`init` → `ovWait(m', T, T, 0)`* with `T = waitTime m m' _ + period m'` and `m` read from `chanMCurr` (`stepMsOutCurrTrans`, so `m = currModeMState k`). Then `d <= modeTransTime <= waitTime = T - period m'` by `timeMax` in `waitTime`. Matching the two `m -mtr-> m'` proofs needs the existing `proof_irrelevance`-based fact (ComhBasics.v:673) or equivalent.
  4. *`ovWait` delays by δ:* `d`, `x`, `y` all drop by δ (saturating at 0) and `t` is fixed, so both inequalities are preserved.
  5. *`ovWait` → `ovReady(m', t, l)`* when `y = 0`: `d <= t - period m'`.
  6. *`ovReady` → `ovWait(m', t - p, t - p, p)`* with `p = period m'`: `d <= t - p` gives both conjuncts.
  7. *`ovWait` → `switchBc m'`* via `$<x>$chanPause!`, enabled only when `x = 0`, so `d = 0`.
  8. *`switchBc` → `switchCurr`* via `chanWake!`: `k` is unchanged. Delays keep `<|m,m',0|>` (`delMStateTout`).
  9. *Frame:* while the overlap is in any of these states, `k` can lose its transitional form only by `chanMStable @?` (needs `ovAbort`/`tfsNext` outputting `chanMStable *!`) or `chanMCurr @?` (needs `switchCurr`/`tfsCurr` outputting `chanMCurr *!`). `stepMsInit` needs a stable `k`. Only the overlap component emits these outputs, and in cases 2–8 it isn't in such a state, except `switchCurr` itself, which leaves the invariant's scope on that step.

  The only new process-level ingredients are "which overlap states can output `chanMStable`/`chanMCurr`" and "the `$<x>$` guard is enabled only at `x = 0`". The existing backtracking (`*_prev_ent`) and urgency tactics should cover the rest.
- **Partial proof:** none possible while the stub is opaque. The explore script that confirms the goal shape is in `EntAuxResults.switchCurr_mState.v`.

## `tfsListen_paused`

- **Where:** `src/EntAuxResults.v` line 114 · **Lemma** · 2015 label: `C` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:false-invariant (listener is not paused on the fail-safe path)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete it (needs owner approval) and re-prove tfsListen_urgent from del_listening_pre plus the tfsListen_abort_in/bad_in/unpause_out activation lemmas.

- **Status:** FALSE (counterexample; and still false with a reachability hypothesis added)
- **Intent:** a helper for `tfsListen_urgent`: "when the overlap component is in `tfsListen`, the listener
  component is `paused`", so the overlap's `chanUnpause!` can synchronise with the listener's
  `chanUnpause?`, which by maximal progress rules out delay.
- **Failure:**
  1. *As stated (no hypothesis on p1, p3):* trivially false. `nilProc $||$ tfsListen $||$ nilProc` satisfies
     `tfsListenStateProt`, but `nilProc` is not bisimilar to `paused` (`paused` enables `chanUnpause *?`,
     `nilProc` enables nothing). Rocq-verified: `tfsListen_paused_cex` in
     `EntAuxResults.tfsListen_paused.cex.v` (Qed in explore mode; adapted from EntAuxResults-2's attempt).
  2. *Adding `reachableProt (p1 $||$ p2 $||$ p3)` does not rescue it.* The listener is only ever paused by
     `ovWait`'s `chanPause!`, i.e. during a *mode switch* (`switchBc/switchCurr/switchListen`). The
     fail-safe path `dormant/ovWait --bad?--> tfsStart -> tfsNext -> tfsCurr -> tfsBc --trans!--> tfsListen`
     never pauses the listener. The thesis says so itself: Example 5.13 (thesis.txt ~l.7041-7050) gives the
     reachable configuration `sleeping | tfsListen | listening` and explains that `listening`'s self-loop
     `cUnpause? qlistening` exists precisely to absorb `tfsListen`'s `cUnpause!`.
     In Rocq I proved (relative to the admitted thesis lemma `ProtAuxResults.paused_switch`, the only
     non-model admitted assumption):
     ```
     Lemma tfsListen_paused_reach_contra p :
       reachableProt p -> tfsListenStateProt p -> pausedStateProt p -> False.
     ```
     (proof in the `.cex.v`: `paused_switch` turns `paused` into `switchState`; `tfsListen` enables
     `chanAbort *?`, none of `switchBc m`/`switchCurr`/`switchListen` does). So the reachable version of the
     lemma would be equivalent to "`tfsListen` is unreachable", contradicting Example 5.13.
- **Ripple-up:** `grep`: only user is `EntAuxResults.tfsListen_urgent` (l.242), which is itself used by
  `NARMisc.v:371`. `show` reports `in_safety_cone=False`. `tfsListen_urgent` is (as far as the thesis goes)
  *true*, but its current proof route through this lemma is unsound.
- **Suggested fix:** delete `tfsListen_paused` (statement change needs owner approval) and re-prove
  `tfsListen_urgent` along the thesis's own sketch (Listing 7.28 and the `del_ovlp` comment): use
  `del_listening_pre` (EntAuxResults l.405, currently *after* `tfsListen_urgent`, so one of the two must be
  moved). It gives listener ∈ {abortOvlp, badOvlp, listening, paused}; in each case a synchronisation with
  `tfsListen` exists: `abortOvlp` outputs `chanAbort *!` vs `tfsListen_abort_in`; `badOvlp` outputs
  `chanBad *!` vs `tfsListen_bad_in`; `listening` and `paused` input `chanUnpause *?` vs
  `tfsListen_unpause_out`. If a protocol-level replacement helper is wanted, a true one is:
  ```
  Lemma tfsListen_listener_sync p3 :
    abortOvlpState p3 \/ badOvlpState p3 \/ listeningState p3 \/ pausedState p3 ->
    discActEnabled p3 (chanAbort *!) \/ discActEnabled p3 (chanBad *!) \/
    discActEnabled p3 (chanUnpause *?).
  ```
  (each disjunct by `activation_tac`, cf. `paused_unpause_in`), which together with `del_listening_pre`
  and the existing `tfsListen_*_in/out` lemmas suffices for `tfsListen_urgent`.
- **Partial proof:** none possible; see `EntAuxResults.tfsListen_paused.cex.v` for both Rocq-checked refutations.

## `gotMsgStateEnt_urgent`

- **Where:** `src/EntAuxResults.v` line 201 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Restore the thesis noComm clause forall l, a <> chanPos;?[basePosition l] inside EntityLanguage.noSyncNow (definition change, needs approval); the target is then provable without reachableEnt (validated on a local copy: gotMsgStateEnt_urgent_fixedA).

- **Status:** FALSE (counterexample) for every faithful definition of the `reachableEnt` stub. The root cause is BLOCKED-ON-DEFINITION: `EntityLanguage.noSyncNow` leaves out the `chanPos` clause of the thesis's `noComm` (Def. 4.22). As stated, the lemma also depends on the opaque stub `reachableEnt`. The only route to a proof inside the frozen development goes through `reachable_ent_prot` and `reachableProt_triple`. That route is vacuous, because `reachableProt_triple` is refutable (see `w1b-14/ProtAuxResults.reachableProt_triple.fail.md`). The prior attempt `EntAuxResults-2/EntAuxResults.gotMsgStateEnt_urgent.vacuous.v` uses exactly that route: it gets `listenerState` for a gotMsg process, which is impossible. Don't accept it.

- **Intent:** an entity whose listener is in `gotMsg m l` (it has just taken a message off `chanInProc` and now has to read its own position on `chanPos`) is urgent, meaning it cannot delay. In the thesis this holds because position reads are always available (rule POS-READ), and `noSyncEnt`/`noComm` forbid delay whenever `P` can input on `chanPos`.

- **Failure:** the Rocq delay rule `stepTeDel` requires only `noSync p i k d`. Its `noSyncNow a p i k` checks only whether `p` can synchronise with the interface `i` or the mode state `k`. A `chanPos` read is a tau via `stepDePosRead`, which involves neither `i` nor `k`, so it never blocks a delay. At process level, `inPrefix` delays freely (`stepTpIn`). Hence a gotMsg entity can delay whenever its other components can.
  Mechanised in `EntAuxResults.gotMsgStateEnt_urgent.cex.v` (HELPERS; compiles under `--explore`). `Print Assumptions` lists only model axioms (`Mode`, `failSafeSucc`, `failSafeSuccFS`, `speedMax`, …) plus stdlib classical reals, FE and PI. No admitted lemma is used.
  ```coq
  Lemma gotMsgStateEnt_urgent_false (R : Entity -> Prop) (m0 : Mode) :
    (forall e, initialEnt e -> R e) ->
    (forall e e' a, R e -> e -EA- a ->> e' -> R e') ->
    ~ (forall (e e' : Entity) (d : Delay) m l,
         R e -> gotMsgStateEnt m l e -> e -ED- d ->> e' -> False).
  ```
  So the target fails for **any** `R` that contains the initial entities and is closed under discrete entity steps. That includes the stub's documented intent ("reflexive transitive closure of initialEnt under entity transition relations"). Witness:
  1. Start from `e0 = [| procProtocol, origin, I1, failSafeSucc m0 |]`, where `I1` has one incoming message `[m0, origin]` stamped `0`. This is `initialEnt`, since `initialEnt` allows any interface.
  2. One `aeTau` step (`stepDeIOInterProc`): `listening` inputs on `chanInProc` and the interface forwards, giving `e1 = [| sleeping || dormant || X, origin, I∅, failSafeSucc m0 |]`. Here `X` is the substituted `gotMsgN([m0, origin])` and `I∅` is the empty interface.
  3. `X ~p~ gotMsg m0 origin` (`gotMsgStateEnt_urgent_X_bisim`), so `gotMsgStateEnt m0 origin e1`.
  4. `e1 -ED- 1 ->> [| sleeping || dormant || gotMsg m0 origin, origin, I∅, failSafeSucc m0 |]` with `delta = origin`. Every discrete action of `sleeping || dormant || X` is an input on `chanWake`, `chanTrans`, `chanMNext`, `chanAbort`, `chanBad` or `chanPos`. The interface outputs only on `chanInProc`/`chanAN`, and a stable mode state outputs only on `chanMCurr`/`chanMStable`, so `noSync` holds. The `stepTpPar` sort side conditions hold because all three components are inputs only.

- **Ripple-up:** used only by `EntAuxResults.msgAbortPathEnt_urgent` (gotMsg case) → `NARMisc.msgAbortPathNet_urgent` → `NARIncomp.v:351`. **Not in the safety cone.** The same root cause very likely also falsifies `msgAbortPathEnt_urgent`. In its gotMsg case the mode state is unstable, but with the overlap in `ovWait` behind a running `$<y>$` guard nothing synchronises. I didn't mechanise this, because building concrete `possiblyIncompatible` modes needs more than the abstract axioms give. More broadly, the missing clause lets *any* entity whose only enabled software action is a `chanPos` read idle: `gotMsg`, and `bcWait`/`ovWait` once their `$<x>$`/`$<y>$` guards have expired. Timeliness arguments that rely on position reads being immediate (broadcast within `period`, `ovReady` timing) are therefore unsupported by the current semantics too.

- **Suggested fix (definition change; needs owner approval):** restore the thesis's `noComm` clause `∀l, ¬ P --chanPos⟨l⟩?-->`.
  - **A (faithful to the thesis, preferred):** in `EntityLanguage.v`,
    ```coq
    Definition noSyncNow (a : DiscAct) (p : ProcTerm)
      (i : Interface) (k : ModeState) : Prop :=
      discActEnabled p a ->
      (~discActEnabledInter (a^) i /\ ~discActEnabledMState (a^) k) /\
      (forall l : Position, a <> chanPos ;? [basePosition l]).
    ```
    `noSync` and `stepTeDel` stay unchanged. Because the clause sits inside `noSyncNow`, it is also enforced at every intermediate point of a delay, which is needed for timed guards that expire mid-delay. With this change the target is provable **without** using `reachableEnt` at all. This is validated in the `.cex.v` on a local copy of the fixed rule (`gotMsgStateEnt_urgent_noSyncNowA` / `_noSyncA` / `_delA`):
    ```coq
    Lemma gotMsgStateEnt_urgent_fixedA (e e' : Entity) (d : Delay) m l :
      gotMsgStateEnt m l e -> gotMsgStateEnt_urgent_delA e d e' -> False.
    ```
    The proof is 5 lines: invert the delay, instantiate `noSync` at `chanPos ;? [basePosition l]`, and use `activation_tac` to show that gotMsg enables that read. Only model axioms are used. The cost: the 6 or so sites that destructure `noSyncNow` (`EntAuxResults.v` 226/257/280/297/355, the tactics in `EntityLanguage.v` 370–394, and `NetAuxBasics.v` 664–710) need `[[NI NM] _]` instead of `[NI NM]`.
  - **B (less invasive):** leave `noSyncNow` alone and add a premise `noPosRead p d` to `stepTeDel`, where
    ```coq
    Definition noPosRead (p : ProcTerm) (d : Delay) : Prop :=
      forall l : Position, ~ discActEnabled p (chanPos ;? [basePosition l]) /\
      (forall p' (d' : Delay), d' < d -> p -PD- d' -PD> p' ->
         ~ discActEnabled p' (chanPos ;? [basePosition l])).
    ```
    The target's proof is the same. Proofs that only invert delays are unaffected apart from auto-generated hypothesis names. Proofs that construct entity delays must discharge `noPosRead`.
  - Either way the target can keep its statement, and the `reachableEnt e` hypothesis becomes unused.

- **Partial proof:** none for the statement as given, since it is refuted. The counterexample, the fix validation and the reusable helpers are all in `EntAuxResults.gotMsgStateEnt_urgent.cex.v`. Reusable pieces:
  - the `gotMsgStateEnt_urgent_vareq` tactic, which evaluates the opaque `varEqDec` tests left by `subProcTerm`/`listsToSub`, making `gotMsgN $(args)$` unfoldings literal;
  - the "non-variable-only" inversion loop `gotMsgStateEnt_urgent_inv`;
  - `gotMsgStateEnt_urgent_X_bisim`, an `app`-unfolding bisimulation pattern.

## `nextEq_mode`

- **Where:** `src/EntAuxResults.v` line 483 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `bisim-state-param-tracking` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete the state-invariant form and use a transition-local lemma (w1b-03's nextEq_mode_step: currOK -> step -> nextEq m' m'' -> nextModeMState k' = Some m'), plus define nextModeEnt.

- **Status:** BLOCKED-ON-STUB (`nextModeEnt`), and FALSE as stated under the stub's intended definition.
- **Intent:** if the listener of an entity is in the `nextEq m' m''` state (it has just read `m'` from the mode state on `chanMNext`), then the entity's mode state is in transition with next mode `m'`.
- **Failure:**
  1. `nextModeEnt` is an opaque `Parameter` (EntAuxDefs.v:146). Nothing usable constrains it. The only admitted fact that produces `nextModeEnt` for a specific mode is the blacklisted `nextModeEnt_not_stable`, and `tfsCurr_failSafe` only gives an existential. So the lemma can't be proved while the stub is opaque.
  2. Under the intended definition in the stub's comment ("mode state `<m, m', d>`, with `m'` the parameter"), the statement is false. `nextEqStateEnt m' m'' e` constrains only the software component and says nothing about the mode state. Counterexample: `e = [| nilProc $||$ nilProc $||$ nextEq m1 m2, l, h, sing m0 |]` satisfies `nextEqStateEnt m1 m2 e` because `bisim_refl` holds, but its mode state is stable. Verified in Rocq with `--explore`: `nextEq_mode_cex_intended` in `w1b-03/EntAuxResults.nextEq_mode.v` compiles with `Qed`. It uses a prefixed inductive `nextEq_mode_nextModeEntI m'` with the single constructor `[|p,l,h,<|m,m',d|>|]`. The earlier prover (`EntAuxResults-2/...cex.v`) showed the same with the opaque stub plus `nextModeEnt_not_stable`.
  3. Adding `reachableEnt e` probably doesn't fix it either. After the listener's `chanMNext` read (`currOK` → `nextEq`), `nextEq` is urgent but only blocks *time*. Another component can still act discretely before the listener's `nextEq` tau. For example, the overlap component can abort (`chanMStable @?` gives `stepMsAbort`, a stable mode state) or switch (`chanMCurr @?` on `<|m,m',0|>`). So as a state invariant, even of reachable entities, it is doubtful.
- **Ripple-up:** used only once, at NARInsuff.v:236. That line is inside the comment opened at NARInsuff.v:218 and closed at :314, part of the commented-out proof of `notifAbort_not_nextSince`. So no live proof depends on this lemma. Not in the safety cone. It is used with `nextMode_ent_mState` (also blocked on the stub) to turn `nextEqStateEnt x1 m' e'` into `nextModeMState k0 = Some x1`.
- **Suggested fix:** delete the state-invariant lemma and replace its single use with a *transition-local* fact. In NARInsuff, the listener step `currOK m'' → nextEq x1 m''` is a synchronisation on `chanMNext` with the mode state (`stepMsOutNext`, which leaves the mode state unchanged). So the needed fact is:
  ```coq
  Lemma nextEq_mode_step p l h k p' l' h' k' a m' m'' :
    currOKStateEnt m'' ([|p, l, h, k|]) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    nextEqStateEnt m' m'' ([|p', l', h', k'|]) ->
    nextModeMState k' = Some m'.
  ```
  It should be provable with `link_ent_proc_neq_disc` (case `p -PA- chanMNext ;? [baseMode m'] -PA> p'` paired with `k -ms- chanMNext .! m' -ms> k'`, where inversion gives `k = k' = <|_, m', _|>`) and the existing `currOK`/listener tracking lemmas. Separately, define `nextModeEnt m e := nextModeMState (mstEnt e) = Some m`, which makes `nextMode_ent_mState` trivial.
- **Partial proof:** none. The counterexample file is `w1b-03/EntAuxResults.nextEq_mode.v` (helpers section).

## `nextMode_ent_mState`

- **Where:** `src/EntAuxResults.v` line 487 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `stub` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Define the nextModeEnt stub (inductive on <|m,m',t|> or via EntityLanguage.nextModeEnt e = Some m), after which the proof is inversion or exact; and fix the partner lemmas tfsCurr_failSafe and nextEq_mode.

- **Status:** BLOCKED-ON-STUB (nextModeEnt)
- **Intent:** If an entity has next mode `m` (relation `nextModeEnt`), then its mode-state component is a transition state whose target is `m`, i.e. `nextModeMState k = Some m`. This is the elimination rule for the stub.
- **Failure:** `nextModeEnt : Mode -> Entity -> Prop` is an opaque `Parameter` (EntAuxDefs.v:146). Before the target, the only lemma with `nextModeEnt` in a hypothesis is `nextModeEnt_not_stable` (EntAuxResults.v:28), which is on the banned known-inconsistent list. Every other lemma (`tfsCurr_failSafe`, `nextEq_mode`) concludes `nextModeEnt`, so none of them eliminates it. Under the opaque stub, `nextModeEnt := fun _ _ => True` is a model of the context that refutes the target (take `k := sing m0`). The explore check shows the bare goal `H : nextModeEnt m ([|p,l,h,k|]) |- nextModeMState k = Some m`.
- **Ripple-up:** Not in the safety cone. Used once, at NARInsuff.v:237, to turn `nextEq_mode` into `nextModeMState k0 = Some x1` and derive a contradiction in a forward-tracking case. It is true under either definition below.
- **Suggested fix (stub definition):** one of the following. Both were checked in Rocq (explore, rc=0) against local prefixed copies in `EntAuxResults.nextMode_ent_mState.v`, where they are also proved equivalent (`nextMode_ent_mState_demo_equiv`).
  1. Per the "Idea" comment at EntAuxDefs.v:147. This matches `NetAuxBasics.nextMode_ent_ex.fail.md`:
     ```coq
     Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
       | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
     ```
     Target proof: `intro U. inversion U; subst. reflexivity.`
  2. Reuse the existing, now-shadowed function `EntityLanguage.nextModeEnt : Entity -> option Mode` (EntityLanguage.v:92):
     ```coq
     Definition nextModeEnt (m : Mode) (e : Entity) : Prop :=
       EntityLanguage.nextModeEnt e = Some m.
     ```
     Target proof: `intro U. exact U.` (it is definitional). Renaming one of the two homonymous `nextModeEnt`s would avoid the shadowing altogether.
- **Related note:** both definitions refute `nextModeEnt_not_stable` *as written* (where `m2` is inferred as `ModeState`). They prove the `(m2 : Mode)`-annotated version by `inversion`/`discriminate` (`nextMode_ent_mState_demo_not_stable`, `..._demo2_not_stable`). See `EntAuxResults.nextModeEnt_not_stable.fail.md` for that lemma's write-up.

## `gotMsg_gotRange_track_ent`

- **Where:** `src/EntAuxResults.v` line 500 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `eSubtract-vs-bPossInc-typing`
- **Fix (audit summary):** Fix the range typing first (make (|vL,l'|) (-) speedMax (.) msgLatency evaluate to a baseDistance, or let bPossInc accept baseNonneg), then restate as w1b-06 suggests: reachable pre-state, conclusion l = l' /\ gotRangeStateEnt m (canonical range) e' instead of parameter equalities.

- **Status:** FALSE. Two independent reasons: (a) the state predicates are bisimulation classes, so `m'` and `r` are
  determined only up to bisimilarity; (b) there is no reachability hypothesis, so a foreign component can feed
  `chanPos`. The Rocq-checked part is the key indistinguishability fact (`gotMsg_gotRange_track_ent_indist` in
  the `.v`). The full counterexample needs a positive bisimilarity proof (sketched below), which I did not mechanise.
- **Intent:** when an entity steps from a listener in `gotMsg m l1` to a listener in `gotRange m' r`, the listener
  read the entity's own position `l` on `chanPos`. So `l = l'`, `m = m'` and `r = dist2d l l1 -nn- speedMax*msgLatency`.
- **Failure:**
  `gotRangeStateProt m' r p'` only says `p3' ~p~ gotRange m' r`, and `gotRange m'' r` uses `r` and `m''`
  **only** through `possIncBool x m'' r`, for an input mode `x`. That happens in `currPincCheck` (`bPossInc vM m'' r`) and in
  `nextPincCheck` (`bPossInc vM' m'' r`). Every other continuation (`listeningN`, `badOvlpN`, `abortOvlpN`) forgets them.
  Hence `gotRange m1 r1 ~p~ gotRange m2 r2` whenever `forall x, possIncBool x m1 r1 = possIncBool x m2 r2`.
  For non-mode inputs both guards fail to evaluate, so `evalBoolExpFunTot` gives `false` for both `b` and `!~b` on both sides.
  1. *`r` counterexample (honest step, no intruder):* take `l1 := l` (message from the receiver's own position), the
     listener `p3 := gotMsg m l` and the entity step `stepDePosRead` (reads `basePosition l`). The derivative is
     `gotRangeN [m, (|l, l| (-) speedMax (.) msgLatency)]`, whose distance argument evaluates to `0`.
     Let `eps := speedMax*adaptNotif > 0`. Then `possIncBool x m eps = possIncBool x m 0 = true` for **every** `x`, because
     `possIncDist x m >= 2*speedMax*adaptNotif`; this is Rocq-checked as `gotMsg_gotRange_track_ent_indist`.
     So `p3' ~p~ gotRange m eps`, and the hypotheses hold with `r := eps`. The conclusion would force `eps = 0`.
  2. *`m` counterexample:* in any model with two modes `m1 <> m2` such that `minDistComp x m1 = minDistComp x m2`,
     `period m1 = period m2` and `trans m1 = trans m2` for all `x`, `possIncBool x m1 r = possIncBool x m2 r` for all `x, r`.
     So `gotRange m1 r ~p~ gotRange m2 r`, and `m = m'` is unprovable. It is consistent with the axioms in
     `ComhBasics.v`, which never separate modes.
  3. *Intruder on `chanPos`:* without `reachableEnt`, `p1` may be `chanPos $<[eBase (basePosition l2)]>$! nilProc`.
     The `stepDpSyncLR` tau then feeds `l2 <> l` to the listener, so the true range is `dist2d l2 l1 - ...`, not `dist2d l l1 - ...`.
  Mechanising (1) needs one positive bisimilarity: `gotRangeN [em, e] ~p~ gotRange m' r'` for any closed `em, e`
  with `forall b, evalBoolExpFun (bPossInc b em e) = evalBoolExpFun (bPossInc b m' r')`. The proof is a cofix over
  the finite derivative set `gotRange -> currPincCheck -> {currComp -> nextPincCheck, badOvlp}`, including the
  timed residuals of the `ifThen` branches. It needs the substitution clean-up tactics (`clean_proc_hyp`,
  `remove_resets_hyp`), because `varEq` is opaque. I estimated 2-4 hours and stopped, since the target is outside the safety cone.
- **Side finding:** the admitted protocol-level lemma used at the call site, `ProtAuxResults.gotMessage_next`,
  is also false as stated. After `chanPos ;? [v]` with `v` **not** a position (e.g. `baseMode _`), the distance
  expression fails to evaluate. Then `currPincCheckN [..]` has both guards `false` and is stuck. Any `gotRange m'' r` with a real `r`
  can always take a branch after a mode input, so no `r` exists. `goMsg_gotRange_track` (`r = mkDistance ...` exactly) is
  false for reason (1).
- **Ripple-up:** not in the safety cone. Its only user is `NARIncomp.v:138` (`msgAbort_not_nextSince`), which uses
  `GGE` to rewrite `x1` (from `gotMessage_next`) into `dist2d l l' -nn- ...`, transferring the `possiblyIncompatible`
  facts of `mapMsg` to `mapGrng`.
- **Suggested fix:** state the conclusion with the canonical range instead of equating parameters. Add
  reachability to exclude foreign `chanPos` writers:
  ```
  Lemma gotMsg_gotRange_track_ent (m : Mode) (l l' l1 : Position)
    (p p' : ProcTerm) h h' k k' a :
    reachableEnt ([|p, l, h, k|]) ->
    gotMsgStateEnt m l1 ([|p, l, h, k|]) ->
    (exists m' r, gotRangeStateEnt m' r ([|p', l', h', k'|])) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    l = l' /\
    gotRangeStateEnt m (mkDistance (dist2d l l1 -nn- speedMax *nn* msgLatency)) ([|p', l', h', k'|]).
  ```
  At `NARIncomp.v:138`, apply `mapGrng` with this canonical `r` (and `m''`) directly instead of `x1`. The
  `possiblyIncompatible` side-conditions then match `mapMsg`'s `r'` syntactically. Reachability is available there
  (`rn`, via `reachable_net_ent`). This is provable once (i) `reachableEnt` is concrete
  (BLOCKED-ON-STUB `reachableEnt`), so the other two components never output on `chanPos`, and (ii) the
  "expression-vs-value" bisimilarity lemma above exists. `gotMessage_next` should similarly be restricted to
  `a = chanPos ;? [basePosition l']` and conclude `gotRangeState m'' (mkDistance (dist2d l' l -nn- ...)) p'`.
- **Partial proof:** `gotMsg_gotRange_track_ent_indist` (in the `.v`, compiles).

## `gotRange_currPincCheck_track_ent`

- **Where:** `src/EntAuxResults.v` line 511 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `bisim-state-param-tracking` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Replace parameter equalities with a forward-tracking conclusion (gotRangeStateEnt m2 r e' \/ currPincCheckStateEnt (currModeMState k) m2 r e') under reachableProt p, as in the w1b-16 write-up.

- **Status:** FALSE (counterexample, checked in Rocq). It needs any `m : Mode` and nothing else.
- **Intent:** if an entity whose listener is in `gotRange m2 r` takes a step into a state whose listener is in `currPincCheck m1' m2' r'`, then the step was the read of the current mode from the mode state. So the parameters carry over (`m2 = m2'`, `r = r'`) and the mode read is the current one (`m1' = currModeMState k`).
- **Failure:** the state predicates are **bisimilarity classes** (`currPincCheckState m m'' d p := p ~p~ currPincCheck m m'' d`), and bisimilarity can't tell parameters apart once the guard decides the branch. `currPincCheck x y z = (!~bPossInc x y z $> currCompN[y,z]) $+$ (bPossInc x y z $> badOvlpN)`. When `bPossInc x y z` evaluates to true:
  - the left summand is a false-guarded conditional, which has no discrete steps and idles under delay (`stepTpIfFalse`);
  - the right summand behaves like its body.

  So `currPincCheck x y z ~p~ badOvlpN` for **every** triple with `possiblyIncompatible x y z`. Since `possIncDist m m' >= 2*speedMax*adaptNotif > 0`, every distance below that bound is possibly incompatible for every pair of modes.

  **Counterexample:**
  - `e = [| nilProc $||$ nilProc $||$ gotRange m r0, l, h, sing m |]` with `r0 = 0`, and `e'` the same with the listener replaced by its `chanMCurr ;? [baseMode m]` derivative `currPincCheckN $([m, m, r0])$`. The step is `stepDeCurrRead` with `stepMsOutCurrSing`.
  - `gotRangeStateEnt m r0 e` holds by reflexivity.
  - `currPincCheckStateEnt m m r1 e'` holds for `r1 = speedMax*adaptNotif` (`<> 0`), because both terms are bisimilar to `badOvlpN`.
  - The conclusion then forces `r0 = r1`, i.e. `0 = speedMax*adaptNotif`, which contradicts `speedMax_pos` and `adaptNotif_positive`.

  This is `gotRange_currPincCheck_track_ent_cex` in `EntAuxResults.gotRange_currPincCheck_track_ent.v`, which closes with `Qed` in --explore. `Print Assumptions` lists only model axioms (`speedMax_pos`, `adaptNotif_positive`, `period_positive`, …) plus the stdlib classical/funext/proof-irrelevance axioms. **No admitted lemma is used.** Adding reachability doesn't help: any reachable entity in `gotRange m'' r` with small `r` (`r` is a truncated `-nn-` subtraction, so `0` is typical) gives the same failure.
  - A second, independent failure appears once `p1`/`p2` are arbitrary. With no reachability hypothesis, `p1` may output `chanMCurr ;! [baseMode m']` and synchronise internally with the listener (`stepDeProcTau`), so even `m1' = currModeMState k` fails for parameter-sensitive cases.
- **Ripple-up:** not in the safety cone. Its only user is `NARIncomp.msgAbort_not_nextSince` (NARIncomp.v:162, case 2 "gotRange"), which needs only the fact `x1 = currModeMState k0`, and only to turn `~possiblyIncompatible (currModeMState k0) m'' r` into `currCompState m'' r p3'` via `currPincCheck_cond_false`.
- **Same defect in siblings (same argument, same helper lemma `..._guard_sum`):**
  - `gotMsg_gotRange_track_ent` (`m = m'`, and `r = …`): `gotRange m r ~p~ gotRange m' r'` whenever `r, r' < 2*speedMax*adaptNotif`.
  - `currComp_nextPincCheck_track_ent` (`m2 = m2' /\ r = r' /\ nextModeMState k = Some m1'`): `nextPincCheck` has the same `!~B $> _ $+$ B $> _` shape.

  Equalities of parameters can **never** be derived from bisimilarity-class state predicates. Only positive state facts can.
- **Suggested fix:** replace the parameter equalities with a forward-tracking conclusion that states the derivative's state with the expected parameters, and add protocol reachability to rule out internal synchronisation:
  ```coq
  Lemma gotRange_currPincCheck_track_ent (m2 : Mode) (r : Distance)
    (p p' : ProcTerm) (l l' : Position) h h' k k' a :
    reachableProt p ->
    gotRangeStateEnt m2 r ([|p, l, h, k|]) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    gotRangeStateEnt m2 r ([|p', l', h', k'|]) \/
    currPincCheckStateEnt (currModeMState k) m2 r ([|p', l', h', k'|]).
  ```
  - **Why it should be provable.** By inversion on the entity step and the parallel triple, either `p3' = p3`, which gives the left disjunct, or `p3` steps. In that case `gotRange m2 r`'s only steps are `chanMCurr ;? [v]` to `currPincCheckN $([v, m2, r])$`. The input either comes from the mode state (`stepDeCurrRead`, where both `stepMsOutCurrSing` and `stepMsOutCurrTrans` output `currModeMState k`), giving the right disjunct via `..._app_bisim`, or from an internal sync with `p1`/`p2`. The internal sync is excluded by a reachability invariant: in a reachable protocol the broadcast and overlap components only output on `chanMCurr` with the empty tuple (`switchCurr`, `tfsCurr`), and an arity mismatch blocks `stepDpIn`. That invariant can be proved by induction on `reachableProt` directly; it doesn't need the admitted, and probably over-strong, `reachableProt_triple`.
  - **Why it suffices for the user.** `msgAbort_not_nextSince` has `rn : reachableNet n`, so `reachable_net_prot` supplies `reachableProt`. In case 2, the left disjunct gives `mapGrng` directly, and the right disjunct gives `currPincCheck_cond_false H8` and then `mapCuco`. The detour through `gotRange_next` and the equalities is no longer needed.
- **Partial proof:** none for the stated lemma (it is false). The counterexample and reusable bisimulation helpers are in the HELPERS of `EntAuxResults.gotRange_currPincCheck_track_ent.v`: `_ifFalse_sum` (cofix), `_ifTrue`, `_guard_sum`, `_app_bisim` and `_pid`. They are demonstrations, not for splicing.

## `currComp_listening_track_ent`

- **Where:** `src/EntAuxResults.v` line 519 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `mode-chan-internal-sync` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Either restate to list every way currComp reaches listening (mode-state chanMStable read, chanMNext read with ~possiblyIncompatible, or internal chanMStable sync with the overlap) as in the w1b-01 write-up, or forbid internal sync on mode-state channels (definition change).

- **Status:** FALSE (counterexample). Two independent counterexamples, both checked in Rocq (`--explore`, rc=0) and closed under the model axioms plus stdlib axioms only, with no admitted lemmas. The second one is ordinary protocol behaviour, so adding `reachableEnt` would not rescue the statement.
- **Intent:** if the listener goes from `currComp m'' r` to `listening` in one entity step, then the step was the listener reading `chanMStable` from the mode state (RD-STBL). So the mode state was stable (`k -ms- chanMStable @! -ms> k'`) and the interface is unchanged.
- **Failure:** a listener in `currComp` can reach a state bisimilar to `listening` in two other ways. Neither involves the mode state outputting on `chanMStable`.
  1. **Internal sync with the overlap component** (`currComp_listening_track_ent_cex1`). The protocol's overlap states `tfsNext m` and `ovAbort` *output* on `chanMStable`; they are meant for WRITE-STBL, which aborts the mode state. The listener's `currComp` *inputs* on `chanMStable`. Inside `p1 $||$ p2 $||$ p3` these two synchronise to a process `tau` (`stepDpSyncLR`), and the entity takes `stepDeProcTau` with `k' = k`. Witness: `[| nilProc $||$ (chanMStable ! nilProc) $||$ currComp m'' r, l, h, <|m,m,zeroTime|> |] -EA- aeTau ->> [| nilProc $||$ nilProc $||$ listeningN, l, h, <|m,m,zeroTime|> |]`. A transitional mode state has no `chanMStable @!` step.
     This state also looks reachable. The listener goes badOvlp → `bad!` (the overlap moves to tfsStart → tfsNext) → listening → receives a message → gotMsg → gotRange → currPincCheck → currComp, while the overlap is still in tfsNext and the mode state is still transitional.
  2. **Reading the next mode when it is not possibly incompatible** (`currComp_listening_track_ent_cex2`). Take `k = <|m, m', t|>` and `~ possiblyIncompatible m' m'' r`, for example `r := possIncDist m' m''`. Then `currComp -chanMNext<m'>?->` gives `nextPincCheckN(m', m'', r)` via `stepDeNextRead` with `stepMsOutNext`, so `k' = k`. Because `bPossInc` evaluates to false, `nextPincCheck = (!~bPossInc $> listeningN) $+$ (bPossInc $> abortOvlpN)` is bisimilar to `listening`. The proof uses `cond_bisim_true`, `cond_bisim_false`, `choice_bisim_context` and `choice_bism_unit_r`. This is exactly the "conditional branch that evaluates to listening" that the ProtAuxDefs comment warns about. Again `k` cannot output `chanMStable`.
  The lemma `currComp_listening_track_ent_refuted` (from cex1) and the lemma `currComp_listening_track_ent_refuted2` (from cex2 with `r := possIncDist m m`) each prove `~ (statement)` for any `m : Mode`.
  The `h = h'` half *is* true: every way of reaching listening leaves the interface alone. Any step that leaves `p3` fixed would need `currComp ~ listening`, which fails because `listening` can do `chanPause *?`.
- **Ripple-up:** not in the safety cone. The only user is `NARIncomp.msgAbort_not_nextSince`, which is marked proved (sub-case 2 of the currComp case, NARIncomp.v:200). That proof currently rests on this false lemma.
  - The user has `possiblyIncompatible m' m'' r` and `nextModeMState k0 = Some m'`, so counterexample 2 is excluded there.
  - Counterexample 1 is not excluded. In that sub-case the overlap may sync on `chanMStable` and the listener ends in `listening` with `k0` unchanged, so the user's `false.` step cannot succeed.
  - The user's *statement* is probably still true. The overlap moved from tfsNext to tfsNext, or from ovAbort to dormant, so `~nextSinceStateNet i n'` (the right disjunct) should hold given reachability. Its proof must take the right disjunct in that sub-case instead of deriving a contradiction.
- **Suggested fix:** either of the following.
  (a) Correct the statement so that it lists every way the step can happen:
  ```coq
  Lemma currComp_listening_track_ent m'' r l l' p1 p2 p3 p' h h' k k' a :
    currCompStateEnt m'' r ([|p1 $||$ p2 $||$ p3, l, h, k|]) ->
    listeningStateEnt ([|p', l', h', k'|]) ->
    [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    h = h' /\
    ( k -ms- chanMStable @! -ms> k'
    \/ (exists m', k -ms- chanMNext .! m' -ms> k' /\ ~ possiblyIncompatible m' m'' r)
    \/ (k = k' /\ exists p1' p2' p3', p' = p1' $||$ p2' $||$ p3' /\
          p1 $||$ p2 -PA- chanMStable *! -PA> p1' $||$ p2') ).
  ```
  This should be provable without reachability by the case analysis above. The ingredients are `currComp ≁ listening`, `nextPincCheck` with possInc true `≁ listening` (it is `~ abortOvlp`, which only does `chanAbort!`), and bisimulation transfer of `p3`'s step to `currComp`.
  For the user: disjunct 1 contradicts `unstable k0`, as now. Disjunct 2 forces `m'` to be the next mode and contradicts `possiblyIncompatible m' m'' r`. Disjunct 3 needs a small reachable-overlap lemma: an overlap state that outputs on `chanMStable` is tfsNext or ovAbort, so its derivative is not `nextSinceState`. That proves the right disjunct of `msgAbort_not_nextSince`.
  (b) Alternatively, change the definition. Give WRITE-STBL its own channel (overlap `chanMAbort!` against a mode-state `chanMAbort?`, plus the missing entity rule; the Rocq `stepDiscEnt` currently has RD-STBL but no WRITE-STBL rule), so that the overlap and listener cannot synchronise. Then add `nextModeMState k = Some m' -> possiblyIncompatible m' m'' r` as a hypothesis, or the second disjunct above. This is a model change and needs owner approval. The same overlap/listener `chanStable` sync is present in the thesis (§4, tfsNext/ovAbort `chanStable!` against currOK/currComp `chanStable?`).
- **Partial proof:** `EntAuxResults.currComp_listening_track_ent.v` (in the prover work area, not committed; the audited copy is under [`../evidence/audit/`](../evidence/audit/)) holds both counterexamples, the two refutations, and the helpers `..._app_bisim` and `..._listeningN : listeningState listeningN`. The helpers can be reused for other `#fwd-track` and listening lemmas.

## `currComp_nextPincCheck_track_ent`

- **Where:** `src/EntAuxResults.v` line 526 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `mode-chan-internal-sync` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Forbid process-internal synchronisation on chanMNext/chanMCurr/chanMStable (definition change) and restate as in the w1b-05 write-up (premise nextModeMState k = Some m1, conclusion currComp unchanged \/ (nextPincCheckStateEnt m1 m2 r e' /\ k' = k)).

- **Status:** FALSE (counterexample, machine-checked). **The statement implies `Mode -> False`**, so it belongs on the known-inconsistent list next to `nextModeEnt_not_stable` etc.
- **Intent:** if the listener goes from `currComp m2 r` to `nextPincCheck m1' m2' r'` in one entity step, then the step was the listener reading the next mode `m1'` from the mode state over `chanMNext`. So the parameters carry over (`m2 = m2'`, `r = r'`) and the mode state is unstable with next mode `m1'`.
- **Failure (main, verified):** the process semantics (`stepDpSyncLR/RL`, SoftwareLanguage.v) lets *any* two parallel components synchronise on *any* channel, mode-state channels included. The overlap state `tfsNext m` outputs `chanMNext<eFailSafeSucc m>!`, and `currComp`'s `chanMNext<vM'>?` input can synchronise with that output *inside the process*. The result is a process `tau`, lifted by `stepDeProcTau`, which never consults the mode state. The listener then holds `nextPincCheck m1' ..` while `k` can be anything, e.g. a stable `sing m0` with `nextModeMState k = None`.
  Concrete counterexample (any `m0 : Mode`, `r : Distance`, `l`, `h`):
  `p  = nilProc $||$ (outPrefix chanMNext [eBase m0] nilProc) $||$ currComp m0 r`,
  `p' = nilProc $||$ nilProc $||$ app nextPincCheckN [m0, m0, r]`, `k = k' = sing m0`, `a = aeTau`.
  `currCompStateEnt m0 r [|p,l,h,k|]` holds by `bisim_refl`. `nextPincCheckStateEnt m0 m0 r [|p',l,h,k|]` holds by unfolding the `app` (helper `ccnp_app_bisim`). The step is `stepDeProcTau` over `stepDpParR (stepDpSyncLR ...)`. The conclusion requires `None = Some m0`.
  In `EntAuxResults.currComp_nextPincCheck_track_ent.v` (HELPERS, compiles under `--explore` at the target's position, using no admitted lemmas):
  - `ccnp_counterexample : (statement) -> forall m0 r l h, False`
  - `ccnp_inconsistent : (statement) -> Mode -> False`
  This is not a quirk of a junk, unreachable state. In the real protocol the overlap's `tfsNext` (or `ovAbort`'s `chanMStable!`) can coexist with the listener's `currComp`/`currOK`, so the listener can "read" the overlap's *proposed* fail-safe mode instead of the mode state's. The thesis has the same unrestricted SYNC-LR/RL rules (thesis ~l.3659–3718).
- **Second, independent problem (argued, not machine-checked):** state predicates are bisimulation classes, and `nextPincCheck m1 m2 r` is a pair of guarded branches. Whenever `possIncBool m1 m2 r = false`, it is bisimilar to `listening`. Take `r'` with `r' >= possIncDist m1' m2'` (it is an arbitrary `Distance`). Then the *honest* step `currComp m2 r --chanMStable *?--> listening` via `stepDeRdStbl`, with a stable `k`, also satisfies both hypotheses. It refutes the conclusion (`nextModeMState k = None`) and `r = r'`. So even with the semantics repaired, the conclusion cannot recover the parameters of the target state from a bisimulation-class hypothesis. Only the parameters *produced by the step* can be concluded.
- **Ripple-up:** not in the safety cone. The only user is `NARIncomp.msgAbort_not_nextSince` (NARIncomp.v:188, case 3 "currComp"). That proof ends in `Qed`, so it currently rests on an inconsistent assumption. Its user is the `incomp_*` chain at NARIncomp.v:280 (also outside the cone). The sibling targets `currComp_listening_track_ent` (internal `chanMStable` sync with `tfsNext`/`ovAbort`, with `k` unstable, refutes its `k -ms- chanMStable @! -ms> k'`) and the `currOK`/`nextEq` analogues have the same internal-sync hole. `gotRange_currPincCheck_track_ent` does not, because `chanMCurr` outputs carry `[]` and `chanMCurr<vM>?` inputs carry 1 value, so `stepDpIn`'s length check blocks a sync.
- **Suggested fix:**
  1. *Definition change (needed for any version of the lemma):* forbid process-internal synchronisation on the mode-state channels, which the thesis's architecture clearly intends to be point-to-point with the mode state. E.g. in `SoftwareLanguage.v`:
     ```coq
     Definition modeStateChan (c : Channel) : Prop :=
       c = chanMStable \/ c = chanMCurr \/ c = chanMNext.
     (* add the premise ~ modeStateChan c to stepDpSyncLR and stepDpSyncRL *)
     ```
     (The `sort`/`noSync` machinery used for delays should get the same side condition.)
  2. *Restated lemma,* concluding only what the step determines, and in the form `msgAbort_not_nextSince` actually uses (it needs: listener moved out of `currComp`, `nextModeMState k0 = Some m'`, so the listener is now in `nextPincCheck m' m'' r`):
     ```coq
     Lemma currComp_nextPincCheck_track_ent (m2 m1 : Mode) (r : Distance)
       (l l' : Position) (p p' : ProcTerm) h h' k k' a :
       currCompStateEnt m2 r ([|p, l, h, k|]) -> nextModeMState k = Some m1 ->
       [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
       currCompStateEnt m2 r ([|p', l', h', k'|]) \/
       (nextPincCheckStateEnt m1 m2 r ([|p', l', h', k'|]) /\ k' = k).
     ```
     Proof idea once fix 1 is in place. If the listener component moves, then by bisimilarity with `currComp m2 r` its action is `chanMStable *?` or `chanMNext ;? [m]`, lifted unchanged to the top level, because syncs on these channels are now forbidden. The only entity rules with these process actions are `stepDeRdStbl`, impossible because `k` is unstable and `chanMStable @!` needs a stable state, and `stepDeNextRead`, where `stepMsOutNext` forces `k = <_, m, _> = k'`, so `m = m1`. The derivative is `app nextPincCheckN [m1, m2, r]`, which is bisimilar to `nextPincCheck m1 m2 r` (helper `ccnp_app_bisim` plus the substitution computation, both already checked in the helper file). In `msgAbort_not_nextSince` case 3 the `mapCuco` hypotheses give exactly `nextModeMState k0 = Some m'` and `possiblyIncompatible m' m'' r`. Then `nextPincCheck_cond_true` gives `abortOvlp`, so `mapAbort` applies, as the current script already intends.
- **Partial proof:** none of the target (it is false). See HELPERS of `EntAuxResults.currComp_nextPincCheck_track_ent.v` for the checked refutation and for `ccnp_app_bisim : def n = (l1, q) -> bisimulation (app n l) (subProcTerm (listsToSub l1 l) q)` (reusable) and `ccnp_varEq_tac` (computes `update`/`varEq` substitutions).

## `ovReady_ovWait_track_ent`

- **Where:** `src/EntAuxResults.v` line 534 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE (counterexample, Rocq-checked with no admitted dependencies). It also NEEDS-HYPOTHESIS: a reachability hypothesis.
- **Intent:** This is the entity-level tracking result for the overlap transition ovReady -> ovWait. If an entity whose overlap component is in `ovReady m t l0` takes a discrete step to an entity whose overlap component is in `ovWait m' ...`, then the step was the software outputting `[m, l0]` on `chanOutProc` to its own interface (`stepDeIOProcInter`), the mode state is untouched, `m = m'`, and the broadcast position `l0` is the entity's own position `l`.
- **Failure:** The statement has no reachability hypothesis. `ovReadyStateEnt`/`ovWaitStateEnt` are `liftProcEnt (liftOverlap ...)`, so they constrain only the middle parallel component of `p`. Both the entity position `l` and the other two components are arbitrary. Two independent counterexamples are checked in `--explore` (rc=0) in `EntAuxResults.ovReady_ovWait_track_ent.v`. `Print Assumptions` on each lists only the ComhBasics model parameters plus the stdlib's classical-reals, functional-extensionality and proof-irrelevance axioms. No admitted lemma is used.
  1. **`l = l0` fails** (`ovReady_ovWait_track_ent_false : forall m0 : Mode, ~ <statement>`). Fix any `m0 : Mode` and take
     - `p  := nilProc $||$ ovReady m0 (period m0) (mkPosition 0 0) $||$ nilProc`, at position `l := mkPosition 1 0`;
     - `p' := nilProc $||$ ovWaitN $([m0, period m0 (-) ePeriod m0, ePeriod m0])$ $||$ nilProc` (the literal ovReady continuation);
     - `h` with empty lists, `h'` with `<([m0, (0,0)], msgLatency)>` buffered in the output list, and `k = k' = sing m0`;
     - the step `stepDeIOProcInter` (ParR/ParL/`stepDpOut` + `stepIntBuffOut`/`stepOlBuff`).

     The ovWait premise holds with `t' = x' = mkTime (period m0 -nn- period m0)` and `y' = period m0`. The statement then yields `mkPosition 1 0 = mkPosition 0 0`, which `lra` refutes. Discrete entity steps never move the entity, and nothing ties `l0` to `l` except the history: `ovReady` is entered via `chanPos` (`stepDePosRead`) and left before any delay. That is an invariant of *reachable* entities only.
  2. **The process/interface conjuncts fail too, even with `l = l0`** (`ovReady_ovWait_track_ent_false2`, which refutes the weaker statement with only the first conjunct). Make the third component `inPrefix chanOutProc [vM'', vL'] nilProc`. The ovReady output then synchronises internally (`stepDpSyncLR`), the entity step is `stepDeProcTau` with `h' = h`, and `p` has no `chanOutProc ;! [m0, l0]` step to `p'`. Inversion refutes it.
  - The non-trivial ingredient in both is the premise `ovWaitState m0 t' t' (period m0) (ovWaitN $([m0, t (-) ePeriod m0, ePeriod m0])$)`. It is proved by a small "bisimulation up to evaluation of time expressions" (`..._R`, `..._R_disc`, `..._R_timed`, `..._R_sym`, `CoFixpoint ..._bisim`). It relates `app` terms to their unfoldings and ovWait/ovReady bodies whose time arguments evaluate (via `evalBaseNonnegFun ∘ evalExpFun`) to the same nonneg real.
- **Ripple-up:** Not in the safety cone. Its only users are inside **commented-out** proofs of two admitted `(*R*)` theorems: `NARMsgPosition.fst_sent` (NARMsgPosition.v:90) and `NARTop.ovWait_sent` (NARTop.v:140). Both live in a `reachableNet n` context. Both use only the process-step and interface-step conjuncts (to build `sentBase`), plus `k = k'`/`m = m'` through `subst`. The `exists l` in their conclusions does not need `l = l0`. Nothing compiled breaks if the statement is changed.
- **Suggested fix:** add a reachability hypothesis. Two variants:
  - (a) **Preferred, stub-free.** Drop `l = l0` and assume protocol reachability, which the callers get from `NetAuxBasics.reachable_net_prot`:
    ```coq
    Lemma ovReady_ovWait_track_ent m m' t t' x' y' l0 a p p' l l' h h' k k' :
      reachableProt p ->
      ovReadyStateEnt m t l0 ([|p, l, h, k|]) ->
      ovWaitStateEnt m' t' x' y' ([|p', l', h', k'|]) ->
      [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
      p -PA- chanOutProc ;! [baseMode m, basePosition l0] -PA> p' /\
      h -i- chanOutProc {? [baseMode m, basePosition l0] -i> h' /\
      k = k' /\ m = m'.
    ```
    Proof plan (believed provable relative to the existing admitted ProtAuxResults lemmas):
    1. `reachableProt_triple` gives `p = p1 $||$ p2 $||$ p3` with broadcast/overlap/listener states, and `p2` is the ovReady component.
    2. Invert the entity step. The four steps that leave `p` unchanged make `p2` bisimilar to both ovReady and ovWait, which `state_pred_elim` / `bisim_contra` refute.
    3. Every other step is a process step. Decompose the parallel step. `p1`/`p3`-only steps leave `p2` unchanged (same contradiction).
    4. A `p2` step lands in ovWait. `ProtAuxResults.ovWait_prev` (Qed) gives the action `chanOutProc ;! [m', l']` with `ovReadyState m' _ l' p2`, and bisimilarity with `ovReady m t l0` forces `m' = m` and `l' = l0`.
    5. Synchronisation with `p1`/`p3` would need a broadcast or listener input on `chanOutProc`, which is impossible (cf. `prot_outProc_in_not`).
    6. So the top-level action is `chanOutProc ;! [m, l0]`. The only entity rule with that process action is `stepDeIOProcInter`, which gives the interface step and `k = k'`.
  - (b) **Keeping `l = l0`.** Add `reachableEnt ([|p, l, h, k|])` instead. `l = l0` then follows from `ovReady_pos` (admitted, D- reachableEnt) together with a completed `inPosEnt` stub (`inPosEnt l [|_, l', _, _|] <-> l = l'`). This variant is therefore BLOCKED-ON-STUB (`reachableEnt`, `inPosEnt`) until those are defined. The other conjuncts follow as in (a) via `reachable_ent_prot`.
- **Related observation:** the sibling `*_track_ent` lemmas just above (`gotMsg_gotRange_track_ent`, `gotRange_currPincCheck_track_ent`, `currComp_listening_track_ent`, `currComp_nextPincCheck_track_ent`) also lack reachability hypotheses. They are very likely refutable the same way, because an arbitrary sibling component can synchronise on `chanPos` / `chanMCurr` / `chanMStable` / `chanMNext` instead of the mode state or the position read. This was not checked here.
- **Partial proof:** none of the target. The `.v` file holds the two Rocq-checked refutations. Its bisimulation helpers (`..._R*`, `..._bisim`) also prove the ovWait half of the admitted `ProtAuxResults.ovlp_outProc_out` for the concrete ovReady continuation, and can be reused there.
