From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.NetAuxBasics.

(* ===== helpers copied verbatim from work/w1b-08/NetAuxBasics.switch_states_mState.cex.v ===== *)

(* VALIDATION ONLY (explore mode). These helpers are not meant to be spliced:
   the target is BLOCKED-ON-STUB, see NetAuxBasics.switch_states_mState.fail.md.
   They show that even under the intended stub definitions the statement is
   false without a reachability hypothesis, as soon as Mode has two distinct
   elements. *)
Require Import ComhCoq.ProcEquiv.
From Stdlib Require Import Reals.

(* Intended definitions of the two stubs (local copies). *)
Definition switch_states_mState_currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
  exists e, e @ i .: n /\ currModeEnt e = m.
Definition switch_states_mState_nextModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
  exists e, e @ i .: n /\ nextModeMState (mstEnt e) = Some m.

(* The target statement with the intended definitions substituted. *)
Definition switch_states_mState_stmt : Prop :=
  forall (n n' : Network) (i : nat) (a : ActDiscNet) (m : Mode),
  n -NA- a -NA> n' -> switchCurrStateNet i n ->
  switchListenStateNet i n' -> switch_states_mState_nextModeNet m i n ->
  switch_states_mState_currModeNet m i n'.

(* Unfolding the name switchListenN is a bisimulation. *)
Lemma switch_states_mState_app_switchListen :
  (app switchListenN []) ~p~ switchListen.
Proof.
  constructor.
  - intros a p' H. exists p'. split; [ | apply bisim_refl].
    inversion H; subst;
    match goal with
    | [HD : stepDiscProc _ _ _ |- _] => inversion HD; subst
    | [HT : stepTimedProc _ _ _ |- _] => inversion HT; subst
    end;
    match goal with [DEF : def _ = (_, _) |- _] =>
      simpl in DEF; inversion DEF; subst end;
    constructor; simpl in *; assumption.
  - intros a q' H. exists q'. split; [ | apply bisim_refl].
    inversion H; subst.
    + constructor. eapply stepDpApp; [reflexivity | simpl; assumption].
    + constructor. eapply stepTpApp; [reflexivity | simpl; assumption].
Qed.

(* Counterexample: a non-reachable entity whose broadcast slot is the process
   chanMCurr?nil. It synchronises with the overlap's output chanMCurr! so the
   entity takes a plain tau step (stepDeProcTau) that leaves the mode state
   <|m0, m, 0|> untouched. switchCurr -> switchListen happens, the next mode is
   m, but the current mode afterwards is still m0. *)
Lemma switch_states_mState_cex :
  switch_states_mState_stmt -> forall m0 m : Mode, m0 = m.
Proof.
  intros H m0 m.
  set (l := mkPosition 0%R 0%R).
  set (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (p1 := inPrefix chanMCurr [] nilProc).
  set (p := p1 $||$ switchCurr $||$ nilProc).
  set (p' := nilProc $||$ (app switchListenN []) $||$ nilProc).
  set (k := <| m0, m, zeroTime |>).
  set (e := [| p, l, h, k |]).
  set (e' := [| p', l, h, k |]).
  assert (STP : p -PA- tauAct -PA> p').
  { unfold p, p'. eapply stepDpSyncRL.
    - unfold p1. apply (stepDpIn chanMCurr [] [] nilProc). reflexivity.
    - apply stepDpParL. apply stepDpOut. constructor. }
  assert (NSTEP : [e] -NA- anTau -NA> [e']).
  { apply stepDnTauHead. unfold e, e'. apply stepDeProcTau. exact STP. }
  assert (SC : switchCurrStateNet 0 [e]).
  { eapply lenWitness; [ | apply einConsLeft]. unfold e.
    apply lifpe. unfold p. apply lftOv. unfold switchCurrState. apply bisim_refl. }
  assert (SL : switchListenStateNet 0 [e']).
  { eapply lenWitness; [ | apply einConsLeft]. unfold e'.
    apply lifpe. unfold p'. apply lftOv. unfold switchListenState.
    apply switch_states_mState_app_switchListen. }
  assert (NM : switch_states_mState_nextModeNet m 0 [e]).
  { exists e. split; [apply einConsLeft | reflexivity]. }
  destruct (H _ _ _ _ _ NSTEP SC SL NM) as [e'' [IN CM]].
  assert (e'' = e') as EQ by (eapply entInNetUnique; [exact IN | apply einConsLeft]).
  subst e''. exact CM.
Qed.

(* ===== audit wrapper ===== *)
Print Assumptions switch_states_mState_cex.
