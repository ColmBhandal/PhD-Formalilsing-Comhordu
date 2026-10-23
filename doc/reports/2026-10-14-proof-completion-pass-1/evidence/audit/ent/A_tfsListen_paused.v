Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxResults.

(* Copied from w1b-10/EntAuxResults.tfsListen_paused.cex.v (same as EntAuxResults-2). *)
Lemma tfsListen_paused_cex :
  ~ (forall p1 p2 p3, tfsListenStateProt (p1 $||$ p2 $||$ p3) ->
     pausedStateProt (p1 $||$ p2 $||$ p3)).
Proof.
  intro H. specialize (H nilProc tfsListen nilProc).
  assert (T : tfsListenStateProt (nilProc $||$ tfsListen $||$ nilProc)).
  { constructor. unfold tfsListenState. apply ProcEquiv.bisim_refl. }
  apply H in T. inversion T as [q1 q2 q3 B]; subst.
  assert (PP : pausedState paused) by (unfold pausedState; apply ProcEquiv.bisim_refl).
  apply paused_unpause_in in PP.
  unfold pausedState in B. apply ProcEquiv.bisim_symm in B.
  assert (DA : discActEnabled nilProc (chanUnpause *?)) by (eapply bisim_dae; eassumption).
  inversion DA as [q STEP]. inversion STEP.
Qed.

(* Direct form: the admitted lemma itself yields False (no Mode needed). *)
Lemma audit_tfsListen_paused_False : False.
Proof. exact (tfsListen_paused_cex tfsListen_paused). Qed.

Lemma tfsListen_paused_reach_contra p :
  reachableProt p -> tfsListenStateProt p -> pausedStateProt p -> False.
Proof.
  intros R T P. apply (paused_switch p R) in P.
  inversion T as [p1 p2 p3 TL]; subst.
  inversion P as [q1 q2 q3 SW EQ].
  apply tfsListen_abort_in in TL.
  inversion SW as [m S | S | S];
  [unfold switchBcState in S | unfold switchCurrState in S | unfold switchListenState in S];
  lets DA : bisim_dae S TL; inversion DA as [q STEP]; inversion STEP; subst.
Qed.

Print Assumptions tfsListen_paused_cex.
Print Assumptions audit_tfsListen_paused_False.
Print Assumptions tfsListen_paused_reach_contra.
