Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProcEquiv.
Require Import ComhCoq.ProtAuxResults.

(* ===== audit evidence ===== *)

Ltac paused_switch_inv :=
  repeat match goal with
   | [H : sum _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : del _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : ifThen _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
  end.

Ltac paused_switch_noact S T :=
  let q := fresh "q" in let T' := fresh "T" in
  red in S; destruct (bisim_disc_match _ _ _ _ S T) as [q T'];
  match type of T' with ?X -PA- _ -PA> _ =>
    let X' := eval red in X in change X with X' in T' end;
  paused_switch_inv.
(** An application process is bisimilar to its (substituted) body. *)
Lemma paused_switch_app n l1 l2 p :
  def n = (l1, p) -> app n l2 ~p~ subProcTerm (listsToSub l1 l2) p.
Proof.
  intros D. constructor.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst.
    + apply stepPDisc. match goal with [S0 : app _ _ -PA- _ -PA> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
    + apply stepPTimed. match goal with [S0 : app _ _ -PD- _ -PD> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst; [apply stepPDisc; eapply stepDpApp |
      apply stepPTimed; eapply stepTpApp]; eassumption.
Qed.

Lemma paused_switch_pausedN : pausedN ~p~ paused.
Proof.
  eapply bisim_trans; [apply (paused_switch_app pausedN [] [] paused); reflexivity | ].
  change (listsToSub [] []) with idSubst. rewrite subProc_id_eq. apply bisim_refl.
Qed.

(** The protocol process can input on chanPause in isolation (no synchronisation
  is required by the process semantics), reaching a state whose listener is paused
  while its overlap component is still dormant. *)
Lemma paused_switch_reach :
  reachableProt (sleeping $||$ dormant $||$ pausedN).
Proof.
  eapply reachprDisc; [apply reachprBase | ].
  unfold procProtocol. apply stepDpParR. apply stepDpParR.
  unfold listening. apply stepDpChoiceL. apply stepDpChoiceR.
  instantiate (1 := chanPause *?). apply stepDpIn. reflexivity.
Qed.

Lemma paused_switch_cex :
  reachableProt (sleeping $||$ dormant $||$ pausedN) /\
  pausedStateProt (sleeping $||$ dormant $||$ pausedN) /\
  ~ switchStateProt (sleeping $||$ dormant $||$ pausedN).
Proof.
  split; [apply paused_switch_reach | split].
  - constructor. apply paused_switch_pausedN.
  - intro H. inversion H; subst.
    assert (T : exists q, dormant -PA- chanAbort *? -PA> q).
    { eexists. unfold dormant. apply stepDpChoiceL. apply stepDpChoiceR.
      apply stepDpIn. reflexivity. }
    destruct T as [q T].
    match goal with [S0 : switchState _ |- _] =>
      destruct S0 as [m S | S | S] end;
    paused_switch_noact S T.
Qed.

Lemma paused_switch_refuted :
  ~ (forall p, reachableProt p -> (pausedStateProt p <-> switchStateProt p)).
Proof.
  intro F. destruct paused_switch_cex as [R [P N]].
  apply N. apply (F _ R). exact P.
Qed.


Print Assumptions paused_switch_refuted.
