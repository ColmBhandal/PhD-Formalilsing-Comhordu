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

(* ===== helpers copied verbatim from work/w1b-08/NetAuxBasics.ovWait_prev_net_strong.cex.v ===== *)

(* VALIDATION ONLY (explore mode): a counterexample showing the target is false
   as stated (no reachability hypothesis). See
   NetAuxBasics.ovWait_prev_net_strong.fail.md. *)
Require Import ComhCoq.ProcEquiv.
From Stdlib Require Import Reals.

Lemma ovWait_prev_net_strong_slot (X : ProcTerm -> Prop) p1 q p3 l h k :
  liftEntNet (liftProcEnt (liftOverlap X)) 0 [ [|p1 $||$ q $||$ p3, l, h, k|] ] -> X q.
Proof.
  intros H. destruct H as [e0 HX HIN].
  assert (e0 = [|p1 $||$ q $||$ p3, l, h, k|]) as EQ
    by (eapply entInNetUnique; [exact HIN | apply einConsLeft]).
  subst e0. inversion HX; subst.
  match goal with [H0 : liftOverlap X _ |- _] => inversion H0; subst end.
  assumption.
Qed.

Ltac ovWait_prev_net_strong_inv :=
  repeat match goal with
  | [H : stepDiscProc (sum _ _) _ _ |- _] => inversion H; subst; clear H
  | [H : stepDiscProc (inPrefix _ _ _) _ _ |- _] => inversion H; subst; clear H
  | [H : stepDiscProc (outPrefix _ _ _) _ _ |- _] => inversion H; subst; clear H
  | [H : stepDiscProc (del _ _) _ _ |- _] => inversion H; subst; clear H
  end.

(* A non-reachable entity whose overlap slot is chanMCurr!ovWait(m,t,x,y) and
   whose broadcast slot is chanMCurr?nil. They synchronise (tau), and the
   overlap becomes ovWait(m,t,x,y), but beforehand it was neither ovWait,
   ovReady nor init. *)
Lemma ovWait_prev_net_strong_cex (m : Mode) (t x y : Time) :
  exists n n' a, ovWaitStateNet m t x y 0 n' /\ n -NA- a -NA> n' /\
  ~ (ovWaitStateNet m t x y 0 n \/ (exists t0 l0, ovReadyStateNet m t0 l0 0 n) \/
     initStateNet m 0 n).
Proof.
  set (l := mkPosition 0%R 0%R).
  set (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (q := outPrefix chanMCurr [] (ovWait m t x y)).
  set (p := (inPrefix chanMCurr [] nilProc) $||$ q $||$ nilProc).
  set (p' := nilProc $||$ (ovWait m t x y) $||$ nilProc).
  exists [ [|p, l, h, sing m|] ] [ [|p', l, h, sing m|] ] anTau.
  assert (QS : q -P- (outAct chanMCurr []) -P> ovWait m t x y).
  { constructor. unfold q. apply stepDpOut. constructor. }
  split; [ | split].
  - eapply lenWitness; [ | apply einConsLeft]. apply lifpe. unfold p'.
    apply lftOv. unfold ovWaitState. apply bisim_refl.
  - apply stepDnTauHead. apply stepDeProcTau. unfold p, p'. eapply stepDpSyncRL.
    + apply (stepDpIn chanMCurr [] [] nilProc). reflexivity.
    + apply stepDpParL. unfold q. apply stepDpOut. constructor.
  - intros [H | [H | H]].
    + unfold ovWaitStateNet, ovWaitStateEnt, ovWaitStateProt in H.
      apply ovWait_prev_net_strong_slot in H. unfold ovWaitState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold ovWait in H end.
      ovWait_prev_net_strong_inv.
    + destruct H as [t0 [l0 H]].
      unfold ovReadyStateNet, ovReadyStateEnt, ovReadyStateProt in H.
      apply ovWait_prev_net_strong_slot in H. unfold ovReadyState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold ovReady in H end.
      ovWait_prev_net_strong_inv.
    + unfold initStateNet, initStateEnt, initStateProt in H.
      apply ovWait_prev_net_strong_slot in H. unfold initState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold init in H end.
      ovWait_prev_net_strong_inv.
Qed.

(* The target statement refutes itself as soon as Mode is inhabited. *)
Lemma ovWait_prev_net_strong_refuted :
  (forall m t x y n n' i a, ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
   ovWaitStateNet m t x y i n \/ (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
   initStateNet m i n) ->
  Mode -> False.
Proof.
  intros S m.
  destruct (ovWait_prev_net_strong_cex m zeroTime zeroTime zeroTime)
    as [n [n' [a [A [B C]]]]].
  apply C. eapply S; eassumption.
Qed.


(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.ovWait_prev_net_strong in exact T).
Lemma audit_ovWait_prev_net_strong : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (ovWait_prev_net_strong_refuted H m).
Qed.
Print Assumptions audit_ovWait_prev_net_strong.
