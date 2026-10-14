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

(* ===== helpers copied verbatim from work/w1b-05/NetAuxBasics.ovWait_prev_net.v ===== *)

(* VALIDATION ONLY (explore mode): counterexample adapted from w1b-08's
   NetAuxBasics.ovWait_prev_net_strong.cex.v to this target's exact statement. *)
Require Import ComhCoq.ProcEquiv.
From Stdlib Require Import Reals.

Lemma ovWpn_slot (X : ProcTerm -> Prop) p1 q p3 l h k :
  liftEntNet (liftProcEnt (liftOverlap X)) 0 [ [|p1 $||$ q $||$ p3, l, h, k|] ] -> X q.
Proof.
  intros H. destruct H as [e0 HX HIN].
  assert (e0 = [|p1 $||$ q $||$ p3, l, h, k|]) as EQ
    by (eapply entInNetUnique; [exact HIN | apply einConsLeft]).
  subst e0. inversion HX; subst.
  match goal with [H0 : liftOverlap X _ |- _] => inversion H0; subst end.
  assumption.
Qed.

Ltac ovWpn_inv :=
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
Lemma ovWpn_cex (m : Mode) (t x y : Time) :
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
      apply ovWpn_slot in H. unfold ovWaitState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold ovWait in H end.
      ovWpn_inv.
    + destruct H as [t0 [l0 H]].
      unfold ovReadyStateNet, ovReadyStateEnt, ovReadyStateProt in H.
      apply ovWpn_slot in H. unfold ovReadyState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold ovReady in H end.
      ovWpn_inv.
    + unfold initStateNet, initStateEnt, initStateProt in H.
      apply ovWpn_slot in H. unfold initState in H.
      destruct H as [F B]. destruct (F _ _ QS) as [r [RS _]].
      inversion RS; subst.
      match goal with [H : stepDiscProc _ _ _ |- _] => unfold init in H end.
      ovWpn_inv.
Qed.

(* The target statement forces Mode to be empty. *)
Lemma ovWpn_refuted :
  (forall m t x y i n n' a, ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
   ovWaitStateNet m t x y i n \/
   (exists l, ovReadyStateNet m (t +t+ period m) l i n) \/
   initStateNet m i n) ->
  Mode -> False.
Proof.
  intros S m.
  destruct (ovWpn_cex m zeroTime zeroTime zeroTime)
    as [n [n' [a [A [B C]]]]].
  apply C. destruct (S _ _ _ _ _ _ _ _ A B) as [H | [[l H] | H]].
  - left; exact H.
  - right; left; do 2 eexists; exact H.
  - right; right; exact H.
Qed.


(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.ovWait_prev_net in exact T).
Lemma audit_ovWait_prev_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (ovWpn_refuted H m).
Qed.
Print Assumptions audit_ovWait_prev_net.
