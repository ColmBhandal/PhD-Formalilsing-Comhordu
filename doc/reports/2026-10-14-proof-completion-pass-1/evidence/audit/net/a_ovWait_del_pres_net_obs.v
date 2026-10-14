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

(* ===== helpers copied verbatim from work/w1b-06/NetAuxBasics.ovWait_del_pres_net.v ===== *)

(* The x (pause timeout) parameter of ovWait is observable: with x = 0 the process
   can output on chanPause immediately; with any x <> 0 it cannot. *)
Lemma ovWait_del_pres_net_x_obs (m : Mode) (t x' y y' : Time) :
  x' <> zeroTime ->
  ~ ProcEquiv.bisimulation (ovWait m t zeroTime y) (ovWait m t x' y').
Proof.
  intros NZ B.
  assert (S : exists q, stepProc (ovWait m t zeroTime y) (actDisc (chanPause *!)) q).
  { eexists. apply stepPDisc. unfold ovWait. apply stepDpChoiceR.
    apply stepDpTimeOut; [ | reflexivity ]. constructor. constructor. }
  destruct S as [q S]. inversion B as [F G]. apply F in S.
  destruct S as [q' [S _]]. inversion S; subst. clear S.
  match goal with H : stepDiscProc _ _ _ |- _ => rename H into D end.
  unfold ovWait in D.
  inversion D; subst; clear D.
  - match goal with H : stepDiscProc _ _ _ |- _ => inversion H; subst; clear H end;
    match goal with H : stepDiscProc _ _ _ |- _ => inversion H; subst; clear H end;
    try match goal with H : stepDiscProc _ _ _ |- _ => inversion H; subst; clear H end.
  - match goal with H : stepDiscProc _ _ _ |- _ => inversion H; subst; clear H end.
    match goal with H : evalExpFunTime _ = Some zeroTime |- _ => rename H into E end.
    destruct x' as [n]. unfold evalExpFunTime in E. simpl in E.
    inversion E; subst. apply NZ. reflexivity.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions ovWait_del_pres_net_x_obs.
