From Stdlib Require Import Program.Equality.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs. 
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults. 
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.NARMisc.

(* ===== audit evidence ===== *)

Lemma rangeBad_notifBad_net_fixed m i n :
  rangeBadStateNet m i n -> currModeNet m i n -> notifBadPathNet i n.
Proof.
  intros R C. destruct R as [e E1 E2]. apply currMode_ent_ex in C.
  destruct C as [e' [E2' CM]].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  inversion E1 as [p l h k P]; subst.
  econstructor; [ | apply E2]. eapply nbpRng. exact P. reflexivity.
Qed.


Print Assumptions rangeBad_notifBad_net_fixed.
