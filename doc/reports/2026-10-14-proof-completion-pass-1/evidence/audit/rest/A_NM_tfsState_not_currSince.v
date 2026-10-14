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

(* Proposed fix: add ~ failSafe m. Proved relative to existing lemmas. *)
Lemma tfsState_not_currSince_fixed (m : Mode) (t : Time) (i : nat) (n n' : Network)
  (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
  ~ failSafe m ->
  tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
Proof.
  intros NFS TS NTS CS. apply NTS.
  eapply tfs_currMode_disc_pres; [exact w | | exact NFS | exact TS].
  eapply currSince_curr. exact CS.
Qed.


Print Assumptions tfsState_not_currSince_fixed.
