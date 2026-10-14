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

(** Proposed replacement statement (extra hypothesis: the entity was currSince
    in n, which is what the only user, NARIncomp.instant_incomp_tfs, has in
    context). Provable relative to existing admitted lemmas. *)
Lemma tfs_zero_disc_pres_fix (n n' : Network) (a : ActDiscNet) (i : nat) (m m' : Mode)
  (t : Time) (p : reachableNet n) (w : n -NA- a -NA> n') :
  currSince m' t i n p -> tfs m zeroTime i n p ->
  tfs m zeroTime i n' (reachNetDisc n n' a p w).
Proof.
  intros CS T. destruct (tfsStateNet_dec i n') as [D|D].
  - apply tfsDisc; assumption.
  - exfalso. eapply (tfsState_not_currSince m' t i n n' p a w);
    [eapply tfs_rel_state; eassumption | exact D | exact CS].
Qed.


Print Assumptions tfs_zero_disc_pres_fix.
