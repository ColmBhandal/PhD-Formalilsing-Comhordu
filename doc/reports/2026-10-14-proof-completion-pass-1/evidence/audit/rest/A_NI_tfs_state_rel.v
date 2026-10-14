From Stdlib Require Import Program.Equality.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.NARMisc.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.NARInsuff.

(* ===== audit evidence ===== *)

(* A dae for an output or a non-matching input of dormant/tfsStart is contradictory. *)
Ltac tfs_state_rel_dae_contra H :=
  let p' := fresh "p'" in let S := fresh "S" in
  destruct H as [p' S];
  repeat (match goal with
          | [S0 : stepDiscProc (sum _ _) _ _ |- _] => inversion S0; subst; clear S0
          | [S0 : stepDiscProc (inPrefix _ _ _) _ _ |- _] => inversion S0
          | [S0 : stepDiscProc (outPrefix _ _ _) _ _ |- _] => inversion S0
          end).

(** The initial overlap process dormant is in none of the tfs states. *)
Lemma tfs_state_rel_dormant_not_tfs : tfsState dormant -> False.
Proof.
  intro T. inversion T as [TS | m TN | TC | TB | TL].
  - lets DA : dormant_abort_in (ComhCoq.ProcEquiv.bisim_refl dormant).
    lets DA' : ComhCoq.ProcEquiv.bisim_dae TS DA. unfold tfsStart in DA'.
    tfs_state_rel_dae_contra DA'.
  - lets DA : tfsNext_mStable_out TN. unfold dormant in DA. tfs_state_rel_dae_contra DA.
  - lets DA : tfsCurr_mCurr_out TC. unfold dormant in DA. tfs_state_rel_dae_contra DA.
  - lets DA : tfsBc_trans_out TB. unfold dormant in DA. tfs_state_rel_dae_contra DA.
  - lets DA : tfsListen_unpause_out TL. unfold dormant in DA. tfs_state_rel_dae_contra DA.
Qed.

(** An initial network has no entity in a tfs state. *)
Lemma tfs_state_rel_init_not_tfs i n : initialNet n -> tfsStateNet i n -> False.
Proof.
  intros INIT T. destruct T as [e TE EIN].
  lets IE : initialNet_ent INIT EIN.
  inversion IE as [p0 l h m IP FS]; subst.
  inversion IP; subst. inversion TE as [p1 l1 h1 k1 TP]; subst.
  unfold procProtocol in TP. inversion TP as [q1 q2 q3 TQ]; subst.
  apply tfs_state_rel_dormant_not_tfs. assumption.
Qed.

(* MISSING: backtracking for tfsBc / tfsListen (no such lemma exists in the development). *)
Lemma tfs_state_rel_tfsBc_prev i n n' a :
  reachableNet n -> tfsBcStateNet i n' -> n -NA- a -NA> n' -> tfsStateNet i n.
Admitted.

Lemma tfs_state_rel_tfsListen_prev i n n' a :
  reachableNet n -> tfsListenStateNet i n' -> n -NA- a -NA> n' -> tfsStateNet i n.
Admitted.


Print Assumptions tfs_state_rel_init_not_tfs.
