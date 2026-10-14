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

(* ===== helpers copied verbatim from work/NetAuxBasics-5/NetAuxBasics.currModeNet_del_pres.v ===== *)

(* Demonstration: with the proposed stub definition, the statement is provable. *)
Definition currModeNet_del_pres_def (m : Mode) (i : nat) (n : Network) : Prop :=
  exists e, e @ i .: n /\ currModeEnt e = m.

Lemma currModeNet_del_pres_ent : forall (e e' : Entity) (d : Delay),
  e -ED- d ->> e' -> currModeEnt e = currModeEnt e'.
Proof.
  intros e e' d D. inversion D; subst. cbn.
  match goal with K : _ -ms- _ -ms> _ |- _ => inversion K; subst; reflexivity end.
Qed.

Lemma currModeNet_del_pres_under_def : forall (n n' : Network) (d : Delay)
  (m : Mode) (i : nat), n -ND- d -ND> n' ->
  (currModeNet_del_pres_def m i n <-> currModeNet_del_pres_def m i n').
Proof.
  intros n n' d m i ND. unfold currModeNet_del_pres_def. split.
  - intros [e [E CM]].
    destruct (link_net_ent_del_fwd n n' e i d ND E) as [e' [E' D]].
    exists e'. split; [exact E' | ].
    rewrite <- CM. symmetry. eapply currModeNet_del_pres_ent. exact D.
  - intros [e' [E' CM]].
    destruct (link_net_ent_del_bkwd n n' e' i d ND E') as [e [E D]].
    exists e. split; [exact E | ].
    rewrite <- CM. eapply currModeNet_del_pres_ent. exact D.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions currModeNet_del_pres_under_def.
