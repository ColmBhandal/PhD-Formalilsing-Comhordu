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

(* ===== helpers copied verbatim from work/w1b-10/NetAuxBasics.nextModeNet_del_pres.demo.v ===== *)

(* Demonstration only: with the proposed stub definitions the statement is provable. *)
Inductive nextModeNet_del_pres_ent (m' : Mode) : Entity -> Prop :=
  | nextModeNet_del_pres_wit p l h m t :
      nextModeNet_del_pres_ent m' ([|p, l, h, <| m, m', t |>|]).

Definition nextModeNet_del_pres_def (m : Mode) := liftEntNet (nextModeNet_del_pres_ent m).

Lemma nextModeNet_del_pres_ent_del (e e' : Entity) (d : Delay) (m : Mode) :
  e -ED- d ->> e' -> nextModeNet_del_pres_ent m e -> nextModeNet_del_pres_ent m e'.
Proof.
  intros D X. inversion X; subst. inversion D; subst.
  match goal with K : _ -ms- _ -ms> _ |- _ =>
    destruct (delMStatePresTrans _ _ _ _ _ K) as [t' E] end.
  subst. constructor.
Qed.

Lemma nextModeNet_del_pres_under_def n n' d m i :
  n -ND- d -ND> n' -> nextModeNet_del_pres_def m i n -> nextModeNet_del_pres_def m i n'.
Proof.
  intros ND [e X E].
  destruct (link_net_ent_del_fwd n n' e i d ND E) as [e' [E' D]].
  econstructor; [ eapply nextModeNet_del_pres_ent_del; eassumption | exact E' ].
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions nextModeNet_del_pres_under_def.
