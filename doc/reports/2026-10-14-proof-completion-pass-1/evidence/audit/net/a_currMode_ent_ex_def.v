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

(* ===== helpers copied verbatim from work/NetAuxBasics-6/NetAuxBasics.currMode_ent_ex.v ===== *)

(* Demonstration only: the proposed completion of the currModeNet stub
   (stated here directly, as currModeNet is declared before liftEntNet). *)
Inductive currMode_ent_ex_currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
  | currMode_ent_ex_cmnWitness (e : Entity) :
    e @ i .: n -> currModeEnt e = m -> currMode_ent_ex_currModeNet m i n.
Lemma currMode_ent_ex_with_def : forall (m : Mode) (i : nat) (n : Network),
  currMode_ent_ex_currModeNet m i n <-> exists e, e @ i .: n /\ currModeEnt e = m.
Proof.
  intros m i n. split.
  - intros [e E C]. exists e. split; assumption.
  - intros [e [E C]]. econstructor; eassumption.
Qed.
(* The intended definition is also equivalent to the lifted form. *)
Lemma currMode_ent_ex_def_lift : forall (m : Mode) (i : nat) (n : Network),
  currMode_ent_ex_currModeNet m i n <-> liftEntNet (fun e => currModeEnt e = m) i n.
Proof.
  intros m i n. split.
  - intros [e E C]. econstructor; eassumption.
  - intros [e C E]. econstructor; eassumption.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions currMode_ent_ex_with_def.
Print Assumptions currMode_ent_ex_def_lift.
