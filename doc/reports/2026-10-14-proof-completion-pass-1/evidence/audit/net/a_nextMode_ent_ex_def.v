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

(* ===== helpers copied verbatim from work/NetAuxBasics-6/NetAuxBasics.nextMode_ent_ex.v ===== *)

(* Demonstration only: the proposed completion of the nextModeNet stub. *)
Definition nextMode_ent_ex_nextModeNet (m : Mode) : nat -> Network -> Prop :=
  liftEntNet (nextModeEnt m).
Lemma nextMode_ent_ex_with_def : forall (m : Mode) (i : nat) (n : Network),
  nextMode_ent_ex_nextModeNet m i n <-> exists e, e @ i .: n /\ nextModeEnt m e.
Proof.
  intros m i n. unfold nextMode_ent_ex_nextModeNet. split.
  - intros [e X E]. exists e. split; assumption.
  - intros [e [E X]]. econstructor; eassumption.
Qed.
(* Proposed completion of the nextModeEnt stub (EntAuxDefs), per its 'Idea' comment. *)
Inductive nextMode_ent_ex_nextModeEnt (m' : Mode) : Entity -> Prop :=
  | nextMode_ent_ex_nmeWitness p l h m t :
    nextMode_ent_ex_nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
Lemma nextMode_ent_ex_nextModeEnt_mState p l h k m :
  nextMode_ent_ex_nextModeEnt m ([|p, l, h, k|]) -> nextModeMState k = Some m.
Proof. intros H. inversion H. reflexivity. Qed.
Lemma nextMode_ent_ex_nextModeEnt_not_stable m1 m2 p l h :
  nextMode_ent_ex_nextModeEnt m1 ([|p, l, h, sing m2|]) -> False.
Proof. intros H. inversion H. Qed.
(* ===== audit wrapper ===== *)
Print Assumptions nextMode_ent_ex_with_def.
Print Assumptions nextMode_ent_ex_nextModeEnt_mState.
Print Assumptions nextMode_ent_ex_nextModeEnt_not_stable.
