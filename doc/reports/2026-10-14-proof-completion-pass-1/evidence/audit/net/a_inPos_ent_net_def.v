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

(* ===== helpers copied verbatim from work/NetAuxBasics-6/NetAuxBasics.inPos_ent_net.v ===== *)

(* Demonstration only: the proposed completion of the inPosEnt stub, and the
   statement proved against it. *)
Inductive inPos_ent_net_inPosEnt (l : Position) : Entity -> Prop :=
  | inPos_ent_net_ipeWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
    inPos_ent_net_inPosEnt l ([|p, l, h, k|]).
Lemma inPos_ent_net_with_def : forall (l : Position) (e : Entity) (i : nat) (n : Network),
  inPos_ent_net_inPosEnt l e -> e @ i .: n -> inPosNet l i n.
Proof. intros l e i n H E. destruct H. econstructor. eassumption. Qed.
(* ===== audit wrapper ===== *)
Print Assumptions inPos_ent_net_with_def.
