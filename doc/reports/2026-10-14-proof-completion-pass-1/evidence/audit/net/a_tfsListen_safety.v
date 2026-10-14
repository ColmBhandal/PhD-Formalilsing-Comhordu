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

(* ===== helpers copied verbatim from audit/audit-net/empty_ev.v ===== *)

(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsListen_failSafe_net in exact T).
Lemma audit_tfsListen_allFS : audit_stmt -> forall m : Mode, failSafe m.
Proof.
  unfold audit_stmt. intros H m.
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (e := [| nilProc $||$ tfsListen $||$ nilProc, mkPosition 0 0, h0, sing m |]).
  apply (H m 0%nat [e]).
  - eapply lenWitness; [ | constructor ]. unfold e.
    eapply lifpe. constructor. unfold tfsListenState. apply ComhCoq.ProcEquiv.bisim_refl.
  - apply (currMode_intro m e 0%nat [e]); [ reflexivity | constructor ].
Qed.
(* With currMode_intro (also in the safety cone), tfsListen_failSafe_net makes
   Main.safety's conclusion provable without any protocol reasoning. *)
Lemma audit_tfsListen_trivialises_safety : audit_stmt -> forall n : Network, safe n.
Proof.
  intros H n e1 e2 i j _ _ _. unfold compatible.
  rewrite (minDistCompFS (currModeEnt e1) (currModeEnt e2) (audit_tfsListen_allFS H _)).
  simpl. apply dist_euc_nonneg.
Qed.
Print Assumptions audit_tfsListen_trivialises_safety.
