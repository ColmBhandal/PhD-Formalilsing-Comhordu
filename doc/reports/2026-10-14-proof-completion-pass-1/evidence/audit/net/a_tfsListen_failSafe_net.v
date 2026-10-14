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
(* Auditor-constructed check: tfsListen_failSafe_net is false in the intended model.
   (1) with the intended definition of the currModeNet stub; (2) with the visible
   Conjecture currMode_intro instead of a definition. *)
Definition audit_cmn (m : Mode) (i : nat) (n : Network) : Prop :=
  exists e, e @ i .: n /\ currModeEnt e = m.

Lemma audit_tfsListen_failSafe_net_intended :
  (forall (m : Mode) (i : nat) (n : Network),
     tfsListenStateNet i n -> audit_cmn m i n -> failSafe m) ->
  forall m : Mode, failSafe m.
Proof.
  intros H m.
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (e := [| nilProc $||$ tfsListen $||$ nilProc, mkPosition 0 0, h0, sing m |]).
  apply (H m 0%nat [e]).
  - eapply lenWitness; [ | constructor ]. unfold e.
    eapply lifpe. constructor. unfold tfsListenState. apply ComhCoq.ProcEquiv.bisim_refl.
  - exists e. split; [ constructor | reflexivity ].
Qed.

Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsListen_failSafe_net in exact T).
Lemma audit_tfsListen_failSafe_net_with_intro : audit_stmt -> forall m : Mode, failSafe m.
Proof.
  unfold audit_stmt. intros H m.
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (e := [| nilProc $||$ tfsListen $||$ nilProc, mkPosition 0 0, h0, sing m |]).
  apply (H m 0%nat [e]).
  - eapply lenWitness; [ | constructor ]. unfold e.
    eapply lifpe. constructor. unfold tfsListenState. apply ComhCoq.ProcEquiv.bisim_refl.
  - apply (currMode_intro m e 0%nat [e]); [ reflexivity | constructor ].
Qed.
Print Assumptions audit_tfsListen_failSafe_net_intended.
Print Assumptions audit_tfsListen_failSafe_net_with_intro.
