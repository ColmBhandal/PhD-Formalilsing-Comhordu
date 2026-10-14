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

(* ===== helpers copied verbatim from work/NetAuxBasics-6/NetAuxBasics.tfsNext_currModeNet_eq.v ===== *)

(* Demonstration (not for splicing): the statement as given, together with the
   visible Conjecture currMode_intro, forces Mode to be a singleton type. *)
Lemma tfsNext_currModeNet_eq_collapses_Mode :
  (forall m1 m2 i n, currModeNet m1 i n -> tfsNextStateNet m2 i n -> m1 = m2) ->
  forall m1 m2 : Mode, m1 = m2.
Proof.
  intros H m1 m2.
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (e := [| tfsNext m2 $||$ tfsNext m2 $||$ tfsNext m2, mkPosition 0 0, h0, sing m1 |]).
  apply (H m1 m2 0%nat [e]).
  - apply (currMode_intro m1 e 0%nat [e]); [ reflexivity | constructor ].
  - eapply lenWitness; [ | constructor ]. unfold e.
    eapply lifpe. constructor. unfold tfsNextState. apply ComhCoq.ProcEquiv.bisim_refl.
Qed.

(* Corrected statement (with reachability), provable from visible results. *)
Lemma tfsNext_currModeNet_eq_reach m1 m2 i n : reachableNet n -> currModeNet m1 i n ->
  tfsNextStateNet m2 i n -> m1 = m2.
Proof.
  intros R C T. apply currMode_ent_ex in C. destruct C as [e [E CE]].
  destruct T as [e' T E']. lets EQ : entInNetUnique E E'. subst e'.
  lets RE : reachable_net_ent R E. lets Q : tfsNext_currMode RE T. congruence.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions tfsNext_currModeNet_eq_collapses_Mode.
Print Assumptions tfsNext_currModeNet_eq_reach.
