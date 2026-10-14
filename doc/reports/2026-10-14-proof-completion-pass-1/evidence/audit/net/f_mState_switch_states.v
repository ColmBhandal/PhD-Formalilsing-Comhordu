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

(* ===== helpers copied verbatim from work/w1b-04/NetAuxBasics.mState_switch_states.v ===== *)

(* Counterexample (explore only): the mode state may spontaneously start a mode
   switch (entity rule stepDeTest), with the software untouched. *)
Lemma mState_switch_states_cex (m : Mode) :
  ~ (forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k k' : ModeState), reachableNet n -> k <> k' ->
  n -NA- a -NA> n' -> mState_in_net k i n -> mState_in_net k' i n' ->
  (tfsCurrStateNet i n /\ tfsBcStateNet i n') \/
  (switchCurrStateNet i n /\ switchListenStateNet i n')).
Proof.
  intro H.
  pose (m0 := failSafeSucc m).
  pose (m1 := failSafeSucc m0).
  pose (pr := failSafeSucc_successor m0).
  pose (l := mkPosition 0%R 0%R).
  pose (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  pose (k' := <| m0, m1, modeTransTime m0 m1 pr |>).
  assert (RN : reachableNet [[|procProtocol, l, h, sing m0|]]).
  { apply reachNetInit. apply initNtCons; [ | apply initNtNil].
    apply initEnt. apply initProcProt. apply failSafeSuccFS. }
  assert (ST : [[|procProtocol, l, h, sing m0|]] -NA- anTau -NA>
               [[|procProtocol, l, h, k'|]]).
  { apply stepDnTauHead. eapply stepDeTest. apply (stepMsInit m0 m1 pr). }
  assert (NEQ : sing m0 <> k') by discriminate.
  assert (M1 : mState_in_net (sing m0) 0 [[|procProtocol, l, h, sing m0|]])
    by (econstructor; apply einConsLeft).
  assert (M2 : mState_in_net k' 0 [[|procProtocol, l, h, k'|]])
    by (econstructor; apply einConsLeft).
  destruct (H _ _ _ _ _ _ RN NEQ ST M1 M2) as [[A _] | [A _]];
  destruct A as [e X E]; inversion E; subst;
  inversion X as [p0 l0 h0 k0 Y]; subst; unfold procProtocol in Y;
  inversion Y as [q1 q2 q3 Z]; subst.
  - lets D : tfsCurr_mCurr_out Z. destruct D as [q T]. unfold dormant in T.
    repeat invert_trans.
  - lets D : switchCurr_mCurr_out Z. destruct D as [q T]. unfold dormant in T.
    repeat invert_trans.
Qed.

(* Suggested fix (explore only): add  unstable k  (the only shape used by the
   caller tfs_transGuard in NARMisc.v). Proved relative to admitted lemmas. *)
Lemma mState_switch_states_fixed : forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k k' : ModeState), reachableNet n -> unstable k -> k <> k' ->
  n -NA- a -NA> n' -> mState_in_net k i n -> mState_in_net k' i n' ->
  (tfsCurrStateNet i n /\ tfsBcStateNet i n') \/
  (switchCurrStateNet i n /\ switchListenStateNet i n').
Proof.
  intros n n' i a k k' RN UK NEQ ST M1 M2.
  destruct M1 as [p l h E1]. destruct M2 as [p' l' h' E2].
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST E2) as [e0 [E0 [EQ | [a' S]]]].
  - subst e0. lets U : entInNetUnique E1 E0. inversion U; subst.
    exfalso; apply NEQ; reflexivity.
  - lets U : entInNetUnique E1 E0. subst e0.
    inversion S; subst; try (exfalso; apply NEQ; reflexivity);
    match goal with V : _ -ms- _ -ms> _ |- _ => inversion V; subst end;
    try (exfalso; apply NEQ; reflexivity); try solve [inversion UK].
    (* only the mCurr write remains *)
    lets RP : link_net_prot_reach RN E1.
    lets PS : reachableProt_triple RP.
    inversion PS as [p1 p2 p3 B O L]; subst.
    match goal with V : _ $||$ _ $||$ _ -PA- _ -PA> _ |- _ => rename V into PT end.
    lets PE : link_par_triple_discEx PT.
    destruct PE as [p1' [p2' [p3' PE]]]. subst.
    lets LPO : link_par_triple_out PT.
    destruct LPO as [[T [Q1 Q2]] | [[T [Q1 Q2]] | [T [Q1 Q2]]]].
    + exfalso. eapply bc_mCurr_out_not; eassumption.
    + lets OV : ovlp_mCurr_out T O.
      destruct OV as [[X Y] | [X Y]].
      * right. split.
        -- eapply lenWitness; [ | exact E1]. apply lifpe. apply lftOv. exact X.
        -- eapply lenWitness; [ | exact E2]. apply lifpe. apply lftOv. exact Y.
      * left. split.
        -- eapply lenWitness; [ | exact E1]. apply lifpe. apply lftOv. exact X.
        -- eapply lenWitness; [ | exact E2]. apply lifpe. apply lftOv. exact Y.
    + exfalso. eapply listen_mCurr_out_not; eassumption.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions mState_switch_states_fixed.
