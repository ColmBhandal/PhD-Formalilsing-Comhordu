Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProcEquiv.
Require Import ComhCoq.ProtAuxResults.

(* ===== audit evidence ===== *)

Local Lemma gotMessage_next_cx_shape e1 e2 :
  evalExpFun (eSubtract e1 e2) = None \/
  exists r, evalExpFun (eSubtract e1 e2) = Some (baseNonneg r).
Proof.
  simpl. destruct (evalExpFun e1); [ | left; reflexivity].
  destruct (evalExpFun e2); [ | left; reflexivity].
  destruct (evalBaseNonnegFun b); [ | left; reflexivity].
  destruct (evalBaseNonnegFun b0); [ | left; reflexivity].
  right. eexists. reflexivity.
Qed.

Local Lemma gotMessage_next_cx_none x y e1 e2 :
  evalBoolExpFun (bPossInc x y (eSubtract e1 e2)) = None.
Proof.
  cbn [evalBoolExpFun].
  destruct (gotMessage_next_cx_shape e1 e2) as [SH | [r SH]]; rewrite SH;
  destruct (evalExpFun x) as [[] | ]; destruct (evalExpFun y) as [[] | ]; reflexivity.
Qed.

Local Lemma gotMessage_next_cx_none2 x y e1 e2 :
  evalBoolExpFun (!~ bPossInc x y (eSubtract e1 e2)) = None.
Proof.
  transitivity (option_map negb (evalBoolExpFun (bPossInc x y (eSubtract e1 e2))));
    [reflexivity | ].
  rewrite gotMessage_next_cx_none. reflexivity.
Qed.

Lemma gotMessage_next_cx (m : Mode) (l : Position) : exists p p' a,
  p -PA- a -PA> p' /\ gotMsgState m l p /\ ~ exists r, gotRangeState m r p'.
Proof.
  exists (gotMsg m l). eexists. exists (chanPos ;? [basePosition l]).
  split; [ | split].
  - unfold gotMsg. apply stepDpIn. reflexivity.
  - apply bisim_refl.
  - intros [r B]. unfold gotRangeState in B.
    assert (T2 : exists q2, gotRange m r -PA- chanMCurr ;? [baseMode m] -PA> q2).
    { eexists. unfold gotRange. apply stepDpIn. reflexivity. }
    destruct T2 as [q2 T2].
    inversion B as [B1 B2].
    destruct (B2 _ _ (stepPDisc _ _ _ T2)) as [q1 [T1 BQ]].
    clear B1 B2.
    inversion T1 as [a0 q1' T1' | ]; subst. clear T1.
    simpl in T1'.
    invert_app_trans.
    inversion T2; subst. clear T2.
    inversion H4; subst. clear H4.
    clean_proc_hyp BQ.
    match type of BQ with _ ~p~ ?Q =>
      assert (DA : exists a q, Q -PA- a -PA> q) end.
    { destruct (possIncBool m m r) eqn:PI.
      - do 2 eexists. eapply stepDpApp; [reflexivity | ]. clean_proc.
        apply stepDpChoiceR. apply stepDpThen;
          [ | unfold evalBoolExpFunTot; simpl; rewrite PI; reflexivity].
        eapply stepDpApp; [reflexivity | ]. clean_proc. constructor. constructor.
      - do 2 eexists. eapply stepDpApp; [reflexivity | ]. clean_proc.
        apply stepDpChoiceL. apply stepDpThen;
          [ | unfold evalBoolExpFunTot; simpl; rewrite PI; reflexivity].
        eapply stepDpApp; [reflexivity | ]. clean_proc.
        apply stepDpChoiceL. apply stepDpIn with (l1 := []). reflexivity. }
    destruct DA as [a2 [q3 DA]].
    destruct (bisim_disc_match _ _ _ _ (bisim_symm _ _ BQ) DA) as [q4 S4].
    clear DA BQ B.
    invert_app_trans.
    match goal with H : _ $+$ _ -PA- _ -PA> _ |- _ => inversion H; subst end;
    match goal with H : _ $> _ -PA- _ -PA> _ |- _ => inversion H; subst end;
    match goal with H : evalBoolExpFunTot _ = true |- _ =>
      unfold evalBoolExpFunTot in H;
      first [rewrite gotMessage_next_cx_none2 in H | rewrite gotMessage_next_cx_none in H];
      discriminate H end.
Qed.

(** Hence the statement as given implies False for any mode and position. *)
Lemma gotMessage_next_false :
  (forall p p' a m'' l, p -PA- a -PA> p' -> gotMsgState m'' l p ->
    exists r, gotRangeState m'' r p') -> forall (m : Mode) (l : Position), False.
Proof.
  intros H m l. destruct (gotMessage_next_cx m l) as (p & p' & a & S & G & NG).
  exact (NG (H _ _ _ _ _ S G)).
Qed.
(* Print Assumptions gotMessage_next_false: only model axioms + proof_irrelevance, functional_extensionality_dep, ClassicalDedekindReals; no admitted lemma. *)


Print Assumptions gotMessage_next_false.
