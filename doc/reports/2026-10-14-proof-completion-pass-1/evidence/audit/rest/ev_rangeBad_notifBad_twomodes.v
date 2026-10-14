Require Import ComhCoq.ProcEquiv.
Lemma rangeBad_next_app_bisim n l :
  n $( l )$ ~p~ subProcTerm (listsToSub (fst (def n)) l) (snd (def n)).
Proof.
  constructor; intros a q T.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + constructor. apply stepDpApp_alt. assumption.
    + constructor. remember (def n) as dn. destruct dn as [l1 b].
      eapply stepTpApp. symmetry. eassumption. assumption.
Qed.
Lemma rangeBad_next_inv m'' a q :
  rangeBad (eBase (baseMode m'')) -PA- a -PA> q ->
  exists b, a = chanMCurr ;? [b] /\ q ~p~ currEq (eBase b) (eBase (baseMode m'')).
Proof.
  intro S. unfold rangeBad in S. inversion S; subst.
  match goal with [H : length ?l = length _ |- _] =>
    destruct l as [ | b [ | b' l]]; simpl in H; try discriminate H end.
  exists b. split; [reflexivity | ].
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp].
  remove_updates.
  eapply bisim_trans; [apply rangeBad_next_app_bisim | ].
  cbn [def fst snd listsToSub liftVarList liftExpList subProcTerm subExp subBoolExp
    listSub map liftNameProc listBaselistExp currEq].
  remove_updates. apply bisim_refl.
Qed.
Lemma rangeBad_next_currOK (b : BaseType) (m'' : Mode) :
  b <> baseMode m'' ->
  currEq (eBase b) (eBase (baseMode m'')) ~p~ currOKN $([eBase (baseMode m'')])$.
Proof.
  intro N. unfold currEq. apply if_then_bisim_false.
  eapply bevalEqualFalse; [apply evalBase | apply evalBase | exact N].
Qed.

Lemma rbnb_currOK_no_bad m'' : ~ discActEnabled (currOKN $([eBase (baseMode m'')])$) (chanBad *!).
Proof.
  intros [q S]. inversion S; subst.
  match goal with H : def currOKN = _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : subProcTerm _ _ -PA- _ -PA> _ |- _ => cbn in H end.
  repeat match goal with
    | H : sum _ _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H
    | H : inPrefix _ _ _ -PA- _ -PA> _ |- _ => inversion H
    end.
Qed.

Lemma rbnb_currEq_same_bad m'' :
  discActEnabled (currEq (eBase (baseMode m'')) (eBase (baseMode m''))) (chanBad *!).
Proof.
  econstructor. apply stepDpChoiceL. apply stepDpThen.
  - apply stepDpApp_alt. cbn. apply stepDpOut. constructor.
  - apply evalBoolExpTrueTot. eapply bevalEqualTrue; apply evalBase.
Qed.

Lemma rbnb_rangeBad_no_bad m : ~ discActEnabled (rangeBad (eBase (baseMode m))) (chanBad *!).
Proof. intros [q S]. unfold rangeBad in S. inversion S. Qed.

(** Two distinct modes refute rangeBad_notifBad_net as stated. *)
Lemma rangeBad_notifBad_net_two_modes_refuted (m1 m2 : Mode) : m1 <> m2 ->
  ~ (forall m i n, rangeBadStateNet m i n -> notifBadPathNet i n).
Proof.
  intros NE H.
  set (e := [| nilProc $||$ nilProc $||$ rangeBad (eBase (baseMode m1)), mkPosition 0 0,
              mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m2 |]).
  assert (R : rangeBadStateNet m1 0 [e]).
  { econstructor; [ | apply einConsLeft]. constructor. constructor.
    apply ComhCoq.ProcEquiv.bisim_refl. }
  apply H in R. destruct R as [e0 NB EIN]. inversion EIN; subst. unfold e in NB.
  inversion NB as [p l h k m RB CM | p l h k BO]; subst.
  - inversion RB as [p1 p2 p3 RB3]; subst. simpl in RB3.
    (* RB3 : rangeBad m1 ~p~ rangeBad m2 *)
    assert (S2 : rangeBad (eBase (baseMode m2)) -PA- chanMCurr ;? [baseMode m2] -PA>
      subProcTerm (listsToSub [vM] (listBaselistExp [baseMode m2]))
        (currEqN $([eVar vM, eBase (baseMode m2)])$)).
    { unfold rangeBad. apply stepDpIn. reflexivity. }
    pose proof S2 as S2'.
    apply rangeBad_next_inv in S2'. destruct S2' as [b2 [E2 C2]]. inversion E2; subst b2.
    destruct RB3 as [_ B2]. destruct (B2 _ _ (stepPDisc _ _ _ S2)) as [q1 [T1 Q1]].
    inversion T1 as [a0 q0 S1 | ]; subst.
    apply rangeBad_next_inv in S1. destruct S1 as [b1 [E1 C1]]. inversion E1; subst b1.
    assert (OK : currEq (eBase (baseMode m2)) (eBase (baseMode m1)) ~p~ currOKN $([eBase (baseMode m1)])$).
    { apply rangeBad_next_currOK. intro X. inversion X. apply NE. symmetry. assumption. }
    (* currOKN m1 ~ currEq m2 m1 ~ q1 ~ q2 ~ currEq m2 m2 *)
    assert (CH : currOKN $([eBase (baseMode m1)])$ ~p~ currEq (eBase (baseMode m2)) (eBase (baseMode m2))).
    { eapply bisim_trans; [apply bisim_symm; exact OK | ].
      eapply bisim_trans; [apply bisim_symm; exact C1 | ].
      eapply bisim_trans; [exact Q1 | exact C2]. }
    apply (rbnb_currOK_no_bad m1). exact (bisim_dae _ _ _ (bisim_symm _ _ CH) (rbnb_currEq_same_bad m2)).
  - inversion BO as [p1 p2 p3 BO3]; subst.
    (* BO3 : rangeBad m1 ~p~ badOvlp *)
    apply (rbnb_rangeBad_no_bad m1). apply (bisim_dae _ _ _ (bisim_symm _ _ BO3)).
    econstructor. unfold badOvlp. apply stepDpOut. constructor.
Qed.
