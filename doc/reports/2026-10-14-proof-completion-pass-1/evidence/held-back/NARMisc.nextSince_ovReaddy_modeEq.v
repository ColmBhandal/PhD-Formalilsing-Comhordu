(* HELPERS *)
(** Two overlap-component state predicates holding for the same entity in the
same network reduce to both holding of the same overlap process.*)
Lemma nextSince_ovReaddy_modeEq_lift (X Y : ProcTerm -> Prop) i n :
  liftEntNet (liftProcEnt (liftOverlap X)) i n ->
  liftEntNet (liftProcEnt (liftOverlap Y)) i n ->
  (forall p, X p -> Y p -> False) -> False.
Proof.
  intros H1 H2 HXY.
  inversion H1 as [e1 E1 I1]; inversion H2 as [e2 E2 I2].
  assert (e1 = e2) as EQ by (eapply entInNetUnique; eassumption). subst e2.
  inversion E1 as [p l h k P1 EQ1]; subst.
  inversion E2 as [p' l' h' k' P2 EQ2]; subst.
  inversion P1 as [a b c X1 EQ3]; subst.
  inversion P2 as [a' b' c' Y1 EQ4]; subst.
  eapply HXY; eassumption.
Qed.

(** Given D : discActEnabled B a, with B a concrete overlap process body that
cannot perform a, closes the goal by exhaustive inversion.*)
Ltac nextSince_ovReaddy_modeEq_inv D :=
  let p' := fresh "p'" in let T := fresh "T" in
  destruct D as [p' T];
  cbv [ovWait ovReady tfsStart tfsNext tfsCurr tfsBc tfsListen switchCurr
    switchBc switchListen dormant init ovAbort] in T;
  repeat match goal with
  | T0 : _ -PA- _ -PA> _ |- _ => inversion T0; subst; clear T0
  end.

Lemma nextSince_ovReaddy_modeEq_ovReady_out m t l p :
  ovReadyState m t l p ->
  discActEnabled p (chanOutProc ;! [baseMode m, basePosition l]).
Proof. activation_tac. Qed.

Lemma nextSince_ovReaddy_modeEq_wr m t x y m' t' l i n :
  ovWaitStateNet m t x y i n -> ovReadyStateNet m' t' l i n -> False.
Proof.
  intros W R.
  apply (nextSince_ovReaddy_modeEq_lift (ovReadyState m' t' l)
    (ovWaitState m t x y) i n R W).
  intros p HR HW.
  lets D : nextSince_ovReaddy_modeEq_ovReady_out HR.
  eapply bisim_dae in D; [ | exact HW].
  nextSince_ovReaddy_modeEq_inv D.
Qed.
(* PROOF *)
Proof.
  intros NS. revert t' l. induction NS; intros t0 l0 OR.
  - exfalso. eapply nextSince_ovReaddy_modeEq_wr; eassumption.
  - match goal with W : _ -NA- _ -NA> _ |- _ =>
      lets PR : ovReady_prev_net OR W end.
    destruct PR as [OR' | [x0 [y0 OW]]].
    + eapply IHNS; eassumption.
    + eapply nextSince_ovWait_modeEq; eassumption.
  - eapply IHNS. eapply ovReady_del_pres_bkwd_net; eassumption.
Qed.
