(* HELPERS *)
(** An entity cannot be both in an ovWait state and in a tfs state.*)
Lemma tfsStart_tfs_zero_ovWait_tfs m t x y i n :
  ovWaitStateNet m t x y i n -> tfsStateNet i n -> False.
Proof.
  intros OW TS. apply tfsState_elim_net in TS.
  destruct TS as [S | [[m2 S] | [S | [S | S]]]].
  - apply (nextSince_ovReaddy_modeEq_lift tfsStartState (ovWaitState m t x y) i n S OW).
    intros q HX HY. pose proof (tfsStart_mCurr_in q m HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift (tfsNextState m2) (ovWaitState m t x y) i n S OW).
    intros q HX HY. pose proof (tfsNext_mStable_out q m2 HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift tfsCurrState (ovWaitState m t x y) i n S OW).
    intros q HX HY. pose proof (tfsCurr_mCurr_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift tfsBcState (ovWaitState m t x y) i n S OW).
    intros q HX HY. pose proof (tfsBc_trans_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift tfsListenState (ovWaitState m t x y) i n S OW).
    intros q HX HY. pose proof (tfsListen_unpause_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
Qed.
(* PROOF *)
Proof.
  intros n t i m p H. induction H; intros TS.
  - reflexivity.
  - match goal with W : _ -NA- _ -NA> _ |- _ =>
      lets PR : tfsStart_prev_net TS W end.
    destruct PR as [TS' | [m0 [t0 [x [y OW]]]]].
    + apply IHtfs; assumption.
    + exfalso. eapply tfsStart_tfs_zero_ovWait_tfs; [exact OW | ].
      eapply tfs_rel_state; eassumption.
  - exfalso. match goal with W : _ -ND- _ -ND> _ |- _ =>
      eapply tfsStart_urgent_net;
      [eapply del_pres_bkwd_tfsStart; [exact W | exact TS] | exact W] end.
Qed.
