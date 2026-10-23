(* HELPERS *)
(** A tfsStart or tfsNext state is never a switchCurr or tfsCurr state:
the latter two can output on mCurr, the former cannot.*)
Lemma tfsNext_tfs_mode_eq_notMCurr i n :
  (tfsStartStateNet i n \/ exists m2, tfsNextStateNet m2 i n) ->
  switchCurrStateNet i n \/ tfsCurrStateNet i n -> False.
Proof.
  intros [S | [m2 S]] [C | C].
  - apply (nextSince_ovReaddy_modeEq_lift switchCurrState tfsStartState i n C S).
    intros q HX HY. pose proof (switchCurr_mCurr_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift tfsCurrState tfsStartState i n C S).
    intros q HX HY. pose proof (tfsCurr_mCurr_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift switchCurrState (tfsNextState m2) i n C S).
    intros q HX HY. pose proof (switchCurr_mCurr_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
  - apply (nextSince_ovReaddy_modeEq_lift tfsCurrState (tfsNextState m2) i n C S).
    intros q HX HY. pose proof (tfsCurr_mCurr_out q HX) as D.
    eapply bisim_dae in D; [ | exact HY]. nextSince_ovReaddy_modeEq_inv D.
Qed.

(** While tfs m and in the tfsStart or tfsNext state, the current mode is m.*)
Lemma tfsNext_tfs_mode_eq_curr m t i n (p : reachableNet n) :
  tfs m t i n p ->
  (tfsStartStateNet i n \/ exists m2, tfsNextStateNet m2 i n) ->
  currModeNet m i n.
Proof.
  intros H.
  induction H as [i0 n0 p0 TS0 CM0 | a0 t0 i0 n0 n0' p0 w0 H0 IH0 TSn
    | d0 t0 i0 n0 n0' p0 w0 H0 IH0]; intros S.
  - exact CM0.
  - assert (PREV : tfsStartStateNet i0 n0 \/ exists m2, tfsNextStateNet m2 i0 n0).
    { destruct S as [S | [m2 S]].
      - lets PR : tfsStart_prev_net S w0.
        destruct PR as [S' | [m3 [t3 [x3 [y3 OW]]]]].
        + left; exact S'.
        + exfalso. eapply tfsStart_tfs_zero_ovWait_tfs; [exact OW | ].
          eapply tfs_rel_state; eassumption.
      - lets PR : tfsNext_prev_net S w0.
        destruct PR as [S' | S'].
        + right; exists m2; exact S'.
        + left; exact S'. }
    lets CMn : IH0 PREV.
    destruct (currMode_pres_fwd n0 n0' a0 m i0 w0 CMn) as [m' CM'].
    destruct (eqDecMode m m') as [EQ | NE].
    + subst m'. exact CM'.
    + exfalso. destruct (currModeNet_switch_states n0 n0' a0 m m' i0 p0 w0 CMn CM' NE)
        as [[C _] | [C _]].
      * eapply tfsNext_tfs_mode_eq_notMCurr; [exact PREV | left; exact C].
      * eapply tfsNext_tfs_mode_eq_notMCurr; [exact PREV | right; exact C].
  - exfalso. destruct S as [S | [m2 S]].
    + eapply tfsStart_urgent_net;
        [eapply del_pres_bkwd_tfsStart; [exact w0 | exact S] | exact w0].
    + eapply tfsNext_urgent_net;
        [eapply del_pres_bkwd_tfsNext; [exact w0 | exact S] | exact w0].
Qed.
(* PROOF *)
Proof.
  intros n t i m1 m2 p H TN.
  apply (tfsNext_currModeNet_eq m1 m2 i n); [ | exact TN].
  eapply tfsNext_tfs_mode_eq_curr; [exact H | right; exists m2; exact TN].
Qed.
