(* HELPERS *)
Ltac notifAbort_not_nextSince_close :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState, tfsStartState,
    tfsNextState, tfsCurrState, tfsBcState, tfsListenState, initState, ovAbortState,
    listeningState, rangeBadState, currOKState, abortOvlpState, badOvlpState,
    currCompState, pausedState, gotMsgState, gotRangeState, currEqState, nextEqState,
    currPincCheckState, nextPincCheckState in *;
  match goal with
  | [V : ProcEquiv.bisimulation ?p ?x, V1 : ProcEquiv.bisimulation ?p ?y |- False] =>
    let BT := fresh "BT" in
    assert (ProcEquiv.bisimulation x y) as BT by
      (eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact V | exact V1]);
    unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
      switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen, ovAbort,
      listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq, abortOvlp,
      gotMsg, gotRange, currPincCheck, currComp, nextPincCheck, paused in BT;
    first [solve [bisim_contra BT] |
      apply ProcEquiv.bisim_symm in BT; solve [bisim_contra BT]]
  end.

(** If the listener component of a reachable entity changes by an input on the
empty channel c, then the partner of that input is one of the other two software
components, the interface or the mode state, each outputting on c.*)
Lemma notifAbort_not_nextSince_in p1 p2 p3 q1 q2 q3 l l' h h' k k' b c :
  protocolState (p1 $||$ p2 $||$ p3) -> p3 <> q3 ->
  (forall act, p3 -PA- act -PA> q3 -> act = c *?) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- b ->> [|q1 $||$ q2 $||$ q3, l', h', k'|] ->
  (p1 -PA- c *! -PA> q1) \/ (p2 -PA- c *! -PA> q2) \/
  (exists h'', h -i- c {! [] -i> h'') \/ (exists k'', k -ms- c @! -ms> k'').
Proof.
  intros PS NEQ TR ST.
  assert (p1 $||$ p2 $||$ p3 <> q1 $||$ q2 $||$ q3) as PNE
    by (intro E; inversion E; contradiction).
  destruct (link_ent_proc_neq_disc _ _ _ _ _ _ _ _ _ PNE ST) as [_ CASES].
  destruct CASES as [T | [[h'' [c0 [v [T H1]]]] | [[h'' [c0 [v [T H1]]]] |
    [[k'' [c0 [m [T H1]]]] | [[k'' [c0 [m [T H1]]]] | [[k'' [c0 [T H1]]] |
    [[k'' [c0 [T H1]]] | T]]]]]]].
  - destruct (link_reach_triple_tau _ _ _ _ _ _ T PS) as [c0 [v CC]].
    destruct CC as [[A1 [A2 A3]] | [[A1 [A2 A3]] | [[A1 [A2 A3]] |
      [[A1 [A2 A3]] | [[A1 [A2 A3]] | [A1 [A2 A3]]]]]]];
      try (subst; contradiction).
    + apply TR in A2. inversion A2; subst. left. assumption.
    + apply TR in A2. inversion A2.
    + apply TR in A2. inversion A2; subst. right; left. assumption.
    + apply TR in A2. inversion A2.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3; subst. right; right; left. eexists; eassumption.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3; subst. right; right; right. eexists; eassumption.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
Qed.

(** As above, but for an output on the empty channel c by the listener.*)
Lemma notifAbort_not_nextSince_out p1 p2 p3 q1 q2 q3 l l' h h' k k' b c :
  protocolState (p1 $||$ p2 $||$ p3) -> p3 <> q3 ->
  (forall act, p3 -PA- act -PA> q3 -> act = c *!) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- b ->> [|q1 $||$ q2 $||$ q3, l', h', k'|] ->
  (p1 -PA- c *? -PA> q1) \/ (p2 -PA- c *? -PA> q2) \/
  (exists h'', h -i- c {? [] -i> h'') \/ (exists k'', k -ms- c @? -ms> k'').
Proof.
  intros PS NEQ TR ST.
  assert (p1 $||$ p2 $||$ p3 <> q1 $||$ q2 $||$ q3) as PNE
    by (intro E; inversion E; contradiction).
  destruct (link_ent_proc_neq_disc _ _ _ _ _ _ _ _ _ PNE ST) as [_ CASES].
  destruct CASES as [T | [[h'' [c0 [v [T H1]]]] | [[h'' [c0 [v [T H1]]]] |
    [[k'' [c0 [m [T H1]]]] | [[k'' [c0 [m [T H1]]]] | [[k'' [c0 [T H1]]] |
    [[k'' [c0 [T H1]]] | T]]]]]]].
  - destruct (link_reach_triple_tau _ _ _ _ _ _ T PS) as [c0 [v CC]].
    destruct CC as [[A1 [A2 A3]] | [[A1 [A2 A3]] | [[A1 [A2 A3]] |
      [[A1 [A2 A3]] | [[A1 [A2 A3]] | [A1 [A2 A3]]]]]]];
      try (subst; contradiction).
    + apply TR in A2. inversion A2.
    + apply TR in A2. inversion A2; subst. left. assumption.
    + apply TR in A2. inversion A2.
    + apply TR in A2. inversion A2; subst. right; left. assumption.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3; subst. right; right; left. eexists; eassumption.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_out_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3; subst. right; right; right. eexists; eassumption.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
  - destruct (link_par_triple_in_neq3 _ _ _ _ _ _ _ _ NEQ T) as [T3 _].
    apply TR in T3. inversion T3.
Qed.
(* PROOF *)
Proof.
  intros U W.
  destruct U as [e E I].
  destruct (link_net_ent_disc_fwd n n' e i a W I) as [e' [I' [EQ | [b ST]]]].
  { subst e'. left. econstructor; eassumption. }
  destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  assert (k' = k) as KEQ.
  { assert (mState_in_net k i n') as M.
    { eapply notifAbort_modeState_eq;
        [econstructor; eassumption | econstructor; exact I | exact W]. }
    eapply mState_in_net_unique; [econstructor; exact I' | exact M]. }
  subst k'.
  assert (reachableProt p) as RP by (eapply reachable_net_prot; eassumption).
  destruct (link_ent_soft_disc p p' l l' h h' k k b ST) as [PEQ | [b' PT]].
  { subst p'. left. econstructor; [ | exact I'].
    inversion E; subst.
    - eapply napRng; [eassumption | reflexivity | eassumption | eassumption].
    - eapply napCuok; eassumption.
    - eapply napAbort; eassumption. }
  inversion E; subst.
  - (* rangeBad *)
    match goal with H : rangeBadStateProt _ _ |- _ =>
      inversion H as [p1 p2 p3 RB3]; subst end.
    destruct (link_par_triple_discEx _ _ _ _ _ PT) as [q1 [q2 [q3 PEQ]]]. subst p'.
    destruct (link_par_triple_discW_3 _ _ _ _ _ _ _ PT) as [P3 | [a3 T3]].
    + subst q3. left. econstructor; [ | exact I'].
      eapply napRng; [constructor; exact RB3 | reflexivity | eassumption | eassumption].
    + destruct (rangeBad_next _ _ _ _ T3 RB3) as [m0 CE].
      assert (m0 = currModeMState k) as M0.
      { eapply (currEq_mode m0 _ ([|q1 $||$ q2 $||$ q3, l', h', k|])).
        constructor. constructor. exact CE. }
      left. econstructor; [ | exact I']. eapply napCuok; [ | eassumption].
      constructor. eapply currEq_cond_false; [ | exact CE]. subst m0. assumption.
  - (* currOK *)
    match goal with H : currOKStateProt _ _ |- _ =>
      inversion H as [p1 p2 p3 CO3]; subst end.
    destruct (link_par_triple_discEx _ _ _ _ _ PT) as [q1 [q2 [q3 PEQ]]]. subst p'.
    destruct (link_par_triple_discW_3 _ _ _ _ _ _ _ PT) as [P3 | [a3 T3]].
    + subst q3. left. econstructor; [ | exact I'].
      eapply napCuok; [constructor; exact CO3 | eassumption].
    + destruct (currOK_next _ _ _ _ T3 CO3) as [[m0 NQ] | LS].
      * assert (nextModeMState k = Some m0) as NK0.
        { apply (nextMode_ent_mState (q1 $||$ q2 $||$ q3) l' h' k m0). eapply nextEq_mode.
          constructor. constructor. exact NQ. }
        left. econstructor; [ | exact I']. eapply napAbort. constructor.
        eapply nextEq_cond_true; [ | exact NQ]. congruence.
      * assert (p3 <> q3) as NEQ3.
        { intro E3. subst q3. notifAbort_not_nextSince_close. }
        assert (protocolState (p1 $||$ p2 $||$ p3)) as PS
          by (apply reachableProt_triple; assumption).
        destruct (notifAbort_not_nextSince_in p1 p2 p3 q1 q2 q3 l l' h h' k k b
          chanMStable PS NEQ3 (fun act T => currOK_listening_track _ _ _ _ CO3 LS T) ST)
          as [T1 | [T2 | [[h'' T] | [k'' T]]]].
        -- exfalso. inversion PS. eapply bc_mStable_out_not; eassumption.
        -- exfalso. inversion PS. eapply ovlp_mStable_out_not; eassumption.
        -- exfalso. eapply inter_mStable_in_not; eassumption.
        -- exfalso. eapply next_modeState_stable_not; eassumption.
  - (* abortOvlp *)
    match goal with H : abortOvlpStateProt _ |- _ =>
      inversion H as [p1 p2 p3 AO3]; subst end.
    destruct (link_par_triple_discEx _ _ _ _ _ PT) as [q1 [q2 [q3 PEQ]]]. subst p'.
    destruct (link_par_triple_discW_3 _ _ _ _ _ _ _ PT) as [P3 | [a3 T3]].
    + subst q3. left. econstructor; [ | exact I']. eapply napAbort.
      constructor. exact AO3.
    + pose proof (abortOvlp_next _ _ _ T3 AO3) as LS.
      assert (p3 <> q3) as NEQ3
        by (intro E3; subst q3; eapply listening_abort_contra; eassumption).
      assert (protocolState (p1 $||$ p2 $||$ p3)) as PS
        by (apply reachableProt_triple; assumption).
      right. intro NS.
      destruct (notifAbort_not_nextSince_out p1 p2 p3 q1 q2 q3 l l' h h' k k b
        chanAbort PS NEQ3 (fun act T => abortOvlp_listening_track _ _ _ AO3 LS T) ST)
        as [T1 | [T2 | [[h'' T] | [k'' T]]]].
      * inversion PS. eapply bc_abort_in_not; eassumption.
      * inversion PS as [x1 x2 x3 BS OS LS0]; subst.
        apply (ovlp_abort_in_notNextSince p2 q2 T2 OS).
        destruct NS as [e0 E0 I0].
        pose proof (entInNetUnique _ _ _ _ I0 I') as EQ0. subst e0.
        inversion E0 as [? ? ? ? NS0]; subst. inversion NS0; subst. assumption.
      * eapply inter_abort_in_not; eassumption.
      * eapply modeState_abort_in_not; eassumption.
Qed.
