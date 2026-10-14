(* HELPERS *)
(* Given D : discActEnabled q a with q a concrete overlap state term that cannot
   perform a, unfold q and invert every transition to close the goal. *)
Ltac ovWait_ovReady_nextMode_net_dae_contra D :=
  let q := fresh "q" in let TR := fresh "TR" in
  destruct D as [q TR];
  unfold dormant, init, ovWait, ovReady, switchCurr, tfsCurr, ovAbort in TR;
  repeat (match goal with [T : stepDiscProc _ _ _ |- _] =>
    inversion T; clear T; subst end).

(* Given P : liftEntNet X i n with X one of ovWait/ovReady/init (entity level),
   and B : liftEntNet Y i n with Y one of switchCurr/ovAbort/tfsCurr, derive False. *)
Ltac ovWait_ovReady_nextMode_net_netdisj P B :=
  let e := fresh "e" in let P1 := fresh "P1" in let P2 := fresh "P2" in
  let e' := fresh "e'" in let B1 := fresh "B1" in let B2 := fresh "B2" in
  let PP := fresh "PP" in let PS := fresh "PS" in
  let BB := fresh "BB" in let QS := fresh "QS" in
  let D := fresh "D" in let D' := fresh "D'" in
  inversion P as [e P1 P2]; clear P; inversion B as [e' B1 B2]; clear B;
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption); subst e';
  inversion P1 as [? ? ? ? PP]; subst; clear P1;
  inversion PP as [? ? ? PS]; subst; clear PP;
  inversion B1 as [? ? ? ? BB]; subst; clear B1;
  inversion BB as [? ? ? QS]; subst; clear BB;
  first [ lets D : switchCurr_mCurr_out QS
        | lets D : ovAbort_stable_out QS
        | lets D : tfsCurr_mCurr_out QS ];
  lets D' : bisim_dae PS D;
  ovWait_ovReady_nextMode_net_dae_contra D'.
(* PROOF *)
Proof.
  intros U. revert m t x y l.
  induction U as [n0 INIT | n0 n1 a U IH ST | n0 n1 d U IH ST];
    intros m t x y l V.
  - exfalso. destruct V as [V|V]; inversion V as [e V1 V2]; subst;
    lets IE : initialNet_ent INIT V2;
    inversion V1 as [? ? ? ? PP]; subst;
    inversion PP as [? ? ? PS]; subst;
    inversion IE as [? ? ? ? IP FS]; subst;
    inversion IP; subst;
    lets D : (dormant_mNext_in dormant m (ComhCoq.ProcEquiv.bisim_refl dormant));
    lets D' : bisim_dae PS D;
    ovWait_ovReady_nextMode_net_dae_contra D'.
  - assert (PREV : (exists t0 x0 y0, ovWaitStateNet m t0 x0 y0 i n0) \/
      (exists t0 l0, ovReadyStateNet m t0 l0 i n0) \/ initStateNet m i n0).
    { destruct V as [V|V].
      - lets P : ovWait_prev_net_strong V ST. destruct P as [P|[[t0 [l0 P]]|P]].
        + left. exists t x y. exact P.
        + right. left. exists t0 l0. exact P.
        + right. right. exact P.
      - lets P : ovReady_prev_net_strong V ST. destruct P as [P|[x0 [y0 P]]].
        + right. left. exists t l. exact P.
        + left. exists t x0 y0. exact P. }
    assert (NM : nextModeNet m i n0).
    { destruct PREV as [[t0 [x0 [y0 P]]]|[[t0 [l0 P]]|P]].
      - apply (IH m t0 x0 y0 l). left. exact P.
      - apply (IH m t0 x y l0). right. exact P.
      - eapply init_nextMode_net; eassumption. }
    eapply nextMode_pres_fwd_net; [exact U | exact NM | | exact ST].
    intro B. destruct PREV as [[t0 [x0 [y0 P]]]|[[t0 [l0 P]]|P]];
    destruct B as [B|[B|B]]; ovWait_ovReady_nextMode_net_netdisj P B.
  - destruct V as [V|V].
    + lets P : ovWait_del_pres_bkwd_net_strong ST V.
      eapply nextModeNet_del_pres; [exact ST | ].
      eapply (IH m t _ _ l). left. exact P.
    + lets P : ovReady_del_pres_bkwd_net ST V.
      eapply nextModeNet_del_pres; [exact ST | ].
      apply (IH m t x y l). right. exact P.
Qed.
