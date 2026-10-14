(* HELPERS *)
(** Two next-mode facts about the same entity coincide. *)
Lemma nextSince_ovWait_modeEq_uniq m m' i n :
  nextModeNet m i n -> nextModeNet m' i n -> m = m'.
Proof.
  intros NM NM'. apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM'. destruct NM' as [e' [EIN' NME']].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  destruct e as [p l h k].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME'.
  rewrite NME in NME'. inversion NME'. reflexivity.
Qed.

(** Across a discrete step whose target is neither switchListen nor tfsBc,
the mode state is unchanged, so next modes before and after coincide. *)
Lemma nextSince_ovWait_modeEq_mst m m0 i n n' a :
  reachableNet n -> n -NA- a -NA> n' -> nextModeNet m i n ->
  nextModeNet m0 i n' -> ~ switchListenStateNet i n' ->
  ~ tfsBcStateNet i n' -> m = m0.
Proof.
  intros RN W NM NM0 NSL NTB.
  apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM0. destruct NM0 as [e0 [EIN0 NME0]].
  destruct e as [p l h k]. destruct e0 as [p0 l0 h0 k0].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME0.
  destruct (eqDecModeState k k0) as [EQ | NEQ].
  - subst. rewrite NME in NME0. inversion NME0. reflexivity.
  - exfalso.
    assert (mState_in_net k i n) as MS by (econstructor; eassumption).
    assert (mState_in_net k0 i n') as MS0 by (econstructor; eassumption).
    lets MSS : mState_switch_states RN NEQ W MS MS0.
    destruct MSS as [[_ TB] | [_ SL]]; [apply NTB | apply NSL]; assumption.
Qed.

(** A nextSince state is neither switchListen nor tfsBc. *)
Lemma nextSince_ovWait_modeEq_nss_not i n :
  nextSinceStateNet i n -> ~ switchListenStateNet i n /\ ~ tfsBcStateNet i n.
Proof.
  intro U. inversion U as [e U1 U2]. inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP U1 U.
  split; intro V; inversion V as [e' V1 V2];
  (assert (e' = [|p1 $||$ p2 $||$ p3, l, h, k|]) as EQ
    by (eapply entInNetUnique; eassumption)); subst e';
  inversion V1; subst;
  (match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end);
  (match goal with [RS : _ p2 |- _] =>
    first [lets PU : switchListen_unpause_out RS | lets PU : tfsBc_trans_out RS];
    clear RS end);
  inversion PS; clear PS; subst;
  (match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end).
Qed.

(** nextSince m implies that the next mode is m. Proved directly by induction
on nextSince, comparing mode states across each discrete step. *)
Lemma nextSince_ovWait_modeEq_next m t i n p :
  nextSince m t i n p -> nextModeNet m i n.
Proof.
  intro NS. induction NS as [a i0 n0 n0' p0 w l t0 t0' x y PND OR OW
    | a t0 i0 n0 n0' p0 w NS IH NSS | d t0 i0 n0 n0' p0 w NS IH].
  - eapply ovWaitState_nextMode_net; [ | eassumption].
    eapply reachNetDisc; eassumption.
  - assert (reachableNet n0') as RN' by (eapply reachNetDisc; eassumption).
    lets NOT : nextSince_ovWait_modeEq_nss_not NSS. destruct NOT as [NSL NTB].
    lets NSN : nexSinceStateNet_cases NSS.
    destruct NSN as [OW | [OR | [SB | SC]]].
    + destruct OW as [m0 [t1 [x1 [y1 OW]]]].
      lets NM0 : ovWaitState_nextMode_net RN' OW.
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct OR as [m0 [t1 [l1 OR]]].
      assert (nextModeNet m0 i0 n0') as NM0.
      { eapply ComhCoq.NetAuxBasics.ovWait_ovReady_nextMode_net
          with (x := zeroTime) (y := zeroTime); [exact RN' | right; eassumption]. }
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct SB as [m0 SB].
      assert (nextModeNet m0 i0 n0') as NM0
        by (eapply switchBc_nextMode_net; eassumption).
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + eapply switchCurr_nextSince_nextMode_net; [ | eassumption].
      exact (nextSinceDisc _ _ _ _ _ _ _ w NS NSS).
  - eapply nextModeNet_del_pres; eassumption.
Qed.

(* PROOF *)
Proof.
  intros NS OW.
  lets NM : nextSince_ovWait_modeEq_next NS.
  lets NM' : ovWaitState_nextMode_net p OW.
  eapply nextSince_ovWait_modeEq_uniq; eassumption.
Qed.
