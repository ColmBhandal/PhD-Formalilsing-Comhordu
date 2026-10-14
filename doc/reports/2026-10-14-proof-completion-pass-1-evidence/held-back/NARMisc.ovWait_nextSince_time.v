(* HELPERS *)
From Stdlib Require Import Lra.

Lemma ovWait_nextSince_time_initDisj q m : initState m q -> nextSinceState q -> False.
Proof.
  intros IS NS.
  assert (exists q', init m -PA- chanMCurr ;? [baseMode m] -PA> q') as [q' TR].
  { eexists. unfold init. constructor. reflexivity. }
  apply ComhCoq.ProcEquiv.bisim_symm in IS.
  destruct (bisim_disc_match _ _ _ _ IS TR) as [q1 TQ].
  destruct NS as [m' t x y H | m' t l H | m' H | m' H];
  destruct (bisim_disc_match _ _ _ _ H TQ) as [q2 T2]; clear - T2;
  [unfold ovWait in T2 | unfold ovReady in T2 | unfold switchBc in T2 | unfold switchCurr in T2];
  repeat (match goal with V : _ -PA- _ -PA> _ |- _ => inversion V; subst; clear V end).
Qed.

Lemma ovWait_nextSince_time_initDisjNet m i n :
  initStateNet m i n -> nextSinceStateNet i n -> False.
Proof.
  intros IS NS. destruct IS as [e E1 E2]. destruct NS as [e' E1' E2'].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  inversion E1 as [p l h k P]; subst.
  inversion E1' as [p' l' h' k' P']; subst.
  inversion P as [p1 p2 p3 P2]; subst.
  inversion P' as [q1 q2 q3 Q2]; subst.
  eapply ovWait_nextSince_time_initDisj; eassumption.
Qed.

(* PROOF *)
Proof.
  intros OW NS. generalize dependent y. generalize dependent x.
  generalize dependent t.
  induction NS; intros t2 x2 y2 OW.
  - (* base case *)
    match goal with H : ovReadyStateNet _ _ _ _ _ |- _ =>
      lets OWT : ovReady_wait_track_net H OW w end.
    destruct OWT as [_ [_ [_ Y]]]. subst y2. simpl. lra.
  - (* discrete inductive case *)
    lets OWP : ovWait_prev_net OW w. destruct OWP as [OWN | [[l ORS] | IS]].
    + eapply IHNS. exact OWN.
    + lets OWT : ovReady_wait_track_net ORS OW w.
      destruct OWT as [_ [_ [_ Y]]]. subst y2.
      assert (0 <= t) by timeNonneg. lra.
    + exfalso. apply nextSince_rel_state in NS.
      eapply ovWait_nextSince_time_initDisjNet; eassumption.
  - (* delay inductive case *)
    lets OB : ovWait_del_pres_bkwd_net_strong w OW. apply IHNS in OB.
    simpl in *. lra.
Qed.
