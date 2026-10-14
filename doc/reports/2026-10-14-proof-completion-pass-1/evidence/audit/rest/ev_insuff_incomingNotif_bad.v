(* HELPERS *)
From Stdlib Require Import Lra.

(* Counterexample: without reachability, the entity's process can be an arbitrary
   term that consumes the zero-stamped notification on chanAN and then becomes nil. *)
Lemma insuff_incomingNotif_bad_cex (m : Mode) :
  ~ (forall (n n' : Network) (a : ActDiscNet) (m : Mode)
      (r : Distance) (l : Position) (i : nat),
      currModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
      incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
      incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
      notifBadPathNet i n').
Proof.
  intro H.
  assert (TR : inPrefix chanAN [vR, vM'', vL] nilProc -PA-
    chanAN ;? [baseDistance (mkDistance zeroNonneg), baseMode m,
    basePosition (mkPosition 0 0)] -PA> nilProc).
  { refine (stepDpIn chanAN [baseDistance (mkDistance zeroNonneg), baseMode m,
    basePosition (mkPosition 0 0)] [vR, vM'', vL] nilProc _). reflexivity. }
  assert (TI : mkInterface (mkInputList []) (mkOutputList [])
      (mkNotifList [<([baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)], zeroTime)>]) -i-
      chanAN {! [baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)] -i>
      mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  { apply stepIntFwdNotif. apply stepNlLift. apply stepTlFwdHd. }
  lets TE : stepDeNotif (mkPosition 0 0) (sing m) TR TI.
  lets W : stepDnTauHead (@nil Entity) TE.
  pose proof (currMode_intro m
    ([|inPrefix chanAN [vR, vM'', vL] nilProc, mkPosition 0 0,
      mkInterface (mkInputList []) (mkOutputList [])
      (mkNotifList [<([baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)], zeroTime)>]), sing m|]) 0
    ([|inPrefix chanAN [vR, vM'', vL] nilProc, mkPosition 0 0,
      mkInterface (mkInputList []) (mkOutputList [])
      (mkNotifList [<([baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)], zeroTime)>]), sing m|] :: nil)
    eq_refl (einConsLeft _ _)) as CM.
  assert (NS : ~ sufficient m (mkDistance zeroNonneg)).
  { intro S. unfold sufficient in S. simpl in S.
    pose proof (cond_nonneg (distance (maxMinDistComp m))).
    pose proof speedMax_pos. pose proof adaptNotif_positive.
    pose proof (period_positive m). pose proof (cond_nonneg (time (trans m))).
    pose proof (Rmax_l adaptNotif transMax).
    assert (0 < Rmax adaptNotif transMax + period m + trans m) by lra.
    assert (0 < speedMax * (Rmax adaptNotif transMax + period m + trans m))
      by (apply Rmult_lt_0_compat; lra).
    lra. }
  assert (IN : incomingNetNotif [baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)] zeroTime 0
    ([|inPrefix chanAN [vR, vM'', vL] nilProc, mkPosition 0 0,
      mkInterface (mkInputList []) (mkOutputList [])
      (mkNotifList [<([baseDistance (mkDistance zeroNonneg), baseMode m,
      basePosition (mkPosition 0 0)], zeroTime)>]), sing m|] :: nil)).
  { econstructor. apply einConsLeft. simpl. left. reflexivity. }
  lets D : H W NS IN. apply CM.
  destruct D as [D | D].
  - inversion D as [p0 l0 li0 lo0 ln0 k0 EIN INL].
    inversion EIN; subst. simpl in INL. exact INL.
  - inversion D as [e0 NB EIN]. inversion EIN; subst.
    inversion NB; subst;
    match goal with Q : _ nilProc |- _ => inversion Q end.
Qed.
(* PROOF *)
Proof.
Admitted.
