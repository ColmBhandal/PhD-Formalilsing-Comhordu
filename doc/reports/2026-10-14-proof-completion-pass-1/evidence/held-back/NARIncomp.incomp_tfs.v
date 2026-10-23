(* HELPERS *)
From Stdlib Require Import Lra.
(* PROOF *)
Proof.
 intros.
  (*We first need to show that speedMax * t is less than possIncDist m m' in order
  to be able to apply a special equivalence result later for our (annoying!)
  subNonnegTot function.*)
  assert (speedMax * t' < possIncDist m m') as TLP. eapply Rle_lt_trans;
  [ | apply H4]. Rplus_le_tac. apply cond_nonneg.  
  (*And then we're back to our proof, which goes smoothly let's hope!*)
  generalize dependent t. generalize dependent l.
  induction H1; intros; rename t into t'.
  contradict H2. apply Rlt_irrefl.
  (*The discrete inductive case carries over easily.*)
  (*First we notice that position is preserved*)
  assert (inPosNet l i n). erewrite inPos_pres_disc. apply H0. apply w.
  (*Now we backtrack from currSince and first eliminate the nextSince case.*)
  dependent destruction H. apply False_ind. eapply incomp_abort. apply H.
  apply H7. apply H1. assumption. assumption. assumption.
  (*Then we show the currSince case to hold*)
  addHyp (IHreceived H2 TLP l H6 H4 t H H5). clear IHreceived. 
  constructor. assumption. apply tfs_rel_state in H7. addHyp (tfsStateNet_dec i n').
  appDisj H8. apply False_ind. eapply tfsState_not_currSince. apply w.
  apply H7. assumption. apply H.
  (*Now for the timed case. We first observe that currSince carries to the previous
  state because it is preserved backwards by delay*)
  dependent destruction H. 
  (*We then split our reasoning into two cases. One where in the previous case
  t', the parameter to received is non-zero, the other where it is 0.*)
  assert (0 <= t'). timeNonneg. apply Rle_lt_or_eq_dec in H5.
  invertClear H5.
  (*If t' is non zero, we must look at the old position, call it l1. Now we know by
  [pos_bound salvaged?] that |l1 - l| <= Smax*d (star).*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). decompose [ex] H5. clear H5.
  rename x into l1. invertClear H7. 
  (*Then from the (triangle inequality) we have that |l1 - l'| <= |l1 - l| + |l - l'|.
  (&&)*)
  addHyp (dist_tri_ineq l1 l l').
  (*But from our assumption we have that |l - l'| - Smax*mL + Smax*(t' + d) < Dpi m m'.
  Adding this to (star) we get
  |l1 - l| + |l - l'| - Smax*mL + Smax*(t' + d) < Dpi m m' + Smax*d.*)
  (*Convert H4 from subNonnegTot to Rminus*)
  apply subNonnegTot_plus_lt_Rminus in H4.
  addHyp (Rplus_le_lt_compat (dist2d l1 l) (speedMax * d)
  (dist2d l l' - speedMax * msgLatency + speedMax * (t' +dt+ d))
  (possIncDist m m') H8 H4).
  (*A bit of algebra allows us to cancel the Smax*d on both sides, giving
  |l1 - l| + |l - l'| - Smax*mL + Smax*t' < Dpi m m' (@).*)
  replace (nonneg (dist2d l1 l) +
  (nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * pos (delay (t' +dt+ d)))) with (nonneg (dist2d l1 l) +
  nonneg (dist2d l l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * (nonneg t') + nonneg speedMax * pos(delay d)) in H9;
  [ |simpl;ring]. replace (nonneg speedMax * pos (delay d) + possIncDist m m')
  with (possIncDist m m' + nonneg speedMax * pos (delay d)) in H9;[ |ring].
  apply Rplus_lt_reg_r in H9.
  (*Then adding - Smax*mL + Smax*t' to (&&) we get
  |l1 - l'| - Smax*mL + Smax*t' <= |l1 - l| + |l - l'| - Smax*mL + Smax*t'.*)
  apply (Rplus_le_compat_r (-speedMax*msgLatency + speedMax*t')) in H7.
  (*By transitivity on (@) then we have |l1 - l'| - Smax*mL + Smax*t' < Dpi m m'.*)
  assert (nonneg (dist2d l1 l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t') < possIncDist m m'). eapply Rle_lt_trans.
  eapply Rle_trans;[ | apply H7]. apply Req_le. ring.
  eapply Rle_lt_trans;[ | apply H9]. apply Req_le. ring.
  (*Now we can apply the I.H. yielding tfs m t' i n p, which by application of the
  tfs delay constructor gives the required tfs m (t' + d) i n p.*)
  constructor. apply IHreceived with (t := t) (l := l1); try assumption. 
  (*The remaining side conditions are simple real arithmetic: Smax*t' < Dpi m m' follows
  from Smax*(t' + d) < Dpi m m', the -nn- inequality is H10, and t' < t follows from
  t' + d < t + d.*)
  assert (0 <= speedMax * d) as SD. apply Rmult_le_pos. apply cond_nonneg. apply Rlt_le. delPos.
  simpl in TLP. simpl in SD. simpl. nra.
  apply Rminus_plus_lt_subNonnegTot.
  assert (0 <= speedMax * d) as SD. apply Rmult_le_pos. apply cond_nonneg. apply Rlt_le. delPos.
  simpl in TLP. simpl in SD. simpl. nra. assumption.
  simpl in H3. lra.
  (*We are then left with the case where t' = 0. Now, by the same argument as
  before involving the (triangle inequality), we have that
  |l1 - l'| - Smax*mL + Smax*t' < Dpi m m'*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). decompose [ex] H5. clear H5.
  rename x into l1. invertClear H7. 
  addHyp (dist_tri_ineq l1 l l').
  (*Here we use a special result to convert the niggly -nn- and make it a nice
  normal -.*)
  apply subNonnegTot_plus_lt_Rminus in H4.
  (*Adding the triangle inequality and the bound Smax*d on the movement, the Smax*d
  terms cancel, giving |l1 - l'| - Smax*mL + Smax*t' < Dpi m m'.*)
  assert (nonneg (dist2d l1 l') - nonneg speedMax * nonneg (time msgLatency) +
  nonneg speedMax * nonneg (time t') < possIncDist m m') as H10.
  clear - H4 H7 H8. destruct d as [[dd DP]]. simpl in *. lra.
  (*Now, with t' = 0 this gives us |l1 - l'| - Smax*mL < Dpi m m'.*)
  rewrite <- H6 in H10. rewrite Rmult_0_r in H10. rewrite Rplus_0_r in H10.
  (*Also by (@@) we have currSince for the previous state. From here we can
  apply (instant-incomp-tfs) to get incomingNet <m', l'> i n  \/
  msgBadPath <m', l'> i n \/ tfs m 0 i n p.*)
  symmetry in H6. apply timeZero in H6. rewrite H6 in H1.
  assert (0 < t) as U. simpl in H3. apply Rplus_lt_reg_r in H3.
  eapply Rle_lt_trans;[ |apply H3]. timeNonneg.
  (*Some stuff to get rid of annoying -nn-*)
  assert (0 < possIncDist m m') as ZPD. eapply Rle_lt_trans; [ | apply TLP].
  apply Rmult_le_pos. apply cond_nonneg. simpl. replace 0 with (0 + 0).
  apply Rplus_le_compat. timeNonneg. apply Rlt_le. delPos. ring.
  lets RLS : Rminus_lt_subNonnegTot ZPD.
  rewrite <- multNonneg_Rmult_eq in H10. apply RLS in H10.
  (*Back to the main proof.*)
  pose proof (instant_incomp_tfs n t l1 l' i m m' p H H5 U H1 H10) as IIT.
  destruct IIT as [IN | [MB | TF]].
  (*The first two disjuncts fail because it can be shown that delay is
  impossible in these cases (incomingNet-urgent), (...EA::msgBadPath-urgent...).*)
  apply False_ind. eapply incomingNet_urgent. apply p. apply IN. apply w.
  apply False_ind. eapply msgBadPathNet_urgent. apply MB. apply w.
  (*Which leaves us with tfs m 0 i n p, and we can proceed immediately from this to
  our goal by one application of the tfs delay constructor.*)
  rewrite H6. constructor. assumption. Qed.
