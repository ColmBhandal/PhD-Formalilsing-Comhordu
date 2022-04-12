(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import Program.Equality.
Add LoadPath "Extras".
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs. 
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults. 
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.ProtAuxResults.

Lemma state_disj_paused_notifAbort i n :
  pausedStateNet i n -> notifAbortPathNet i n -> False. Admitted. (*#state-pred-elim*)

Lemma state_disj_tfsCurr_start : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsStartStateNet i n -> False. Admitted. (*#state-pred-elim*)

Lemma state_disj_tfsCurr_bc : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsBcStateNet i n -> False. Admitted. (*#state-pred-elim*)

Lemma state_disj_tfsCurr_switchListen : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> switchListenStateNet i n -> False. Admitted. (*#state-pred-elim*)

(*The following string of results should be provable by lifting inter-component
relationships. Except the one with nextSince, not so sure there.*)
Lemma init_nextMode_net m i n :
  initStateNet m i n -> nextModeNet m i n. Admitted. (*4*)
(*+*)
Lemma ovWait_ovReady_nextMode_net i n (p : reachableNet n) :
  (forall m t x y, ovWaitStateNet m t x y i n ->
   nextModeNet m i n) /\
  (forall m t l, ovReadyStateNet m t l i n -> nextModeNet m i n).
  Admitted. (*4*)
(*+*)
Lemma switchBc_nextMode_net m i n :
  switchBcStateNet m i n -> nextModeNet m i n. Admitted. (*4*)
(*+*)
Lemma switchCurr_nextSince_nextMode_net m t i n p :
  nextSince m t i n p ->
  switchCurrStateNet i n -> nextModeNet m i n. Admitted. (*4*)

Lemma nextSince_switchBc_modeEq m m' t i n p :
  nextSince m t i n p -> switchBcStateNet m' i n -> m = m'.
(*Proof: Inudction nextSince, eliminate all non-matching state predicates.*)
  Admitted. (*4*)

Lemma nextSince_ovWait_modeEq m m' t t' x y i n p :
  nextSince m t i n p -> ovWaitStateNet m' t' x y i n -> m = m'.
(*Proof: Inudction nextSince, eliminate all non-matching state predicates.*)
  Admitted. (*4*)
(*+PROBABLY NEED TO PROVE THESE TOGETHER FROM A MASTER "MUTUAL" RESULT+*)
Lemma nextSince_ovReaddy_modeEq m m' t t' l i n p :
  nextSince m t i n p -> ovReadyStateNet m' t' l i n -> m = m'.
(*Proof: Inudction nextSince, eliminate all non-matching state predicates.*)
  Admitted. (*4*)

(*If an entity is tfs m, then it is in some tfsState.*)
Theorem tfs_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : tfs m t i n p -> tfsStateNet i n .
  intros.
  (*Induction on tfs.*)
  induction H.
  (*Base case can be shown by tfsStateNet constructor.*)
  invertClear H. econstructor;[ |apply H2]. invertClear H1.
  constructor. invertClear H. repeat constructor.
  (*assumption.
  (*Discrete inductive case follows from definition of tfs.*)
  assumption.
  (*Delay constructor follows from standard result (...del_pres_tfsState...) that
  delay preserves the tfsState predicate.*)
  erewrite <- tfsState_del_pres_net. apply IHtfs. apply w. Qed.*)
  Admitted. (*R*)

(*The tfs relation is at zero time when in the state tfsStart.*)
Lemma tfsStart_tfs_zero : forall (n : Network) (t : Time)
  (i : nat) (m : Mode) (p : reachableNet n),
  tfs m t i n p -> tfsStartStateNet i n -> t = zeroTime.
(*Proof: Similar to tfsNext_tfs_zero except can eliminate the backtrack
case because it implies the previous state is not tfs.*)
  intros. induction p. initNet_contra H0.
(*Discrete inductive case.*)
  dependent destruction H. reflexivity. 
  (*
  lets TPN : tfsStart_prev_net H1 s. elim_intro TPN TS OW.
  apply IHp; assumption. decompEx4 OW m' t' x y OW.
  apply tfs_rel_state in H. apply tfsState_elim_net in H.
  elimOr5 H TFS; try state_pred_elim_net OW TFS. invertClearAs2 TFS m'' TFS'.
  state_pred_elim_net OW TFS'.
(*Timed case: Follows from delay preservation of tfsStart and contraction
because tfsStart is urgent.*)
  lets DPT : del_pres_bkwd_tfsStart s H0.
  lets TU : tfsStart_urgent_net DPT s. inversion TU. Qed.*)
  Admitted. (*R*)

(*The tfs relation is at zero time when in the state tfsNext.*)
Lemma tfsNext_tfs_zero : forall (n : Network) (t : Time)
  (i : nat) (m : Mode) (p : reachableNet n),
  tfs m t i n p -> tfsNextStateNet m i n -> t = zeroTime.
  intros. induction p. initNet_contra H0.
  (*
  assert (tfs m t i n p) as TFP. dependent destruction H.
  state_pred_elim_net H H1. assumption.
  lets TPN : tfsNext_prev_net H0 s. elim_intro TPN TN TS.
  apply IHp; assumption.
  eapply tfsStart_tfs_zero. apply TFP. assumption.
(*Timed case: Follows delay preservation of tfsNext and contraction
because tfsNext is urgent.*)
  lets DPT : del_pres_bkwd_tfsNext s H0.
  lets TU : tfsNext_urgent_net DPT s. inversion TU. Qed.*)
  Admitted. (*R*)
  
Lemma currModeNet_switch_states n n' a m m' i :
  reachableNet n -> n -NA- a -NA> n' -> currModeNet m i n ->
  currModeNet m' i n' -> m <> m' ->
  (switchCurrStateNet i n /\ switchListenStateNet i n') \/
  (tfsCurrStateNet i n /\ tfsBcStateNet i n'). Admitted. (*3*)
(*Proof: First of all use a tactic to generate the entities and the entity level
predicates, then do brute force elimination on these using a tactic leaving only
the desirable cases. Finally map the entity level results back up to the network
level using a tactic- netState_auto_tac or some variant?*)

(*tfs and tfsNext state simultaneously mean the mode parameters coincide*)
Lemma tfsNext_tfs_mode_eq : forall (n : Network) (t : Time)
  (i : nat) (m1 m2 : Mode) (p : reachableNet n),
  tfs m1 t i n p -> tfsNextStateNet m2 i n -> m1 = m2. 
(**Proof: Induction on tfs. Base case fails by state pred elim with tfsNext. Discrete inductive
case can use back-tracking to show that the previous state was either tfsStart or tfsNext. In the former
case, we use an auxiliary theorem (...write it...) like this one except instead of tfsNextStateNet m2 i n we
have tfsStartStateNet i n  and currModeNet m2. In the latter case, as in the delay inductive case (due to delay pres),
we can just apply I.H. For the discrete case, a result currModeNet_switch_states will do (the possible states contradict
the one given) to give the mode equality for this state. In the timed case, a delay preservation result
on currModeNet suffices*)
  Admitted. (*3*)

(* If the nextSince relation holds for some m t then the entity in question
is in a nextSinceState.*)
Theorem nextSince_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : nextSince m t i n p -> nextSinceStateNet i n. 
  (*Induction on nextSince.*)
  intro U. induction U.
  (*The base case follows because ovWaitStateNet m t' x y i n' is a nextSinceStateNet.*)
  netprottrip H1 U q l0 h k.
  dofirst4 econstructor. apply U0. apply U.
  (*The discrete inductive case follows immediately from the definition of nextSince.*)
  assumption.
  (*The delay case follows by applying I.H. to the previous state to get nextSinceStateNet i n*)
  netprottrip IHU U q l h k.
  (*Then we show that delay preserves this state predicate
  (...del_pres_nextSinceState...).*)
  lets DX : net_del_elim U0 w. decompEx6 DX q' q0' q1' l' h' k' DE.
  andflat Q. dofirst3 econstructor. eapply del_pres_nextSinceState.
  apply U1. apply Q0. apply Q. Qed.

Lemma nextSince_next : forall (m : Mode) (t : Time) (i : nat)
  (n : Network) (p : reachableNet n),
  nextSince m t i n p -> nextModeNet m i n.
(**Proof: Strtengthen the statement to replace nextSince with nextSinceState.
Then split into the different nextSinceState cases and use an aux lemma for each.*)
  intros. lets NSR : nextSince_rel_state H.
  lets NSC : nexSinceStateNet_cases NSR. 
  lets OON : ovWait_ovReady_nextMode_net i n p. andflat OON.
  elimOr4 NSC NSC; ex_flat.
(*Case 1*)
  eapply OON0. replace m with x. eassumption. symmetry.
  eapply nextSince_ovWait_modeEq; eassumption. 
(*Case 2*)
  eapply OON1. replace m with x. eassumption. symmetry.
  eapply nextSince_ovReaddy_modeEq; eassumption.
(*Case 3*)
  eapply switchBc_nextMode_net. replace m with x. eassumption. symmetry.
  eapply nextSince_switchBc_modeEq; eassumption.
(*Case 4*)
  eapply switchCurr_nextSince_nextMode_net; eassumption.
  Qed.

(*Let's say two entities e1 and e2 are separated by a distance x. If e1 has delivered
message v to radius r t time units ago, and x + 2*Smax*t <= r, then e2 has received v t time
units ago.*)
Theorem delivered_received (n : Network) (v : list Base) (t : Time) (r x : Distance)
  (i j : nat) (p : reachableNet n) (l : Position) :
  delivered ([-v, l, r-]) t i n p -> i <> j ->
  distNet i j n x -> x + 2*speedMax*t <= r -> received v t j n p.
  intros. generalize dependent x.
  (*Induction on the proof of delivered.*)
  induction H; intros.
  (*In the base case, we have that n -v_l_r_i!-> n' and t = 0. So our last hypothesis
  becomes x <= r.*)
  simpl in H1. rewrite Rmult_0_r in H2. rewrite Rplus_0_r in H2.
  (*By analysing the transition from n to n', we can see from the semantics
  that this can only happen when all entities within range of entity i input the message,
  and all others ignore.*)
  addHyp (distNet_elim i j n' x H1). decompose [ex] H. clear H. decompose [and] H4.
  clear H4. rename x0 into e1'. rename x1 into e2'.
  addHyp (link_net_ent_disc_bkwd n n' e2' j (([-v, l, r-]) /! i) w H5).
  decompExAnd H3 e2 H4 Q.
  (*By x <= r, our guy is within range. Therefore he inputs.*)
  addHyp (inRange_out_input n n' v l r x i j e2 w H4 H0 H1 H2).
  invertClear H3. invertClear H7.
  (*Therefore, by the base case of received, he receives, with time
  parameter 0, as required.*)
  eapply receivedBase. apply H4. apply H8. apply H3.
  (*In the discrete case of induction, we get that the distance x doesn't change between n and n'*)
  addHyp (disc_pres_distNet_bkwd n n' a i j x w H1).
  (*The goal the follows easily by discrete inductive case of received
  and inductive hypothesis.*)
  constructor. apply (IHdelivered H0 x);assumption.
  (*In the timed case, we have delivered v r t i n p and so we can show
  delivered v r (t + d) i n' p'*)
  remember (reachNetDel n n' d p w) as p'.
  assert (delivered ([-v, l, r-]) (t +dt+ d) i n' p'). rewrite Heqp'. constructor.
  assumption.
  (*Let's call the distance at n' x'. Then we have that dist i j n' x' and x' + 2*Smax*(t + d) <= r*)
  rename x into x'.
  (*The latter rearranges to x' + 2*Smax*t + 2*Smax*d <= r.*)
  assert (nonneg (distance x') +
  2 * nonneg speedMax * nonneg (time t) + 2 * nonneg speedMax * pos (delay d)
  <= nonneg (distance r)). rewrite Rmult_assoc in H2. simpl in H2.
  repeat rewrite Rmult_plus_distr_l in H2. rewrite <- Rplus_assoc in H2.
  repeat rewrite <- Rmult_assoc in H2. assumption.
  (*But we can also prove that x <= x' + 2*Smax*d, where dist i i' n x.*)
  addHyp (del_link_distNet_bkwd n n' d i j x' w H1). invertClear H5.
  invertClear H6.
  (*Strategically adding 2*Smax*t to each side of the inequality we get
  x + 2*Smax*t <= x' + 2*Smax*t + 2*Smax*d*)
  apply (Rplus_le_compat_r (2*speedMax*t)) in H7.
  (*Now, from a previous result, this is in turn <= r. So x + 2*Smax*t <= r.*)
  assert (x + 2 * speedMax * t <= r). eapply Rle_trans. apply H7.
  eapply Rle_trans;[ |apply H2]. apply Req_le. simpl. ring.
  (*So we have enough information now to show from the I.H. that received v t j n p.*)
  assert (received v t j n p). apply (IHdelivered H0 x); assumption.
  (*And so by the delay constructor of received, we get received v (t + d) i' n p'.*)
  rewrite Heqp'. constructor. assumption.
  (*Note: The intuition here is that e1 and e2 could have been separated by at most
  x + 2*Smax*t t time units ago, due to the separation being x now, the maximum
  relative speed being 2*Smax and the time since the message delivery being t.*) 
  Qed. 

(*The currSince relation for mode m implies that the current mode we are now in is m.*)
Theorem currSince_curr (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : currSince m t i n p -> currModeNet m i n.
  intros.
  (*Induction on currSince.*)
  induction H.
  (*Base case follows from previous results.*)
  eapply switch_states_mState; try apply w; try assumption. eapply nextSince_next. 
  apply H.
  (*The discrete inductive case is straightforward: the definition of currSince includes in
  it that the currMode is m, so the goal follows immediately.*)
  assumption.
  (*Delay doesn't change the mode state, so I.H. will do.*)
  erewrite <- currModeNet_del_pres. apply IHcurrSince. apply w. 
  Qed.

(*If an entity is tfs t in the state tfsCurrState, then there is some t' such that
the mode transition guard for that entity is t' and the sum of t and t' is at most
trans m.*)
Theorem tfs_transGuard (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : 
  tfsCurrStateNet i n -> tfs m t i n p ->
  exists t', transGuard t' i n /\ t + t' <= trans m.
  intros.
  (**Proof: Induction on tfs.*)
  induction H0.
  (*The base case fails because the state is wrong.*)
  (*First we show that there is a mode state at i in n.*)
  apply False_ind. eapply state_disj_tfsCurr_start. apply H. assumption.
  (*In the discrete inductive case, we check whether or not the previous case was
  tfsCurrStateNet.*)
  addHyp (tfsCurrNet_dec i n). invertClear H2.
  (*If it was we can apply the IH.*)
  apply IHtfs in H3. invertClear H3. rename x into t'. invertClear H2.
  (*Now we can use t' as our witness because the mode state shouldn't have changed.*)
  exists t'. split;[ |assumption].
  addHyp (transGuard_elim t' i n H3). decompose [ex] H2. rename x into m1.
  rename x0 into m2.
  (*Then we show that there must be a mode state at i in n'*)
  remember (<| m1, m2, t' |>) as k. addHyp (mState_disc_pres n n' i a k w H6).
  invertClear H5. rename x into k'.
  (*Now, either the mode states are equal or they are not.*)
  addHyp (eqDecModeState k k'). invertClear H5.
  (*If they are equal, then the tranGuard property immediately follows.*)
  eapply transGuard_intro. rewrite <- H8 in H7. rewrite Heqk in H7. apply H7.
  (*Otherwise, the mode states are not equal. So the software component must have
  been in one of two states at n', because this is the only way that the mode state
  can change. However, the cases don't match, so this case is written off with
  contradiction.*)
  apply False_ind. lets H5 : mState_switch_states p H8 w H6 H7.
  invertClear H5; invertClear H9. eapply state_disj_tfsCurr_bc. apply H.
  assumption. eapply state_disj_tfsCurr_switchListen. apply H. assumption.
  (*So now we must deal with the case where the previous state wasn't tfsCurr.
  Here we can show (...PA::tracking...) that it was tfsNext and that the transition
  was an output to the mode state of the next mode.*)
  addHyp (tfsCurrStateNet_bktrk_net n n' i a H w). invertClear H2. contradiction H3.
  decompose [ex] H4. clear H4. rename x into m1. rename x0 into mF.
  decompose [and] H2. clear H2.
  (*Now, by previous knowledge we know that the mode transition time
  is less than or equal trans m.*)
  (*Also, we know from other theorems that tfs is 0 on entering this state.
  So the bound holds.*)
  addHyp (tfsNext_tfs_mode_eq n t i m m1 p H0 H4). rewrite <- H2 in H4.
  addHyp (tfsNext_tfs_zero n t i m p H0 H4). rewrite H5. simpl.
  exists (modeTransTime m1 mF x1). rewrite Rplus_0_l.
  generalize dependent x1. rewrite <- H2. intros. split.  
  eapply transGuard_intro. apply H7. apply modeTransTime_bound.
  (*Now, for the delay inductive case, we know that delay preserves tfsCurr*)
  addHyp (tfsCurrState_del_pres_net n n' d i w). addHyp H. rewrite <- H1 in H2.
  (*So we can apply I.H. to the previous state.*)
  apply IHtfs in H2. invertClear H2. rename x into t'. invertClear H3.
  (*Then we know that the transGuard decreases and the t from
  tfs increases proportionately, and so the sum remains the same.*)
  addHyp (transGuard_del n n' d t' i w H2). invertClear H3.
  remember (minusTime t' d x) as t0. exists t0. split. assumption.
  rewrite Heqt0. eapply Rle_trans;[ |apply H4]. apply Req_le.
  simpl. ring. Qed.

  
(*If an entity is tfs m for a time of t, then this t is bounded from above by trans m.*)
Theorem tfs_bound (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : tfs m t i n p -> t <= trans m.
  intros.
  (*Induction on the proof of reachable.*)
  generalize dependent t. induction p; intros.
  (*The base case is easy because the base proof of reachability implies zero time
  which is less than any time.*)
  dependent destruction H. simpl. timeNonneg.
  (*The discrete inductive case is easy: either we have the base case of tfs, in
  which case the previous argument applies, or we just apply the I.H. and observe
  that the time hasn't changed.*)
  dependent destruction H. simpl. timeNonneg.
  apply IHp. assumption. addHyp H. rename H0 into Q.
  remember (reachNetDel n n' d p s) as p'. rewrite Heqp' in H.
  (*The timed case takes a bit more effort. First some preliminaries.*)
  dependent destruction H. simpl. timeNonneg.
  (*Now we apply (tfs_rel_state) and show that the middle software component must delay.*)
  addHyp (tfs_rel_state n m t i p H). invertClear H0. invertClear H1.
  invertClear H0. rewrite <- H4 in H3.
  addHyp (del_net_ent e i n n' d H2 s). rewrite <- H3 in H2.
  invertClear H0. rename x into e'. rewrite <- H3 in H5.
  (*Now do inversion on the tfsStates show that no time can pass for tfsListen, tfsBc,
  tfsNext and tfsStart (...EA::urgency...), contradicting the delay just shown*)
  invertClear H1.
  (*
  (*tfsStart*)
  apply False_ind. eapply tfsStartStateEnt_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*tfsNext*)
  apply False_ind. eapply tfsNext_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. apply H0.
  apply H5.
  (*tfsBc*)
  Focus 2. apply False_ind. eapply tfsBc_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*tfsListen*)
  Focus 2. apply False_ind. eapply tfsListen_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*For tfsCurr use a special result (tfs_transGuard), to give us our bound.*)
  assert (tfsCurrStateNet i n). econstructor. constructor. constructor.
  apply H0. apply H2. 
  addHyp (tfsCurrState_del_pres_net n n' d i w). addHyp H1. rewrite H6 in H7.
  clear H6. rename H7 into H6.
  addHyp (tfs_transGuard n' m (t +dt+ d) i p' H6 Q). invertClear H7.
  rename x into t'. invertClear H8. eapply Rle_trans;[ | apply H9].
  apply Rplus_le_weaken_rr. timeNonneg. apply Rle_refl. Qed.*)
  Admitted. (*R*)



(*If v is timed out and outgoing, and the parent network makes a discrete transition,
then in the resultant network, v is either still timed out and outgoing or it has just
been delivered in this instant.*)
Theorem outgoing_timeout_disc (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableNet n) (w : n -NA- a -NA> n') (v : list Base) (l : Position) :
  outgoing v zeroTime i n ->
  outgoing v zeroTime i n' \/
  exists r, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
  introz U.
  (*Case analysis on the discrete action in question*)
  destruct a.
  (*In the case of output, we further check to see if the message payload output is v.*)
  destruct m as [v' l' r'].
  (*The only case where something is in the output list of an interface and not in the
  output list of the derivative is where the action linking the states is a broadcast
  of the message in question, which gives us delivered with timestamp 0 i.e. the RHS.*)
  (*For a of type tau, input or ignore, we can show that outgoing is preserved
  (...linking theorems + theorems on timed lists...), hence the LHS. *)
  Admitted. (*3*)
(**Proof: In steps above*)

(*AMALGAMATE WITH OTHERS- cull repetitions?*)
Lemma notifAbortPathNet_urgent (i : nat) (n n' : Network) (d : Delay) :
  reachableNet n -> notifAbortPathNet i n -> n -ND- d -ND> n' -> False. Admitted. (*4*)
(**Proof: lift from...EA::urgency... #urgent-path*)

Lemma notifBadPathNet_urgent i n n' d :
  notifBadPathNet i n -> n -ND- d -ND> n' -> False. Admitted. (*4*)
(**Proof: Follows from urgency results from all underlying component states.
Urgency holds in each one because there is always a synch possible with the
mode state or the overlap component. #urgent-path*)

Lemma msgBadPathNet_urgent (n n' : Network) (d : Delay) (i : nat) :
  msgBadPathNet i n -> n -ND- d -ND> n' -> False. Admitted. (*4*)
(**Proof: Lift urgency from EA urgency result. #urgent-path*)

Lemma msgAbort_paused_disj_net (i : nat) (n : Network) :
  msgAbortPathNet i n -> pausedStateNet i n -> False.
  (*Proof: Follows directly from the definition of msgAbortPath,
  all of the cases of which are disjoint from a paused state*)
  introz U. inversion U. inversion U0. entnetuniq EN e e0.
  subst. clear H0. inversion H1. subst. inversion H; subst.
  (*
  state_pred_elim H0 H7. state_pred_elim H3 H5.
  state_pred_elim H0 H7. state_pred_elim H3 H5.
  state_pred_elim H0 H6. state_pred_elim H3 H5.
  state_pred_elim H0 H4. state_pred_elim H3 H6.
  Qed.*)
  Admitted. (*R*)

(** If we are switching from a tfs state to a non tfs state, then we cannot be currSince.*)
Lemma tfsState_not_currSince (m : Mode) (t : Time) (i : nat) (n n' : Network)
  (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
  tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p. Admitted. (*3*)
(**Proof: Well, such a switch would mean we are going from tfsListen to dormant. And we can
show in a separate result that the tfsListen state implies that we're not currSince (which
in turn is because the tfsBc state is not currSince, which again in turn is because it is
preceded by an output on mCurr to switch the mode to some fail safe mode*)

Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  msgBadPathNet i n -> currModeNet m i n ->
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w). Admitted. (*3*)
(**Proof: Decompose msgBadPath. For all cases but one, fwd-tracking gives that either the state is preserved or the next state is also on the bad path, which is the LHS. The only exception is the badOvlp state, in which case the future may be the listening state. In this case though, fwd-tracking gives that the transition was an output on bad. Now, this must be matched in order for a synch to occur, and the only possible match is from the overlap component. There are 3 states in which this listens on bad. We can eliminate tfsListen and tfsCurr because they would imply that the entity is alredy tfs, which contradicts the assumption that it was on the msgBadPath: the definition of msgBadPath dictates that an entity is not tfs. Thus the remaining case is the transition from ovWait to tfsStart, giving the base case for tfs, which is the RHS exactly.*)

(*Needs some inter-component results for its proof*)
(** With a time parameter of 0, the tfs relation is preserved*)
Lemma tfs_zero_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  tfs m zeroTime i n p ->
  tfs m zeroTime i n' (reachNetDisc n n' a p w). Admitted. (*4*)
(**Proof: A state that is tfs with 0 time parameter must be either tfsStart, tfsNext or a guarded tfsCurr. It can be shown
by tracking that the first two cases are either preserved or go to the next case, ending at tfsCurr. This in turn is then delay
guarded, because a next mode has just been written to the mode state and the state can only be left by writing mCurr to the mode
state, which is only possible when this delay expires. But since the time parameter to tfs is 0, time can't pass, and so the entity
remains stuck in this state.*)

Lemma ovWait_nextSince_time (n : Network) (m : Mode) (x y t t1: Time) (i : nat)
  (p : reachableNet n) :
  ovWaitStateNet m t x y i n -> nextSince m t1 i n p -> period m - y <= t1.
(**Proof: Induction on next since. The base case gives that y = period m,
so the LHS of the inequality is 0 and trivially true. For the discrete
inductive case, neither t1 nor y changes, and so the I.H. suffices.
For the timed inductive case, y decreases and t1 increases proportionally.
Hence both sides of the inequality increase by the same amount, which can be
cancelled, and then the I.H. is applicable.*)
  intros OW NS. generalize dependent OW. induction NS; intro OW.
  lets OWT : ovReady_wait_track_net H0 H1 w. andflat EQ.
  invertClearAs2 EQ1 pr EQM. subst. clear EQ.
  (*
  state_pred_elim_net OW H1; unique_exps; my_applys_eq (Rle_refl 0); ring.
  (*Discrete inductive case*)
  lets OWP : ovWait_prev_net OW w. elim_intro OWP OWN ORX.
  apply IHNS; assumption.
  (*Now we case analyse on whether the previous state was ovReady or init.*)
  elim_intro ORX ORS IS.
  (*In the case of ovReady, we use ovReady_wait_track_net.*)
  invertClearAs2 ORS l OR.
  lets OWT : ovReady_wait_track_net OR OW w. andflat EQ. subst.
  Rminus_refl_simpl. timeNonneg.
  (*In the case of init, we show a contradiction with nextSince.*)
  apply nextSince_rel_state in NS. apply nexSinceStateNet_cases in NS.
  or_flat; ex_flat; [ | rename H0 into H1 |
  rename H0 into H1 | rename OR0 into H1];
  (state_pred_elim H1 IS; entnetuniq2 EN n; subst;
  state_pred_elim H3 H0; state_pred_elim H5 H7;
  state_pred_elim H11 H8).
  (*Delay inductive case*)
  assert (ovWaitStateNet m t x y i n) as ODP. eapply ovWait_del_pres_net.
  apply w. assumption. eapply Rle_trans. apply IHNS. assumption.
  simpl. Rplus_le_tac. apply Rlt_le. delPos. Qed.*)
  Admitted. (*R*)

(*The mode parameter of ovWait is the same as that of the nextSince relation if both hold.*)
Lemma nextSince_ovWait_modes_eq (n : Network) (m1 m2 : Mode) (t t1 x y : Time)
  (i : nat) (p : reachableNet n) :
  ovWaitStateNet m1 t x y i n -> nextSince m2 t1 i n p -> m1 = m2. Admitted. (*3*)
(**Proof: Generalise the statement to include a similar statement about ovReadyState, then proceed by induction on nextSince. Back tracking
shows that ovReadySate and ovWaitState are predecessors to each other and so the I.H. carries forward. The base case follows directly from the
definition of nextSince.*)

Lemma bcWait_bktrk_net (n n' : Network) (m : Mode) (x : Time)
  (i : nat) (a : ActDiscNet) (p : reachableNet n) :
  bcWaitStateNet m x i n' -> n -NA- a -NA> n' ->
  bcWaitStateNet m x i n \/ (sleepingStateNet i n /\ x = zeroTime) \/
  (exists l, bcReadyStateNet m l i n /\ x = period m /\
  sent [baseMode m, basePosition l] zeroTime i n p). Admitted. (*4*)
(**Proof: Lift back tracking result.*)

Lemma msgAbortPathNet_urgent i n n' d :
  reachableNet n -> msgAbortPathNet i n -> n -ND- d -ND> n' -> False.
  intros. inversion H. link_netentdelfwd_tac e' LD.
  assert (reachableEnt e) as RE. eapply reachable_net_ent; eassumption.
  eapply msgAbortPathEnt_urgent; eassumption. Qed.
(**Proof: Synchronisation is always possible for the msgAbortPath states between the
listener component and either the position, the mode state or the overlap component.
Hence a delay would violate the noSynch property, and so cannot exist.*)

(*LOCAL TIDY*)

(** The notifBadPathNet relation can be broken down into the following cases.*)
Lemma notifBadPathNet_cases m i n :
  notifBadPathNet i n -> currModeNet m i n ->
  rangeBadStateNet m i n \/
  badOvlpStateNet i n.
  (*Proof: Similar to nexSinceStateNet_cases.*)
  intros. rename H0 into CMN. inversion H.
  inversion H0.
  apply currMode_ent_ex in CMN. ex_flat. and_flat.
  subst. entnetuniq2 EN n. subst. 
  left. eexists;[ | apply H1]. simpl.
  econstructor. assumption.
  subst. right. econstructor;[ | apply H1]. subst.
  constructor. assumption. Qed.

Lemma rangeBad_notifBad_net m i n :
  rangeBadStateNet m i n -> notifBadPathNet i n.
  Admitted. (*#notifBadNetLift #complexNetLift*)

Lemma badOvlp_notifBad_net i n :
  badOvlpStateNet i n -> notifBadPathNet i n.
  Admitted. (*#notifBadNetLift #complexNetLift*)

Lemma ovReady_nextSince_state m t l i n :
  ovReadyStateNet m t l i n -> nextSinceStateNet i n.
  Admitted. (*#complexNetLift #nextSinceStateNetLift*)

(*-LOCAL TIDY*)