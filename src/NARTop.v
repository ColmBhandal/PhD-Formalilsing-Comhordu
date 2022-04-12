(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import Equality.

Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
(*
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.*)
Require Import ComhCoq.NetworkLanguage.
(*Require Import ComhCoq.EntAux.*)
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.EntAuxResults.

(*** Net Aux Results Imports ***)
Require Import ComhCoq.NARInsuff.
Require Import ComhCoq.NARMisc.
Require Import ComhCoq.NARMsgPosition.
Require Import ComhCoq.NAROvlpTime.

(* Let's say we can show that a network is currSince m t i n, then we can show
that the time parameter to this relation is always greater than mL + max AN trans,
which is the lower bound for the pre-sent interval.*)
Theorem currSince_lower_bound (n : Network) (t : Time) (m : Mode)
  (i : nat) (p : reachableNet n) : currSince m t i n p ->
  msgLatency + Rmax adaptNotif transMax < t.  
  (**Proof: Induction on currSince.*)
  intros. induction H.
  (*It's the base case that requires the most attention here. Well, we notice that
  the base case of currSince involves a proof of nextSince for the previous state.
  It also enforces the entity in the previous state to be in the state switchCurrState m.
  We prove elsewhere (NAROvlpTime::nextSince_switchCurr_lower) that nextSince, in this previous state,
  implies the lower bound. since the t is the same in the base case from premise to
  conclusion (passed on like a relay bat), this lower bound carries on to the t in
  currSince, and that's the base case done.*)
  apply (nextSince_switchCurr_lower n m i t p H H0).
  (*The inductive cases are the easy ones for once- because
  the parameter t to currSince is non-decreasing over these.*)
  assumption. apply Rplus_lt_weaken_rr. apply Rlt_le. delPos.
  assumption. Qed.

Lemma maxAnTrans_positive : 0 <= Rmax adaptNotif transMax.
  eapply Rle_trans;[ |apply Rmax_l]. timeNonneg. Qed.

(* If an entity has been awaiting a transition to a mode m for the past t time units,
and this t is bounded from below by mL + AN, then the entity in question has delivered
a message of <m, l0> to a sufficient radius r and l0, the position broadcast, differs
from the current position by at most Smax*t.*)
Theorem nextSince_fst_deliv_suff (n : Network) (t : Time) (m : Mode)
  (i : nat) (l : Position) (p : reachableNet n) : 
  nextSince m t i n p -> inPosNet l i n ->
  forall q : msgLatency + Rmax adaptNotif transMax < t,
  let s := (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax)
  t q maxAnTrans_positive) in
  let s' := Rlt_le msgLatency t s in
  exists l0 l1 r,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) (minusTime t msgLatency s') i n p /\ 
  sufficient m r /\ dist l l0 <= speedMax*t. 
  intros U0 U1 q. simpl.
  (*Well since mL + AN < t, then mL < t.*)
  assert (msgLatency < t) as MT. eapply Rplus_lt_weaken_lr. apply q.
  (*So by (NARMsgPosition::fst_delivered) we have that
  delivered <m, l0> r (t - mL) i n p /\ |l - l0| <= Smax*t.*)
  apply maxAnTrans_positive. lets FX : fst_delivered U0 U1 MT. decompEx3 FX l0 l1 r FD.
  decompAnd2 FD DE DI.
  (*This will do for our existential.*)
  exists l0 l1 r. splits;[my_applys_eq DE | | apply DI]. timering.
  (*So all that remains to be proven is the sufficiency of the radius r for the mode m.
  Now, again taking our inequality mL + AN < t we can easily obtain AN < t - mL.*)
  assert (adaptNotif < t - msgLatency) as AT. apply Rplus_lt_swap_ll in q.
  eapply Rle_lt_trans;[ |apply q]. apply Rmax_l.
  (*Also due to positive mL we have t - mL < t.*)
  assert (t - msgLatency < t). apply Rplus_lt_swap_rr. Rplus_lt_tac.
  apply msgLatency_positive.
  (*Hence by (deliv_next_suff) we get sufficient m r, and we're done.*)
  eapply deliv_next_suff. apply U0. apply DE. simpl. assumption. apply H.
  Qed.

(*TIDY*)

(*DELETE ON RECOMPILE*)
Lemma ovWait_del_pres_bkwd_net_strong n n' d m t x y i :
  n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
  ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n. Admitted.

Lemma init_ovWait_track_net m m' t' i x y n n' a :
  initStateNet m i n -> ovWaitStateNet m' t' x y i n' ->
  n -NA- a -NA> n' -> m = m' /\ x = t' /\ y = zeroTime.
  Admitted. (*#lift-track-net*)
(*Might prove a stronger version of this with the value of t' =
tx(m, m') + period m', where m is the current mode.*)

(*-TIDY*)

(* If we are in the wait state of the overlap component, and the y clock value is non-zero,
then a message containing the mode in question and some position was sent exactly
(period m - y) time units ago.  *)
Theorem ovWait_sent (n : Network) (m : Mode) (t x y : Time) (i : nat) (p : reachableNet n) : 
  ovWaitStateNet m t x y i n -> 0 < y ->
  exists l q,
  sent [baseMode m, basePosition l] (minusTime (period m) y q) i n p.  
  (*Induction on p.*)
  introz U. genDep2 x y. induction p; intros y U0 x U.
  (*
  (*The base case fails because we know all entities are dormant to begin with.*)
  initNet_contra U.
  (*The discrete inductive case has three major cases, which we get by applying a back
  tracking result for ovWait*)
  lets OWP : ovWait_prev_net_strong U s. or_flat.
  (*In the first case, our previous state was ovWait, in which case the I.H. and the
  discrete sent constructor will do.*)
  apply IHp in OR. ex_flat. exists x0 x1. constructor. assumption. assumption.
  (*In the ovReady case, we further have that y = period m, and the action linking
  the states is a tau consisting of output of outProc of m l*)
  ex_flat. lets ORWT : ovReady_wait_track_net H0 U s. and_flat.
  ex_flat. subst.
  (*Now we have the sent base case, because period m - period m = 0.*)
  exists x1 (Rle_refl (period m)).
  state_pred_elim H0 U. state_pred_elim H H2. subst.
  link_netentdisc_tac b. inversion H. subst. state_pred_elim H7 H5.
  subst. state_pred_elim H6 H9.
  lets OOTE : ovReady_ovWait_track_ent H H2 H9. and_flat. subst.
  ent_disc_pres_pos_tac. subst.
  assert (p0 <> p1) as PNE. unfold not. intro. subst.
  state_pred_elim H H2. subst. state_pred_elim H7 H8.
  subst. state_pred_elim H6 H11. lets TAU : procNeq_tau_net H1 H3 s PNE.
  subst. lets SB : sentBase p s H1 H3 AND0. apply SB in AND2.
  my_applys_eq AND2. apply timeEqR. simpl. ring. 
  (*The case where the previous state was init fails, because we
  get y = 0, contradicting the positivity of y from the hypothesis.*)
  lets IOT : init_ovWait_track_net OR1 U s. and_flat.
  subst. false. eapply Rle_not_lt;[ | apply U0].
  apply Rle_refl.
  (*The delay inductive case follows by delay preservation,
  an application of I.H. and then the delay constructor for sent.*)
  lets OPB : ovWait_del_pres_bkwd_net_strong s U. apply IHp in OPB.
  ex_flat.
  assert (y <= period m) as YLE. eapply Rle_trans;[ | apply x1].
  simpl. Rplus_le_tac. apply Rlt_le. delPos. exists x0 YLE.
  match goal with [U : sent ?v ?t ?i ?n p |-
  sent ?v ?t' ?i ?n' (reachNetDel ?n ?n' ?d _ _)] =>
  replace t' with (delToTime (t +dt+ d)) end.
  constructor. assumption. apply timeEqR. simpl. ring.
  eapply Rlt_trans. apply U0. simpl. Rplus_lt_tac. delPos.
  Qed.*)
  Admitted. (*R*)

(* Let's say an entity has been awaiting transition to the mode m since t time units ago.
Then for any t' < t, we can assert that a message was sent containing the mode in
question m and some position l0 within the window t' and t' + period m. We also know
that the message was sent at most t units ago.*)
Theorem nextSince_periodic_sent (n : Network) (m : Mode) (t t' : Time)
  (i : nat) (p : reachableNet n) :
  nextSince m t i n p -> t' < t ->
  exists t'' l,
  t' < (time t'') <= t' + period m /\ t'' <= t /\
  sent [baseMode m, basePosition l] t'' i n p. 
  (*The proof should resemble that of currSince_periodic_sent. Here's an illustrative
  intuitive diagram for it:
  nextSince-------------t------------
    [  period m )--------t'----------
        sent------------t''----------*)
  intros. gen t'.
  (*Induction on nextSince.*)
  induction H; intros.
  (*The base case with t = 0 fails becasue then we'd have t' < 0, which contradicts
  the non negativity of time.*)
  contradict H2. apply Rle_not_lt. simpl. timeNonneg.
  (*The discrete inductive case follows by simple application of the inductive hypothesis
  and then the discrete sent constructor.*)
  lets IH : IHnextSince H1. clear IHnextSince. decompEx2 IH t'' l W.
  andflat Y. exists t'' l. splits; try assumption. split; assumption.
  constructor. assumption.
  (*Leaving us with just the timed inductive case to solve. Here we apply
  (Misc::nextSince_rel_state) to get the possible states for nextSince.*)
  lets NR : nextSince_rel_state H.
  (*We show by (...EA::urgency...) that the only such state capable of delay is ovWait.*)
  lets ND : nextSince_del_ovWait w NR. decompEx4 ND m0 t0 x y OS. assert (m0 = m) as ME.
  eapply nextSince_ovWait_modes_eq. apply OS. apply H.
  (*We then proceed analogously to currSince_periodic_sent, case analysing on d <= t' or
  t' < d etc. only we use (ovWait_sent) in the place of (bcWait_sent).*)
  lets RO : Rle_or_lt d t'. elim_intro RO DT TD.
  (*In the former case, we can show then that t' = t'' + d for some t''.*)
  assert (exists t'', nonneg t' = (time t'') + d) as TX. apply RlePlusExistsR in DT.
  invertClearAs2 DT dt TE. decompAnd2 TE TP TL. rewrite Rplus_comm in TP.
  exists (mkTime (mknonnegreal dt TL)). apply TP. invertClearAs2 TX t'' TE.
  (*Now, we also know t' < t + d, so t'' < t*)
  assert (t'' < t) as TL. rewrite TE in H0. simpl in H0. Rplus_lt_tac.
  (*So we can apply the I.H. for t'' and the previous state*)
  apply IHnextSince in TL. clear IHnextSince. decompEx2 TL u l TA.
  andflat T.
  (*So our existential becomes u + d*)
  exists (u +dt+ d) l.
  (*Now we need to show inequality the sub-cases of our goal by a bit of algebraic manipulation*)
  splits. rewrite TE. simpl.
  split. Rplus_lt_tac. Rplus3_swap_2_3 t'' d (period m). Rplus_le_tac. simpl. Rplus_le_tac.
  (*Then apply the sent delay constructor and we're done.*)
  constructor. assumption.
  (*Now all that remains is the delay case where t' < d. Well we already know that the previous state
  was ovWait m0 t0 (x + d) (y + d). So by (ovWait_sent) we get
  sent <m, l> (period m - (x + d)) for the previous case*)
  assert (zeroTime < (delToTime (y +dt+ d))) as YD. simpl. replace 0 with (0 + 0).
  apply Rplus_le_lt_compat. timeNonneg. delPos. ring.
  lets SX : ovWait_sent p OS YD. decompEx2 SX l q SE.
  (*So for the current case our existential is period m - y*)
  assert (y <= period m0) as YL. simpl in q. eapply Rplus_le_weaken_lr.
  apply q. apply Rlt_le. delPos.
  exists (minusTime (period m0) y YL) l. simpl in q, YD. simpl. splits.
  (*And now we clean up the inequalitites.*)
  split. simpl. eapply Rlt_le_trans. apply TD. Rplus_le_tac.
  simpl. rewrite Rplus_comm. rewrite ME. 
  Rminus_plus_zero (period m) y. Rplus_le_tac. apply Rplus_le_swap_rr.
  replace 0 with (0 + 0). apply Rplus_le_compat; timeNonneg. ring.
  rewrite <- ME in H. lets ON : ovWait_nextSince_time OS H. simpl in ON.
  apply Rminus_le_swap_lr. my_applys_eq ON. ring. generalize dependent YL.
  rewrite <- ME. intro YL. lets SD : sentDel p w SE. my_applys_eq SD.
  timering. Qed.


(*If we're in the tfsBc state, then we're not currSince.*)
Theorem tfsBc_not_currSince (n : Network) (m : Mode) (t  : Time)
  (i : nat) (p : reachableNet n) :
  tfsBcStateNet i n -> currSince m t i n p -> False. Admitted. (*1*)
(**Proof: Induction on currSince. The base case fails because tfsBcState is not switchListen.
The delay case is easy because by (...backwards del pres state...) the previous state is
tfsBc also, and we just apply the I.H. to get false. The discrete case proceeds by
(...backtracking...) on tfsBcState to get that the previous state was either tfsBc state or
tfsCurr. In the former case, applying the I.H. will do. In the latter, we can show that the
current mode is no longer m. We do this by showing that the mode was m in the previous
state (currSince-curr) and then showing that the mode transition relation is anti-reflexive
& by (...tracking...) we know the action linking the states is a synch on mCurr, so the new
mode must be different to m, which contradicts the currSince discrete constructor that
required the currMode to be m.*)

(*Relates the currSince relation to the state of the broadcast software
component. In particular, if we're currSince, then the broadcast component is either
waiting to broadcast or ready to broadcast.*)
Theorem currSince_bc_state (n : Network) (m : Mode) (t : Time)
  (i : nat) (p : reachableNet n) : currSince m t i n p ->
  (exists x, bcWaitStateNet m x i n) \/
  (exists l, bcReadyStateNet m l i n). Admitted. (*1*)
(**Proof: Induction on currSince. In the base case, we have that the overlap component has
gone from switchCurr to switchListen, in which case the broadcast component can be shown to
have stayed the same (...). But in a separate result (...EA::inter_component...) we can
show that switchCurrState m implies bcWaitState m, and since the broadcast component has
not changed across the transition, we have our left disjunct to satisfy our goal. Now,
for the inductive cases, we can apply the I.H. and then do a case analysis on the previous
state.
For the bcReady state, we can show (...fwd_track...) that it is either preserved or
transitions to bcWait by a discrete transition, giving us our goal. We can also show that
is urgent, allowing us to proceed with a contradiction in the delay inductive case.
For the bcWait state, it is easy to show (...delay_pres_state...) that the delay transition
preserves this state. For the discrete transition case, we assume that our goal does not
hold towards a contradiction. Well then the broadcast component must be in the sleeping
state. Then we can show (...tracking...) that the action linking the states must be a tau,
with the broadcast component contributing an input on trans. Now, it can be shown
(...activation...) that the only state willing to output on trans is tfsBc. But we can show
elsewhere (tfsBc_not_currSince) that tfsBc implies that we are not currSince, which
contradicts the hypothesis.*)

(** If we're currSince & we can delay, then we're in the bcWait state.*)
Corollary currSince_del_bcWait (n n' : Network) (m : Mode) (t : Time)
  (i : nat) (d : Delay) (p : reachableNet n) :
  n -ND- d -ND> n' -> currSince m t i n p ->
  exists x, bcWaitStateNet m (delToTime (x +dt+ d)) i n. Admitted. (*2*)
(**Proof: Apply currSince_bc_state and then eliminate bcReady as it is urgent*)

(* If we are in the wait state of the broadcast component with time x,
and we are currSince for time t, then x <= t.*)
Theorem bcWait_currSince_time (n : Network) (m : Mode) (x t: Time)
  (i : nat) (p : reachableNet n) :
  bcWaitStateNet m x i n -> currSince m t i n p -> period m - x <= t.
  Admitted. (*2*)
(**Proof: Induction on currSince.
Base case: x = period m, so <= t is trivial.
Discrete inductive: x and t preserved so I.H. carries forth.
Delay inductive: x decreases, t increases, so I.H. is more than enough.
*)

(* If we are in the wait state of the broadcast component, and the clock value is non-zero,
then a message containing the mode in question and some position was sent exactly
(period m - x) time units ago.*)
Theorem bcWait_sent (n : Network) (m : Mode) (x : Time)
  (i : nat) (p : reachableNet n) :
  bcWaitStateNet m x i n -> zeroTime < x ->
  exists l q,
  sent [baseMode m, basePosition l] (minusTime (period m) x q) i n p.
  intros. gen x.
  (*Induction on p.*)
  induction p; intros.
  (*The base case fails because we know all entities are sleeping to begin with.*)
  false. eapply initial_not_bcWait_net. apply i0. apply H.
  (*The discrete inductive case follows from the theorem (bcWait_bktrk_net).*)
  assert (x <> zeroTime) as Q. unfold not. intro F. rewrite F in H0.
  contradiction (Rlt_irrefl zeroTime).
  lets BB : bcWait_bktrk_net p H s. decompOr3 BB W1 W2 W3.
  apply IHp in W1. decompEx2 W1 l q V. exists l q. constructor. assumption.
  assumption. andflat Y. contradiction Q. invertClearAs2 W3 l L.
  andflat Y. rewrite <- Y1. exists l (Rle_refl x). constructor. my_applys_eq Y2.
  timering.
  (*The delay inductive case follows by an application of I.H. and then the delay
  constructor for sent.*)
  lets BD : bcWaitNet_del_bkwd s H. assert (zeroTime < x +dt+ d) as ZL.
  apply Rplus_lt_weaken_rl. timeNonneg. simpl.
  delPos. lets IH : IHp BD ZL. decompEx2 IH l q SE. assert (x <= period m) as q0.
  simpl in q. eapply Rplus_le_weaken_lr. apply q. apply Rlt_le. delPos. exists l q0.
  eapply sentDel in SE. my_applys_eq SE. timering. Qed.


(* Let's say an entity has been broadcasting in the current mode m since t time units ago.
Then for any t' < t, we can assert that a message was sent containing the mode in
question m and some position l0 within the window t' and t' + period m. We also know
that the message was sent at most t units ago.*)
Theorem currSince_periodic_sent (n : Network) (m : Mode) (t t' : Time)
  (i : nat) (p : reachableNet n) :
  currSince m t i n p -> t' < t ->
  exists t'' l, t' < (time t'')  /\ t'' <= t' + period m /\ t'' <= t /\
  sent [baseMode m, basePosition l] t'' i n p. 
  (*Let us start with a little attempt at a sketch of what is to be proven:

  currSince-------------t------------
    [  period m )--------t'----------
        sent------------t''----------  

  Now we proceed by induction on currSince.*)
  intros. generalize dependent t'. induction H; intros.
  (*In the base case, we have that the previous state was nextSince. In which case we
  apply (nextSince_periodic_sent) and the discrete sent constructor and we're done.*)
  addHyp (nextSince_periodic_sent n m t t' i p H H2). decompose [ex] H3.
  rename x into t''. rename x0 into l. exists t''. exists l. decompose [and] H5.
  clear H5. repeat (split; try assumption). constructor. assumption.
  (*The discrete inductive case is easy: apply I.H. and then discrete constructor for sent.*)
  apply IHcurrSince in H1. decompose [ex] H1. clear H1. decompose [and] H3.
  clear H3. rename x into t''. rename x0 into l. exists t''. exists l.
  clear IHcurrSince. repeat (split; try assumption). constructor. assumption.
  (*Which leaves the delay Here we do a case analysis on d <= t' or t' < d.*)
  addHyp (Rle_or_lt d t'). invertClear H1.
  (*In the former case, we can show then that t' = t'' + d for some t''.*)
  assert (exists t'', nonneg t' = (time t'') + d). apply RlePlusExistsR in H2.
  invertClear H2. rename x into t''. invertClear H1. rewrite Rplus_comm in H2.
  exists (mkTime (mknonnegreal t'' H3)). apply H2. invertClear H1. rename x into t''.
  (*Now, we also know t' < t + d, so t'' < t*)
  assert (t'' < t). rewrite H3 in H0. simpl in H0. eapply Rplus_lt_reg_l in H0.
  assumption.
  (*So we can apply the I.H. for t'' and the previous state*)
  apply IHcurrSince in H1. clear IHcurrSince. decompose [ex] H1. clear H1.
  rename x into u. rename x0 into l. decompose [and] H5. clear H5.
  (*So our existential becomes u + d*)
  exists (u +dt+ d). exists l.
  (*Now we need to show inequality the sub-cases of our goal by a bit of algebraic manipulation*)
  split. rewrite H3. apply Rplus_lt_compat_r. assumption. split. rewrite Rplus_comm.
  rewrite H3. rewrite <- Rplus_assoc. apply Rplus_le_compat_r. rewrite Rplus_comm.
  assumption. split. apply Rplus_le_compat_r. assumption.
  (*Then apply the sent delay constructor and we're done.*)
  constructor. assumption.
  (*Now all that remains is the delay case where t' < d. Well we know that the previous state
  was bcWait m (x + d)*)
  addHyp (currSince_del_bcWait n n' m t i d p w H). invertClear H1.
  (*So by (bcWait_sent) we get sent <m, l> (period m - (x + d)) for the previous case*)
  assert (zeroTime < (delToTime (x +dt+ d))). simpl. replace 0 with (0 + 0).
  apply Rplus_le_lt_compat. timeNonneg. delPos. ring.
  addHyp (bcWait_sent n m (x +dt+ d) i p H3 H1). decompose [ex] H4. clear H4.
  rename x1 into Q. rename x0 into l.
  (*So for the current case our existential is period m - x*)
  assert (x <= period m). simpl in Q. eapply Rplus_le_weaken_lr. apply Q.
  apply Rlt_le. delPos. exists (minusTime (period m) x H4). exists l. split.
  (*Now since t' < d < period m - x, then t' < period m - x.*)
  eapply Rlt_le_trans. apply H2. simpl. simpl in Q. apply Rplus_le_swap_lr.
  rewrite Rplus_comm. assumption. split.
  (*But we also clearly have that period m - x <= t' + period m*)
  simpl. rewrite Rplus_comm.
  apply Rminus_le_weaken_lr. timeNonneg. apply Rplus_le_weaken_rr. timeNonneg.
  apply Rle_refl. split. simpl. addHyp (bcWait_currSince_time n m (x +dt+ d) t i p H3 H).
  simpl in H5. apply Rminus_le_swap_lr. eapply Rle_trans;[ |apply H5].
  apply Req_le. ring.
  (*So now by the delay constructor of sent, we get sent <m, l> (period m - x) for the current
  state:
  currSince-------------t------------|---------------d-------------|
                          [  period m )------------t'------------|
                             sent---(period m - x)---------------|
  and we're done.*)
  replace (minusTime (nonneg (time (period m))) (nonneg (time x)) H4)
  with (delToTime (minusTime (nonneg (time (period m)))
  (nonneg (time (delToTime (x +dt+ d)))) Q +dt+ d)).
  constructor. assumption. apply timeEqR. simpl. ring. Qed.

(*If an entity in position l is currSince m t, then it has delivered a message <m, l0>
to a sufficient radius r and this happened t - mL time units ago. Also, l0 differs from
l by at most Smax*t.*)
Theorem currSince_fst_deliv_suff (n : Network) (m : Mode) (t : Time)
  (i : nat) (l : Position) (p : reachableNet n) :
  currSince m t i n p -> inPosNet l i n ->
  exists q,
  let s := (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax) t q
  maxAnTrans_positive) in
  let s' := Rlt_le msgLatency t s in
  exists r l0 l1,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) (minusTime t msgLatency s') i n p /\ 
  sufficient m r /\ dist l l0 <= speedMax*t. 
  (*Induction on currSince.*)
  intro. generalize dependent l. induction H; intros.
  (*In the base case, we have that the previous entity was nextSince m t and in
  switchCurrState. Then by (nextSince_switchCurr_lower) we would get
  that mL + max AN trans < t.*)
  addHyp (nextSince_switchCurr_lower n m i t p H H0).
  (*From this we easily obtain mL + AN < t.*)
  assert (msgLatency + adaptNotif < t). eapply Rle_lt_trans;[ |apply H3].
  apply Rplus_le_compat. apply Rle_refl. apply Rmax_l.
  (*Also, it is clear by the discrete nature of the transition in this case that the
  position is preserved.*)
  addHyp (inPos_pres_disc n n' a l i w). rewrite <- H5 in H2.
  (*Hence by (nextSince_fst_deliv_suff) we have delivered <m, l0> r (t - mL) i n p /\ 
  sufficient m r /\ |l - l0| <= Smax*t for some r and l0.*)
  addHyp (nextSince_fst_deliv_suff n t m i l p H H2 H3). cbv zeta in H6.
  decompose [ex] H6. clear H6. rename x into l0. rename x0 into l1. rename x1 into r.
  decompose [and] H7. clear H7. exists H3. exists r. exists l0. exists l1.
  repeat (split; try assumption). 
  (*This closely resembles our goal, the only difference being the
  delivered <m, l0> r (t - mL) i n p instead of delivered <m, l0> r (t - mL) i n' p'.
  This last touch is shown by the application of the discrete delivered constructor, and
  we're done with this case.*)
  constructor. assumption.
  (*The discrete inductive case is almost identical to the base case: backwards preservation of
  position, apply I.H., apply discrete constructor on delivered.*)
  addHyp (inPos_pres_disc n n' a l i w). rewrite <- H2 in H1.
  apply IHcurrSince in H1. clear IHcurrSince. cbv zeta in H1.
  decompose [ex] H1. clear H1. rename x into q. rename x0 into r. rename x1 into l0.
  rename x2 into l1. decompose [and] H4. clear H4. exists q. exists r. exists l0. exists l1.
  repeat (split; try assumption). constructor. assumption.
  (*The delay case is a little more complicated. We apply the result (inPos_del_bound_bkwd)
  to show that the previous state was inPosNet l1 i n, for some l1 with |l - l1| <= Smax*d.*)
  addHyp (inPos_del_bound_bkwd n n' d l i H0 w). invertClear H1. rename x into l0.
  invertClear H2. 
  (*Then we apply the inductive hypothesis and tidy up a bit.*)
  apply IHcurrSince in H1. clear IHcurrSince. cbv zeta in H1. decompose [ex] H1.
  clear H1. rename x0 into r. rename x1 into l1. rename x2 into l2.
  decompose [and] H4. clear H4. 
  (*Now, we have mL + max AN trans < t, so clearly mL + max AN trans < t + d*)
  assert (msgLatency + Rmax adaptNotif transMax < t +dt+ d) as q. apply Rplus_lt_weaken_rr.
  apply Rlt_le. delPos. assumption.
  (*Now we can use this last assertion as our existential and carry on with the goal.*)
  exists q. exists r. exists l1. exists l2. split.
  (*The proof of delivered carries over by the delay delivered constructor.*)
  replace (minusTime (nonneg (time (delToTime (t +dt+ d)))) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time (delToTime (t +dt+ d))))
  (Rplus_lt_weaken_lr (nonneg (time msgLatency))
  (Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)))
  (nonneg (time (delToTime (t +dt+ d)))) q maxAnTrans_positive))) with
  (delToTime (minusTime (nonneg (time t)) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time t))
  (Rplus_lt_weaken_lr (nonneg (time msgLatency))
  (Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)))
  (nonneg (time t)) x maxAnTrans_positive)) +dt+ d)). constructor. assumption. apply timeEqR. simpl. ring.
  (*The sufficiency of the message is preserved.*)
  split. assumption.
  (*The bound on the distance then is shown by the triangle inequality. Elaborating on this last
  point, we want to show |l - l0| <= Smax*(t + d). We have both that |l - l1| <= Smax*d and
  |l1 - l0| <= Smax*t. The triangle inequality also gives us
  that |l - l0| <= |l - l1| + |l1 - l0|. So we get our result by adding the inequalities
  and transitivity.*)
  eapply Rle_trans. eapply dist_tri_ineq. simpl. rewrite Rmult_plus_distr_l.
  rewrite Rplus_comm. apply Rplus_le_compat. apply H6. rewrite distSymmetric in H3.
  apply H3. Qed.

(*If an entity in position l is currSince m t, then it has delivered a message <m, l0> to a
sufficient radius r and this happened t' time units ago, with t' < t in the pre delivery
interval of m and the distance between the sent position and the current position being no
more than Smax*(mL + t').*)
Theorem pre_del_suff (n : Network) (m : Mode) (t : Time)
  (i : nat) (l : Position) (p : reachableNet n) :
  currSince m t i n p -> inPosNet l i n -> ~failSafe m ->
  exists t' r l0 l1,
  delivered ([-[baseMode m, basePosition l0], l1, r-]) t' i n p /\ 
  sufficient m r /\ t' [:] (preDeliveredInterval m) /\ t' < t /\
  dist l l0 <= speedMax*(msgLatency+ t'). intros.
  match goal with [ H : ~failSafe m |- _ ] => rename H into Q end.
  (*Let us first recall the definition of
  Ipd = (max AN trans, max AN trans + period m + trans m]).*)  
  remember (preDeliveredInterval m) as h. unfold preDeliveredInterval in Heqh.
  (*Let u = mL + max AN trans + period m + trans m. Then we can do a case analysis on
  t <= u or u < t.*)
  remember (msgLatency + Rmax adaptNotif transMax + period m + trans m) as u.
  addHyp (Rle_or_le t u). invertClear H1.
  (*Case t <= u: Well, we can show by (currSince_fst_deliv_suff) that there is a sufficient
  message delivered at t' = t - mL and some position l0 is sent in that message such
  that |l - l0| <= Smax*(mL + t').*)
  addHyp (currSince_fst_deliv_suff n m t i l p H H0). simpl in H1. decompose [ex] H1.
  clear H1. decompose [and] H4. clear H4. rename x0 into r. rename x1 into l0.
  rename x2 into l1. remember (minusTime t msgLatency (Rlt_le msgLatency t
  (Rplus_lt_weaken_lr msgLatency (Rmax adaptNotif transMax) t x maxAnTrans_positive)))
  as t'.
  foldDist l l0 H6. assert (nonneg t = t' + msgLatency). rewrite Heqt'. simpl. ring.
  rewrite H3 in H6. rewrite Rplus_comm in H6.
  (*By the positivity of mL, it is easy to show t' < t.*)
  assert (t' < t). rewrite H3. apply Rlt_plus_r.
  apply msgLatency_positive.
  (*So now we can apply t', r, l0, and l1 as our existential witnesses and it just
  remains to show that t' : Ipd m.*)
  exists t' r l0 l1. split. assumption. split. assumption. split;[ |split;assumption].
  rewrite Heqh. replace (nonneg (time t')) with (nonneg (time t') +
  nonneg (time msgLatency) - nonneg (time msgLatency));[ | ring]. split.
  (*Well, since by (currSince_lower_bound) we have that mL + max AN trans < t,
  then max AN trans < t - mL = t', which is our lower bound done.*)
  addHyp (currSince_lower_bound n t m i p H). apply Rplus_lt_swap_ll in H7.
  rewrite H3 in H7. simpl. assumption.
  (*Also, since t <= u = mL + max AN trans + period m + trans m, then
  t - mL <= max AN trans + period m + trans m,which is our upper bound done.
  Case closed.*)
  simpl. rewrite Hequ in H2. rewrite Rplus_assoc in H2. rewrite Rplus_assoc in H2.
  apply Rplus_le_swap_rl in H2. rewrite H3 in H2. rewrite Rplus_assoc. assumption.
  (*Case u < t. Well we can easily show mL + max AN trans + trans m < t.
  We show this by transitivity via u*)
  assert (nonneg (time msgLatency) +
  Rmax (nonneg (time adaptNotif)) (nonneg (time transMax)) + nonneg (time (trans m)) < t).
  eapply Rlt_le_trans;[ |apply H2]. rewrite Hequ. apply Rplus_lt_compat_r.
  rewrite Rplus_assoc. repeat (apply Rplus_lt_compat_l). apply Rlt_plus_r.
  apply period_positive.
  (*so by (currSince_periodic_sent) we have that there was a sent message <m, l0> at a time
  t' within the window (mL + max AN trans + trans m, mL + max AN trans + period m + trans m]
  and t' <= t ($).*)
  remember (msgLatency +t+ (timeMax adaptNotif transMax) +t+ trans m) as w.
  assert (nonneg (time msgLatency) + Rmax (nonneg (time adaptNotif))
  (nonneg (time transMax)) + nonneg (time (trans m)) =
  nonneg ((msgLatency +t+ timeMax adaptNotif transMax) +t+ trans m)). simpl.
  ring. rewrite H3 in H1. rewrite <- Heqw in H1.
  addHyp (currSince_periodic_sent n m t w i p H H1). decompose [ex] H4.
  clear H4. decompose [and] H6. clear H6. rename x0 into l0. rename x into t'.
  assert (t' <= u). rewrite Hequ. eapply Rle_trans. apply H7. rewrite Heqw.
  rewrite <- H3. rewrite Rplus_assoc. rewrite Rplus_comm. rewrite Rplus_assoc.
  rewrite Rplus_comm. apply Rplus_le_compat_r. rewrite Rplus_comm. apply Rle_refl.
  rewrite Hequ in H6.
  (*By (sent-pos_bound) we can establish that |l - l0| <= Smax*t' (@).*)
  addHyp (sent_pos_bound n m t' i l l0 p H9 H0).
  (*Then by (sent_delivered) we know that this message was delivered to some radius r
  at time t'' = t' - mL ($$)*)
  assert (msgLatency < t'). eapply Rle_lt_trans;[ |apply H4]. rewrite Heqw.
  rewrite <- H3. rewrite Rplus_assoc. apply Rle_plus_r. apply Rle_zero_plus.
  rewrite <- timeMax_RMax. timeNonneg.
  timeNonneg.
  addHyp (sent_delivered n [baseMode m, basePosition l0] t' i p H9 H10).
  decompose [ex] H11. clear H11. rename x0 into l1. rename x into r. 
  remember (minusTime (nonneg (time t')) (nonneg (time msgLatency))
  (Rlt_le (nonneg (time msgLatency)) (nonneg (time t')) H10)) as t''.
  (*We can show that t'' is within the window
  (max AN trans + trans m, max AN trans + period m + trans m]) (@@)*)
  assert ((Rmax adaptNotif transMax) + trans m < t'').
  rewrite Heqt''. simpl. apply Rplus_lt_swap_ll. rewrite <- Rplus_assoc.
  rewrite H3. rewrite <- Heqw. assumption. 
  assert (t'' <= (Rmax adaptNotif transMax) + period m + trans m).
  rewrite Heqt''. simpl. apply Rplus_le_swap_rl. repeat rewrite <- Rplus_assoc.
  assumption.
  (*It is clear then that t'' is also within the window Ipd m, since the window
  mentioned above is contained within Ipd m*)
  assert (t'' [:] preDeliveredInterval m). split;simpl.
  eapply Rle_lt_trans;[ | apply H11]. apply Rle_plus_r. timeNonneg.
  assumption.
  (*Now, since from ($) t' <= t, then t'' < t, by ($$) and the
  positivity of mL*)
  assert (t'' < t). rewrite Heqt''. simpl. eapply Rlt_le_trans;[ |apply H5].
  apply Rplus_lt_swap_rr. apply Rlt_plus_r. apply msgLatency_positive.
  (*Also, rearranging ($$) we get t' = mL + t''*)
  assert (nonneg t' = msgLatency + t''). rewrite Heqt''. simpl. ring.
  (*Substituting into our earlier result (@) we get |l - l0| <= Smax*(mL + t'').*)
  rewrite H16 in H8.
  (*Now let's apply t'', r, l0 and l1 as our existential witnesses and prune the goal.*)
  exists t'' r l0 l1. rewrite Heqh. repeat (split;try assumption).
  (*We have now shown every sub-goal except the sufficiency of the delivered message.
  It can be shown that the coverage r must be sufficient for the mode m by assuming
  otherwise and proving a contradiction.*)
  addHyp (suffDec m r). appDisj H17. assumption. 
  (*Well, it is clear from (@@) that AN < t''*)
  assert (adaptNotif < t''). eapply Rle_lt_trans;[ |apply H11].
  apply Rplus_le_weaken_rr. timeNonneg. apply Rmax_l.
  (*We have already shown that t'' < t so by (NARInsuff::insuff_react), we get that
  we are tfs m (t'' - AN).*)
  addHyp (insuff_react n m l0 l1 r t t'' i p H H13 H17 H15 n0 Q).
  (*Now, by (tfs_bound), this would imply t'' - AN <= trans m.*)
  decompExAnd H18 x LT TF. lets TB : tfs_bound TF.
  assert (minusTime t'' adaptNotif (Rlt_le adaptNotif t'' H17) <= trans m) as C1.
  eapply Rle_trans. apply LT. assumption.
  (*However, we also have by (@@) that max AN trans + trans m < t'' and so
  AN + trans m < t''*)
  assert (adaptNotif + trans m < t''). eapply Rle_lt_trans;[ |apply H11].
  apply Rplus_le_compat_r. apply Rmax_l.
  (*and so trans m < t'' - AN.*)
  simpl in C1. apply Rplus_lt_swap_ll in H18.
  (*Hence we arrive at a contradiction, which is that t'' - AN < t'' - AN*)
  apply False_ind. apply (Rlt_irrefl (t'' - adaptNotif)). eapply Rle_lt_trans.
  apply C1. assumption. Qed.
  (*So we must accept that the broadcast range was sufficient. This concludes the proof of
  all our sub-goals.*)