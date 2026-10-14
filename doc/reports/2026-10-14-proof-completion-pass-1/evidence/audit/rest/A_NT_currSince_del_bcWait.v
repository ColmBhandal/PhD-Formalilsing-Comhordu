(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.

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
  sufficient m r /\ dist2d l l0 <= speedMax*t. 
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


From Stdlib Require Import Lia Lra.

(** A delay from a bcWait process never yields a bcReady process: the former
keeps its willingness to input on chanTrans, which the latter lacks.*)
Local Lemma currSince_del_bcWait_aux1 m x m' l q q' d :
  bcWaitState m x q -> q -PD- d -PD> q' -> bcReadyState m' l q' -> False.
  intros B T R. inversion B as [H0 H1]. clear H1.
  lets TP : stepPTimed T. apply H0 in TP. destruct TP as [r [TR BR]].
  inversion TR; subst. unfold bcWait in H1.
  assert (discActEnabled r (chanTrans *?)) as D.
  inversion H1; subst.
  match goal with [U : _ $+$ _ -PD- _ -PD> _ |- _] => inversion U; subst end.
  inversion H4; subst.
  apply daeSumL. apply daeSumL. apply ProtAuxResults.dae_inPfx. reflexivity.
  lets D1 : ProtAuxResults.bisim_dae (ProcEquiv.bisim_symm _ _ BR) D.
  lets D2 : ProtAuxResults.bisim_dae R D1. inversion D2. unfold bcReady in H.
  repeat (match goal with [P : _ -PA- _ -PA> _ |- _] => inversion P; clear P; subst end).
  Qed.

Local Lemma currSince_del_bcWait_aux2 m x m' l e e' d :
  bcWaitStateEnt m x e -> e -ED- d ->> e' -> bcReadyStateEnt m' l e' -> False.
  intros B T R. inversion B; subst. inversion R; subst. inversion T; subst.
  match goal with [U : bcWaitStateProt _ _ _ |- _] => inversion U; subst end.
  match goal with [U : bcReadyStateProt _ _ _ |- _] => inversion U; subst end.
  match goal with [U : _ $||$ _ $||$ _ -PD- _ -PD> _ |- _] => inversion U; subst end.
  eapply currSince_del_bcWait_aux1; eassumption. Qed.

Corollary currSince_del_bcWait (n n' : Network) (m : Mode) (t : Time)
  (i : nat) (d : Delay) (p : reachableNet n) :
  n -ND- d -ND> n' -> currSince m t i n p ->
  exists x, bcWaitStateNet m (delToTime (x +dt+ d)) i n.

Proof.
  intros W C. lets CS : currSince_bc_state C.
  destruct CS as [[x BW] | [l BR]].
  lets CS' : currSince_bc_state (currSinceDel m d t i n n' p W C).
  destruct CS' as [[x' BW'] | [l BR']].
  exists x'. eapply bcWaitNet_del_bkwd; eassumption.
  exfalso. inversion BW as [e E1 E2]. inversion BR' as [e'' E1' E2'].
  link_netentdelfwd_tac e' LD.
  match goal with [U : e' @ i .: n' |- _] => lets EQ : entInNetUnique U E2' end. subst.
  eapply currSince_del_bcWait_aux2; eassumption.
  exfalso. inversion BR as [e E1 E2]. link_netentdelfwd_tac e' LD.
  eapply bcReady_urgent. eapply reachable_net_ent. apply p. apply E2.
  apply E1. eassumption. Qed.

Print Assumptions currSince_del_bcWait.
