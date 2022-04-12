(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

(*Require Import Reals.
Require Import List.*)
Require Import Equality.

Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.NARMisc.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxResults.
 
(*TIDY*)

(*TOGO: NARMisc*)
Lemma tfs_state_rel i n (p : reachableNet n) :
  tfsStateNet i n -> exists m t, tfs m t i n p.
  Admitted. (*4*)
  (*Proof: Induction on reachable.*)

(*TOGO: NARMisc?*)
Lemma tfs_currModeNet m1 m2 t i n p : tfs m1 t i n p ->
  currModeNet m2 i n -> ~failSafe m2 -> m1 = m2.
  Admitted. (*4*)
(**Proof: induction on tfs. The first base follows from the definition of
tfs. The discrete inductive case follows by application of I.H. and use
of the mode-swith-states(exact name?) theorem to eliminate all states
except tfsCurr->tfsBc. For this, it can be shown that the curr mode
is fail safe in the derivative, contradicting our hypothesis. The delay
inductive case follows by I.H. and a preservation theorem (name?) for
currModeNet over a delay*)

(*-TIDY*)

(***************************** Basic Results *****************************)

Lemma currModeNet_notifBad_pres_bkwd m i n n' a
  (rn : reachableNet n) (w : n -NA- a -NA> n') :
  currModeNet m i n' -> notifBadPathNet i n ->
  ~failSafe m ->
  currModeNet m i n \/
  exists t, tfs m t i n' (reachNetDisc n n' a rn w). introz U.
  lets CPB : currMode_pres_bkwd w U. ex_flat.
  lets EDM : eqDecMode x m. elim_intro EDM EQ NEQ.
  subst. left. assumption.
  lets CSS : currModeNet_switch_states rn w H U NEQ.
  lets NBC : notifBadPathNet_cases U0 H.
  elim_intro CSS SW TF. and_flat.
  (*For the first case let's use paused switch.*)
  lets PS : paused_switch_net i rn.
  assert (switchStateNet i n) as SSN. inversion AND.
  inversion H0. inversion H2. subst.
  econstructor; [do 2 econstructor | ].
  eapply switCurSt. eassumption. eassumption.
  rewrite <- PS in SSN.
  (*
  (*Now we can eliminate the paused/rangeBad/badOvlp clash.*)
  or_flat.
  state_pred_elim OR SSN. entnetuniq2 EN n. subst.
  state_pred_elim H0 H2. state_pred_elim H4 H6.
  subst. state_pred_elim H7 H10.
  state_pred_elim OR0 SSN. entnetuniq2 EN n. subst.
  state_pred_elim H0 H2. state_pred_elim H4 H6.
  subst. state_pred_elim H7 H10.
  (*Now we show the RHS because a tfs state implies tfs for all reachable
  networks.*)
  assert (tfsStateNet i n') as TSS. and_flat. apply tfsBc_tfs_net.
  assumption. remember (reachNetDisc n n' a rn w) as rn'.
  lets TSR : tfs_state_rel rn' TSS. ex_flat.
  right. exists x1. my_applys_eq H1.
  eapply tfs_currModeNet; eassumption. Qed.*)
  Admitted. (*R*)

Lemma currEq_eq_badOvlp_net m m'' i n :
  m = m'' -> currEqStateNet m m'' i n -> badOvlpStateNet i n.
  (*Proof: Just lift the appropriate definitions*)
  introz U. subst. inversion U0. inversion H.
  inversion H1. subst. econstructor; [do 2 econstructor | ];
  [ | eassumption].
  (*
  inversion H3; econstructor; try eassumption;
  reflexivity. Qed.*)
  Admitted. (*R*)

(***************************** More Complex Results *****************************)

(*If a message was delivered at a time less than AN ago, then a notification of that
message's delivery is enqueued with time stamp AN - t. *)
Theorem delivered_incomingNetNotif (n : Network) (v : list BaseType) (r : Distance)
  (l : Position) (t : Time) (i : nat) (p : reachableNet n) :
  delivered ([-v, l, r-]) t i n p -> forall q : t < adaptNotif,
  incomingNetNotif ((baseDistance r)::v) (minusTime adaptNotif t (Rlt_le t adaptNotif q)) i n.
  intros H q.
  (**Proof: Induction on delivered.*)
  induction H.
  (*The base case enforces an output of v to r by i. By looking at the semantics,
  we can see that this is only possible when the notification list of entity i also
  buffers r::v with timestamp AN. Hence we have incomingNetNotif r::v AN i n, which is our
  goal because t = 0.*)
  lets OI : outNet_incomingNetNotif w. my_applys_eq OI. apply timeEqR. simpl. ring.
  (*In the discrete inductive case, we have by I.H. that incomingNetNotif r::v (AN - t) i n*)
  lets IH : IHdelivered q. clear IHdelivered.
  (*Also by (Basics::incomingNetNotif-disc-pres) we get incomingNetNotif r::v (AN - t) i n'.*)
  lets ID : incomingNetNotif_disc_pres w IH. apply ID. apply RltMinusBothSides. assumption.
  (*So we're left with the delay inductive case. Well, if t + d < AN, then t < AN*)
  assert (t < adaptNotif) as Q. eapply Rplus_lt_weaken_lr. apply q. apply Rlt_le. delPos.
  (*So by IH incomingNetNotif r::v (AN - t) i n.*)
  lets IH : IHdelivered Q. clear IHdelivered.
  (*Then by (Basics::incomingNetNotif-del) we have incomingNetNotif r::v (AN - t - d) i n' which is the
  same as incomingNetNotif r::v (AN - (t + d)) i n and we're done.*)
  lets Q1 : incomingNetNotif_del p w IH.
  invertClearAs2 Q1 p1 Q2. my_applys_eq Q2. apply timeEqR. simpl. ring. Qed.


Theorem insuff_incomingNotif_abort (n n' : Network) (a : ActDiscNet) (m : Mode)
  (r : Distance) (l : Position) (i : nat) : 
  nextModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
  notifAbortPathNet i n'. Admitted. (*3*)
(**Proof: Much like Basics::outgoing_timeout_disc. We case analyse the action a.
For the cases where a is either input, output or ignore, we can show that
incomingNetNotif is preserved (...linking theorems / theorems on timed lists...),
and we have our LHS. In the remaining case, a is a tau action. Then we can show
that either incomingNetNotif <r, m, l> 0 i n' or the tau is the result of an output
of <r, m, l> by the interface on the channel AN and an input by the process on
this channel. Then by the base case of notifAbortPath, we have that
notifAbortPath m r i n', giving us the RHS of the goal, and we're done.

Idea: Standardised proof method? Destruct everything right down to timed lists of interface,
then show the notif lists are either equal or there's a transition from one to the other.
Then show that only such a transition, with the arguments of the buffered message,
will cause it to leave the list. But in that case, you have a case for the notifAbort path.
So that's it.*)

Theorem nextSince_next (n : Network) (m : Mode) (t : Time) (i : nat) (p : reachableNet n) : 
  nextSince m t i n p -> nextModeNet m i n. 
  (*By induction on nextSince.*)
  introz U. induction U. 
  (*In the base case, we carry over a similar result for ovWait (ovWait_next).*)
  eapply ovWaitState_nextMode_net.
  eapply reachNetDisc. apply p. apply w. apply H1.
  (*In the discrete inductive case, we have by I.H. that the nextMode was m in the previous
  state. Now let's assume towards a contradiction that the nextMode is no longer m.*)
  
(*nextModeNet

Well we can then show by (...linking...) and some elimination that the only
matching cases are those in which the software component either outputs on stable or on
mCurr. Now, by (Misc::nextSince_rel_state), we know that in our previous state we were
in one of the next_since states. We can show elsewhere that none of these are enabled
on mCurr! or stable! (...PA::activation...). Also, we can show that none of the broadcast
or listener states are enabled on these actions (...PA::activation...). Hence the software
process couldn't have done such an action, giving us our contradiction.*)

(*The timed inductive case is easy: the mode state's modes don't
change with time.*)
Admitted. (*3*)
(**Proof: As detailed above*)

(*If an entity is on the notification abort path, and a
discrete transition happens, then in the next state it is either still on the
notification abort path, or it is not in a nextSince state.*)
Theorem notifAbort_not_nextSince (n n' : Network)
  (a : ActDiscNet) (i : nat) (rn : reachableNet n) : 
  notifAbortPathNet i n -> n -NA- a -NA> n' ->
  notifAbortPathNet i n' \/ ~nextSinceStateNet i n'. introz U. 
  (**Proof: Similar to msgAbort_not_nextSince*)
  (*Link down to the entity level and eliminate the entity equality case.*)
  inversion U. link_netentdiscfwd_tac e' b U1. left. econstructor.
  apply H. rewrite U2. assumption.
  (*Extract the process transition from the entity one.*)
  (*Apply linking from the entity transition to the software transition.*)
  link_entsoftdisc_tac;
  (*Show and use equality between mode states.*)
  lets MSI : minet H0; lets MSI' : minet U1;
  lets NME : notifAbort_modeState_eq U MSI U0;
  lets MIU : mState_in_net_unique MSI' NME; subst.
  (*First deal with the case where the process terms are equal.*)
  left. econstructor;[ | apply U1]. inversion H.
  econstructor; eassumption. eapply napCuok; eassumption.
  eapply napAbort; eassumption.
  (*Now on to the case where the process term transitions.
  Invert the path predicate and solve all 3 sub-cases.*)
  inversion H; subst.
  (*---------------------Case 1: rangeBad-----------------*) 
  inversion H6; subst. link_partripdiscex_tac_norm. 
  lets LPT : link_par_triple_discW_3 H1. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply napRng. econstructor. eassumption. reflexivity.
  assumption. assumption.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets RBN : rangeBad_next H3 H2. ex_flat.
  left. econstructor. eapply napCuok. econstructor.
  eapply currEq_cond_false. apply H8. my_applys_eq H4.
  remember ([|p1' $||$ p2' $||$ p3', l, h, k0|]) as e'.
  replace (currModeMState k0) with (currModeEnt e').
  assert (currEqStateEnt x1 m' e'). subst.
  (*
  repeat econstructor.
  assumption. eapply currEq_mode. eassumption. subst.
  reflexivity. eassumption. eassumption.
  (*---------------------Case 2: currOK-----------------*) 
  inversion H4; subst. link_partripdiscex_tac_norm. swap H2 H1.
  lets LPT : link_par_triple_discW_3 H2. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply napCuok. econstructor. eassumption. assumption.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets CON : currOK_next H3 H1.
  elim_intro CON NEX LIS.
  (*First sub-case of the tracking- show abortOvlp state holds.*)
  ex_flat. left. econstructor.
  eapply napAbort. econstructor. eapply nextEq_cond_true;
  [ | apply H5]. remember ([|p1' $||$ p2' $||$ p3', l, h, k0|]) as e'.
  assert (nextEqStateEnt x1 m' e'). subst. repeat econstructor. assumption.
  lets NEM : nextEq_mode H6. rewrite Heqe' in NEM.
  apply nextMode_ent_mState in NEM. rewrite H7 in NEM. inversion NEM.
  reflexivity. apply U1.
  (*Second sub-case of the tracking. Show a contradiction because it implies an input on
  the channel abort by the listener, which cannot be matched by any component- particularly
  the mode state, because it has a next mode and so is not stable.*)
  assert (p3 <> p3') as PNE3. unfold not. intros. subst.
  state_pred_elim H1 LIS.
  assert (p1 $||$ p2 $||$ p3 <> p1' $||$ p2' $||$ p3') as PNE.
  unfold not. intro. inversion H5. subst. apply PNE3. reflexivity.
  (*apply ent proc link theorem and flatten out the ands, ors and exists.*)
  lets LEP : link_ent_proc_neq_disc PNE U3. andflat LEP.
  or_flat; ex_flat; and_flat; try link_partripneq_tac;
  try (lets CLT : currOK_listening_track H1 LIS AND1; inversion CLT); subst.
  (*From here there are 5 LEP sub-cases (some were eliminated)*)
  (*In the first case apply this tactic: link_partriptau_tac,
  and use tracking to narrow down info and eliminate some cases.*)
  reach_net_prot_tac.
  link_partriptau_tac c v LPT;
  try (lets CLT : currOK_listening_track H1 LIS LPT1;
  inversion CLT; subst).
  (*Eliminate first two sub-cases by contradiction.*)
  subst; contradict PNE3; reflexivity.
  subst; contradict PNE3; reflexivity.
  (*Two remaining sub-cases are that p1 or p2 output on MStable.
  Contradictions can be shown in both cases.*)
  false. eapply bc_mStable_out_not. apply LPT.
  inversion RPT. assumption.
  false. eapply ovlp_mStable_out_not. apply LPT.
  inversion RPT. assumption.
  (*Now back to the remaining cases. First eliminate interface/software synch.*)
  false. eapply inter_mStable_in_not. eassumption.
  (*Then do the modeState/software synch.*)
  false. eapply next_modeState_stable_not; eassumption.
  (*Get rid of p reading current position by tracking and showing that actions can't be equal-
  incompatible actions in question are input on pos and input on stable*)
  lets CLT : currOK_listening_track H1 LIS AND; inversion CLT.
  (*---------------------Case 3: abortOvlp-----------------*) 
  inversion H3; subst. link_partripdiscex_tac_norm. swap H1 H2.
  lets LPT : link_par_triple_discW_3 H2. elim_intro LPT EQP EXP.
  (*EQ case, LHS follows directly*)
  left. subst. econstructor;[ | apply U1].
  eapply napAbort. econstructor. eassumption.
  (*transition case- need to use fwd-tracking.*)
  ex_flat. lets CON : abortOvlp_next H4 H1. right.
  (*Assert some useful results for later.*)
  assert (p3 <> p3') as PNE3. unfold not. intros. subst.
  false. eapply listening_abort_contra; eassumption.
  assert (p1 $||$ p2 $||$ p3 <> p1' $||$ p2' $||$ p3') as PNE.
  unfold not. intro. inversion H5. subst. apply PNE3. reflexivity.
(*apply ent proc link theorem and flatten out the ands, ors and exists.*)
  lets LEP : link_ent_proc_neq_disc PNE U3. andflat LEP.
  or_flat; ex_flat; and_flat; try link_partripneq_tac;
  try (lets CLT : abortOvlp_listening_track H1 CON AND1; inversion CLT); subst.
  (*In the first case apply this tactic: link_partriptau_tac,
  and use tracking to narrow down info and eliminate some cases.*)
  reach_net_prot_tac.
  link_partriptau_tac c v LPT;
  try (lets CLT : abortOvlp_listening_track H1 CON LPT1;
  inversion CLT; subst).
  (*Eliminate first two sub-cases by contradiction.*)
  subst; contradict PNE3; reflexivity.
  subst; contradict PNE3; reflexivity.
  (*Two remaining sub-cases are that p1 or p2 output on MStable.
  Contradictions can be shown in both cases.*)
  false. eapply bc_abort_in_not. apply LPT.
  inversion RPT. assumption.
  (*This is the special case, where we need to show that nextSinceState does not hold.*) 
  inversion RPT.
  lets OAI : ovlp_abort_in_notNextSince LPT H9. unfold not. intro. apply OAI.
  inversion H11. entnetuniq2 EN n'. subst. inversion H12. inversion H6.
  assumption.
  (*Now back to the remaining cases. First eliminate interface/software synch.*)
  false. eapply inter_abort_in_not. eassumption.
  (*Then do the modeState/software synch.*)
  false. eapply modeState_abort_in_not; eassumption.
  (*Get rid of p reading current position by tracking and showing that actions can't be equal-
  incompatible actions in question are input on pos and input on stable*)
  lets CLT : abortOvlp_listening_track H1 CON AND; inversion CLT. Qed.*)
  Admitted. (*R*)

(* If a message with mode m was delivered exactly AN time units ago, and the
coverage of the message was insufficient with respect to said mode, and we have
been awaiting a transition to m for some t time units greater than AN, then one
of two things holds. Either a) A notification of the message and its coverage is
pending immediately i.e. with timestamp 0 or b) the entity in question is on the
notification abort path. *)
Theorem instant_insuff_abort (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t : Time) (i : nat) (p : reachableNet n) : 
  delivered ([-[baseMode m, basePosition l], l0, r-]) adaptNotif i n p -> ~sufficient m r ->
  nextSince m t i n p -> adaptNotif < t ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n \/
  notifAbortPathNet i n. 
  (*Induction on delivered. BaseType case fails because of AN not equal 0.*)
  intros H H0 H1 H2.
  (*Induction on delivered. BaseType case fails because of AN not equal 0.*)
  dependent induction H. false. apply (Rlt_irrefl adaptNotif).
  eapply Rle_lt_trans. rewrite <- x. apply Rle_refl. apply adaptNotif_positive.
  (*Discrete inductive case: Apply I.H. to previous state, yielding incomingNetNotif
  <r, m, l> 0 i n \/ notifAbortPath m r i n.*)
  dependent destruction H1. false. eapply Rlt_not_le. apply H4. simpl. timeNonneg.
  lets IHdisc : IHdelivered H0 H1 H3.
  (*Now we do a case analysis on this disjunction. First off we have
  incomingNetNotif <r, m, l> 0 i n. We can show then by (insuff_incomingNet_abort) that our
  goal holds in the next state.*)
  elim_intro IHdisc D1 D2.
  assert (nextModeNet m i n) as Q. eapply nextSince_next. apply H1.
  eapply insuff_incomingNotif_abort. apply Q.
  apply w. assumption. assumption.
  (*Then there's the case where notifAbortPath m r i n. In this case, we can show by
  (notifAbort_not_nextSince) that either notifAbortPath m r i n' or ~nextSineState m i n'.*)
  lets G : notifAbort_not_nextSince p D2 w. elim_intro G G1 G2.
  (*The former gives us our goal by the RHS.*)
  right. assumption.
  (*The latter gives us a contradiction by nextSinceState*)
  false.
  (*Delay case: Apply (delivered_incomingNetNotif) to previous state and get
  incomingNetNotif <r, m, l> (AN _ (AN - d)) i n = incomingNetNotif <r, m, l> d i n.*)
  assert (t0 < adaptNotif) as Q. rewrite <- x. simpl. Rplus_lt_tac. delPos.
  lets W : delivered_incomingNetNotif H Q.
  (*Then by (Basics::incomingNetNotif_del) we get incomingNetNotif <r, m, l> 0 i n',
  our left disjunct.*)
  left. lets E : incomingNetNotif_del p w W. invertClearAs2 E Z1 Z2.
  my_applys_eq Z2. apply timeEqR. simpl. rewrite <- x. simpl. ring. Qed.

Theorem insuff_incomingNotif_bad (n n' : Network) (a : ActDiscNet) (m : Mode)
  (r : Distance) (l : Position) (i : nat) : 
  currModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
  notifBadPathNet i n'. Admitted. (*3*)
(*Proof: Much like insuff_incomingNotif_abort.*)

(** If the badOvlp state holds at a particular reachable state,
and in the next state listening holds, then the next state is tfs for some
time t, with the mode parameter equal to the current mode.*)
Theorem badOvlp_listening_tfs n n' a i m 
  (rn : reachableNet n) (w : n -NA- a -NA> n') :
  badOvlpStateNet i n -> listeningStateNet i n' ->
  currModeNet m i n ->
  exists t, tfs m t i n' (reachNetDisc n n' a rn w).
(*Proof: Going to have to solidify this one a bit, but the intuition is as follows.
Either the derivative state is tfs or it is not (a result to prove in itself?). If it
is, then the conclusion is done (though we may need to prove an auxiliary result that
the mode parameter of tfs always matches the current mode? Or is this already done?).
If the derivative state is not tfs, then we can show a contradiction. We show this
by tracking the transition from badOvlp to listening, showing that the listener
component must output on "bad" for this to occur, and show (inter-comp?)
that the only other component capable of matching this output is the overlap
component. Then show (brute force?) that the overlap component is capable of inputting
on this channel only if it is in a tfs state. Then show (or use existing result?) that
tfsState implies tfs for some parameters. And again use an auxiliary result to show
that the tfs mode parameter must match the current mode*)
Admitted. (*2*)

(*If an entity is on the notification bad path, and a discrete transition
happens, then in the next state it is either still on the notification bad path,
or the tfs relation holds in the next state.*)
Theorem notifBad_pres_tfs (m : Mode) (n n' : Network)
  (a : ActDiscNet) (i : nat) (rn : reachableNet n)
  (w : n -NA- a -NA> n') : 
  notifBadPathNet i n -> currModeNet m i n' -> ~failSafe m ->
  notifBadPathNet i n' \/ (exists t, tfs m t i n' (reachNetDisc n n' a rn w)).
  introz U.
  (*Case analyse the notifBadPath using notifBadPathNet_cases.*)
  lets CPB : currModeNet_notifBad_pres_bkwd U0 U U1.
  elim_intro CPB CMN TFD.
  lets NBC : notifBadPathNet_cases U CMN. or_flat. ex_flat.
  (*In the rangeBad case, forward tracking gives you a state that will
  yield notifBadPathNet.*)
  lets RNN : rangeBad_next_net w OR CMN. left. or_flat.
  eapply rangeBad_notifBad_net; eassumption.
  ex_flat.
  assert (badOvlpStateNet i n') as BOS. eapply currEq_eq_badOvlp_net.
  reflexivity. eassumption. apply badOvlp_notifBad_net; assumption.
  (*In the badOvlp case, fwd-tracking gives one case of badOvlp,
  which also yields notifBadPath.*)
  lets BNN : badOvlp_next_net w OR0. or_flat.
  left. apply badOvlp_notifBad_net; assumption.
  (*So now we are left with the case of the transition from badovlp to listening.
  From here, we simply apply an auxiliary result saying that tfs is implies, and
  the proof is complete.*)
  right. eapply badOvlp_listening_tfs; eassumption.
  (*We finally deal with the remaining tfs case generated by a previous
  application of currModeNet_notifBad_pres_bkwd.*)
  right. apply TFD. Qed.

Lemma tfs_pres_not_currSince m t i n n' p a
  (w : n -NA- a -NA> n') : tfs m t i n p ->
  tfs m t i n' (reachNetDisc n n' a p w) \/
  (forall m' t' p', ~currSince m' t' i n p').
(*Note: might want to ease up on the generality of the second conjunct?
All we really need is the t general, the m and the p are not necessary.
Proof:  Most tfs cases are preserved forward. We can separately prove for
tfsBc and tfsListen that ~currSince holds. Then the tfsListen case is done
here.*)
Admitted. (*2*)

(* If a message with mode m was delivered exactly AN time units ago, and the coverage
of the message was insufficient with respect to said mode, and we have been broadcasting
in mode m for some t time units greater than AN, then one of 3 things holds. 
Either a) A notification of the message and its coverage is pending immediately i.e. 
with timestamp 0 or b) the entity in question is on the notification bad path or 
c) we are at the beginning of a transition to a fail safe mode. *)
Theorem instant_insuff_bad (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t : Time) (i : nat) (p : reachableNet n) : 
  delivered ([-[baseMode m, basePosition l], l0, r-]) adaptNotif i n p -> ~failSafe m ->
  ~sufficient m r -> currSince m t i n p -> adaptNotif < t ->
  incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n
  \/ notifBadPathNet i n \/ exists t, tfs m t i n p.
  intros H NFS H0 H1 H2. lets CSS : H1.
  (*Induction on delivered. BaseType case fails by contradiction on AN = 0.*)
  dependent induction H. false. apply (Rlt_irrefl adaptNotif).
  eapply Rle_lt_trans. rewrite <- x. apply Rle_refl. apply adaptNotif_positive.
  (*Discrete Inductive case. Destruct currSince for previous cases.*)
  dependent destruction H1.
  (*Get rid of the case where the previous state was nextSince
  first apply instant_insuff_abort. Then show that the transition from nextSince to
  currSince was impossible for notifAbortPathNet and so message must be incoming. Then
  show that the transition from nextSince to currSince preserves incoming, giving us LHS*)
  lets IIA : instant_insuff_abort H H0 H1 H4.
  (*To use later: let's show that we're in a switch state and hence are paused.*)
  assert (reachableNet n') as p'. eapply reachNetDisc; eassumption.
  assert (switchStateNet i n') as SSN2. inversion H3. inversion H5. inversion H7.
  netState_auto_pre. eapply switLisSt. eassumption.
  assert (switchStateNet i n) as SSN1. inversion H2. inversion H5. inversion H7.
  netState_auto_pre. eapply switCurSt. eassumption.
  lets PSN2 : paused_switch_net i p'. rewrite <- PSN2 in SSN2.
  lets PSN1 : paused_switch_net i p. rewrite <- PSN1 in SSN1.  
  (*OK, now we're back to the run of the mill, a few contradictions to come later.*)
  elim_intro IIA IL IR.
  assert (nextModeNet m i n) as NM. eapply nextSince_next. eassumption.
  lets IIA : insuff_incomingNotif_abort NM w H0 IL. elim_intro IIA IIL IIR.
  left. assumption.
  (*OK, so contradictions follow from the assertion of paused contradicting with the
  notifAbortPath, either now or in the previous state.*)
  false. eapply state_disj_paused_notifAbort. apply SSN2. assumption.
  false. eapply state_disj_paused_notifAbort. apply SSN1. assumption.
  (*OK, now we're at a case where the previous state is currSince,
  so we can apply I.H. to previous state, yielding
  incomingNetNotif <r, m, l> 0 i n \/ notifAbortPath m r i n \/ tfs 0.*)
  lets IH : IHdelivered NFS H0 H1 H3.
  (*We then break the IH into its three cases and prove each separately.*)
  lets IHC : IH H1. clear IH. rename IHC into IH. elimOr3 IH IH.
  (*First, there's the semi-preservation of incomingNetNotif,zeroTime by a discrete
  transition and currSince (and so currMode) holding. So first we assert that currMode
  holds and then we can apply this theorem.*)
  assert (currModeNet m i n) as CMN. eapply currSince_curr. eassumption.
  lets IIB : insuff_incomingNotif_bad CMN w H0 IH0.
  elim_intro IIB INN NBN. left. assumption. right. left. assumption.
  (*Then notifBadPathNet is shown to be either preserved or goes to tfs*)
  right. eapply notifBad_pres_tfs; assumption.
  (*Now tfs is shown to hold in the previous state, and we must show it to hold now.
  Well, a separate result gives us two cases to consider. First, tfs holds in the next
  state. In this case, we're done. Else, ~currSince must hold in the next state-
  which contradicts a hypothesis. So we're done in any case.*)
  invertClearAs2 IH t0 TFS.
  lets TPNC : tfs_pres_not_currSince w TFS. elim_intro TPNC TF NCS.
  right. right. exists t0. assumption. false. eapply NCS. eassumption.
  (*Delay inductive case: previous state must have delivered the message at some t' < AN.
  Then from (delivered_incomingNetNotif) and incomingNetNotif delay constructor,
  we have the LHS.*)
  assert (t0 < adaptNotif) as TLAN. rewrite <- x. simpl. Rplus_lt_tac.
  delPos. lets DIN : delivered_incomingNetNotif H TLAN. left. 
  lets IND : incomingNetNotif_del p w DIN. destruct IND. my_applys_eq i0.
  apply timeEqR. simpl. rewrite <- x. simpl. ring.
  (*Note, the proof is Similar to instant_insuff_abort.*)
  Qed.

(* If a message was delivered t' time units ago, and we have been waiting to
enter the next mode m for some time t, with t' < t, and the time since delivery
is greater than AN, then message delivery in question was sufficient.*)
Theorem deliv_next_suff (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t t' : Time) (i : nat) (p : reachableNet n) :
  nextSince m t i n p ->
  delivered ([-[baseMode m, basePosition l], l0, r-]) t' i n p ->
  adaptNotif < t' -> t' < t -> sufficient m r.
  introv H H0. gen t.
  (*Induction on delivered.*)
  induction H0; intros u G1 G2 G3; [false | dependent destruction G1..].
  (*The base case fails because of AN < 0.*)
  false. eapply Rlt_not_le. apply G2. simpl. timeNonneg.
  (*For the inductive cases, we can know that since delivered and nextSince share
  the same history p, that the previous state was also nextSince- we show this
  via an inversion on nextSince. One of these cases is contradictory with t0 < t.*)
  false. eapply Rlt_not_le. apply G3. simpl. timeNonneg.
  (*In the discrete inductive case we notice that t & t' haven't changed and so we just
  apply the I.H.*)
  eapply IHdelivered; try assumption. apply G1. apply G3.
  (*In the timed case, we do a case analysis on AN < t in the previous case.*)
  lets Q : Rlt_or_le adaptNotif t.
  elim_intro Q Q1 Q2.
  (*On the one hand, we may have AN < t, in which case we can just apply the I.H.*)
  eapply IHdelivered; try assumption. apply G1. simpl in G3. Rplus_lt_tac.
  (*Which leaves us with the other case, t <= AN, the only part of the proof that requires real thinking.
  Well, we again do a case analysis this time on t < AN or t = AN.*)
  apply Rle_lt_or_eq_dec in Q2. elim_intro Q2 F1 F2.
  (*If t' < AN, then by (delivered_incomingNetNotif), we get incomingNetNotif <r, m, l0> (AN - t') i n.*)
  lets K : delivered_incomingNetNotif H0 F1.
  (*Now, we already have from our hypothesis that AN < t' + d, rearranging to AN - t' < d.
  However, (Basiscs::incomingNetNotif-del) gives us that d <= AN - t', which is a
  contradiction.*)
  lets K1 : incomingNetNotif_del p w K. invertClearAs2 K1 K2 K3. simpl in K2. false.
  eapply Rle_not_lt. apply K2. simpl in G2. Rplus_lt_tac.
  (*So we are left with the case where t' = AN. We proceed from here by reductio
  ad absurdum, that is assume ~sufficient m r towards a contradiction.*)
  lets K : suffDec m r. elim_intro K K1 K2. assumption.
  (*We have enough information to apply (instant_insuff_abort) giving us
  incomingNetNotif <m, l, r> 0 i n \/ notifAbortPath m r i n.*)
  replace t with adaptNotif in H0; [ |apply timeEqR; symmetry; assumption].
  assert (adaptNotif < t0) as H. simpl in G3. rewrite F2 in G3. Rplus_lt_tac.
  lets G : instant_insuff_abort H0 K2 G1 H.
  (*We case analyse this disjunction.*)
  elim_intro G H1 H2.
  (*The first case fails by contradiction via an application of (Basiscs::incomingNetNotif_del)
  yielding d <= 0, impossible for a strictly positive delay.*)
  lets H4 : incomingNetNotif_del p w H1. invertClearAs2 H4 H5 H6. false.
  eapply Rle_not_lt. apply H5. simpl. delPos.
  (*The next case fails also because it can be shown that delay is impossible whenever we're on a
  notifAbortPath m r i n (...EA::notifAbortPath_urgent...). Hence we arrive at
  contradiction and conclude that the coverage is sufficient.*)
  lets nau : notifAbortPathNet_urgent p H2 w. contradiction nau.
  (*Note, this theorem bears resemblance to incomp_bad in how it is proved.*)
  Qed.

(* If an insufficient message was delivered t' time units ago, wtih AN < t',
and we've been currSince for some time t greater than t', then we are tfs for
some x > (t' - AN) time units.*)
Theorem insuff_react (n : Network) (m : Mode) (l l0 : Position)
  (r : Distance) (t t' : Time) (i : nat) (p : reachableNet n) :
  currSince m t i n p -> 
  delivered ([-[baseMode m, basePosition l], l0, r-]) t' i n p ->
  forall q : adaptNotif < t', t' < t ->  ~sufficient m r -> ~failSafe m ->
  exists x, minusTime t' adaptNotif (Rlt_le adaptNotif t' q) <= (time x) /\
  tfs m x i n p.
  (*Induction on currSince.*)
  intro. generalize dependent l. generalize dependent l0. generalize dependent r.
  generalize dependent t'. induction H; intros;
  match goal with [ H : ~failSafe m |- _ ] => rename H into Q end.
  (*In the base case, we proceed via contradiction. We get that the previous state was
  nextSince. We note that no time has passed since the previous state. Also, the action
  linking the the previous state to the current one is a tau, we show this.*)
  addHyp (switchCurr_listen_trans_tau n n' a i w H0 H1).
  (*So then delivered must be true for the previous state also, because the base case
  doesn't match against a tau.*)
  generalize dependent w. rewrite H5. intros. dependent destruction H2.
  (*But then by (deliv_next_suff), we can show sufficient m r*)
  addHyp (deliv_next_suff n m l l0 r t t0 i p H H2 q H3).
  (*This in direct contradiction with one of our hypothesis.*)
  contradiction H4.
  (*In the discrete inductive case, we can apply the I.H.*) 
  dependent destruction H1. contradict q. eapply Rle_not_lt.
  simpl. timeNonneg.
  addHyp (IHcurrSince t0 r l0 l H1 q H2 H3 Q). clear IHcurrSince.
  (*Tidy up the existential*)
  invertClearAs2 H4 x TFA. decompAnd2 TFA TFL TF. rename TF into H4.
  (*Then we must establish that we are currently still in a tfs state.*)
  assert (tfsStateNet i n'). apply currSince_curr in H.
  apply tfs_rel_state in H4. apply (tfs_currMode_disc_pres n n' a i m w H Q H4).
  (*Then the discrete consructor for tfs does the rest and the case is done.*)
  exists x. split. assumption. constructor; assumption.
  (*In the delay inductive case, we first assert t' < t from t' + d < t + d*)
  dependent destruction H0. rename t0 into t'.
  assert (t' < t). eapply Rplus_lt_reg_l. apply H1.
  (*Then we split this further depending on whether AN < t'*)
  addHyp (Rlt_or_le adaptNotif t'). invertClear H4.
  (*Make the IH a bit more useable.*)
  lets IH : IHcurrSince H0 H5 H3 H2 Q. decompExAnd IH x TL TF. clear IHcurrSince.
  (*First, let's assume it is. Then we can apply the I.H. and the delay constructor
  of tfs and we're done.*)
  replace ((minusTime (nonneg (time (delToTime (t' +dt+ d))))
  (nonneg (time adaptNotif)) (Rlt_le (nonneg (time adaptNotif))
  (nonneg (time (delToTime (t' +dt+ d)))) q))) with
  (delToTime (minusTime t' adaptNotif (Rlt_le adaptNotif t' H5) +dt+ d)).
  exists (x +dt+ d). split. apply Rplus_le_compat_r. assumption.
  constructor. assumption. apply timeEqR. simpl. ring.
  (*Otherwise, t' <= AN. In which case we have either t' < AN or t' = AN.*)
  remember ([baseMode m, basePosition l]) as v. apply Rle_lt_or_eq_dec in H5. invertClear H5.
  (*We apply (delivered_incomingNetNotif) for the t' < AN case, towards a contradiction.*)
  addHyp (delivered_incomingNetNotif n v r l0 t' i p H0 H4).
  remember (minusTime (nonneg (time adaptNotif)) (nonneg (time t'))
  (Rlt_le (nonneg (time t')) (nonneg (time adaptNotif)) H4)) as t''.
  addHyp (incomingNetNotif_del n n' d ((baseDistance r)::v) t'' i p w H5). invertClear H6.
  rename x into Q1. generalize dependent Q1. rewrite Heqt''. intros.
  simpl in Q1. simpl in q.
  (*The contradiction comes in the form d <= AN - t' < d*)
  assert (adaptNotif - t' < d). apply Rplus_lt_swap_rl. assumption.
  contradict H6. apply Rle_not_lt. assumption.
  (*So now we have the t' = AN case and we apply (instant_insuff_bad)*)
  apply timeEqR in H4. rewrite H4 in H0, H3. rewrite Heqv in H0.
  addHyp (instant_insuff_bad n m l l0 r t i p H0 Q H2 H H3).
  (*This leaves us with 3 sub cases on which to discriminate.*)
  decompose [or] H5; clear H5.
  (*The first two cases fail because delay can be shown to be impossible (...urgency...).*)
  remember ([baseDistance r, baseMode m, basePosition l]) as v2.
  addHyp (incomingNetNotif_del n n' d v2 zeroTime i p w H6). invertClear H5.
  rename x into Q2. clear H7. contradict Q2. apply Rlt_not_le. simpl. delPos.
  contradiction (notifBadPathNet_urgent i n n' d H7 w).
  (*Hence we are left with t' = AN and tfs m t i n for some t. In this case, we apply the tfs
  delay constructor to show tfs m (t + d) i n which is exactly our goal simplified from
  tfs m (AN + t + d - AN) i n p.*)
  invertClearAs2 H7 x TF. lets TFD : tfsDel w TF. exists (x +dt+ d).
  split. simpl. rewrite H4. apply Rminus_le_swap_lr. cut (0 <= x). intro LT0.
  my_applys_eq LT0. ring. timeNonneg. assumption. Qed.
  (*
  >The following picture captures the intuition of this proof:

  currSince --------------t----------------------------
      insuff-deliv--------t'---------------------------
                  ------AN------------
                                      -------tfs-------
  *)

