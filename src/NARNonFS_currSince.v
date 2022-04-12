(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".  
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.NARMisc.

Lemma ovWait_nextSinceState_net m t x y i n : 
  ovWaitStateNet m t x y i n -> nextSinceStateNet i n. Admitted (*9*).
(*Proof: Is there some auto tactic for this? #lift-compound-net-tac*)

(*If we are in the ovWaitState then we are either pending or nextSince.*)
Theorem ovWait_nextSince_pending (n : Network) (m : Mode) (t x y : Time) (i : nat)
  (p : reachableNet n) :
  ovWaitStateNet m t x y i n -> pending i n p \/ exists t, nextSince m t i n p.
  (*Proof: Induction on p, the proof of reachability.*)
  introz U. induction p.
  (*The base case fails by contradiction.*)
  initNet_contra U.
  (*In the discrete inductive case, we backtrack for cases of the previous state.*)  
  Admitted. (*C- This proof actually goes through based on
  ovReady_nextSince_pending, but the two are mutually inductive so we
  possibly need to combine the two into one result- or figure out a way
  to do mutual induction in Coq. The most straightforward solution to this
  is to prove a mutual result with a conjunction, and then the individual
  results follow easily from this.*)


(*SHARED TACTICS WITH OVWAITSTATE ANALOGUE?
If we are in the ovReadyState then we are either pending or nextSince.*)
Theorem ovReady_nextSince_pending (n : Network) (m : Mode) (t : Time) (i : nat)
  (l : Position) (p : reachableNet n) :
  ovReadyStateNet m t l i n -> pending i n p \/ exists t, nextSince m t i n p.
  introz U.
  (**Proof: Induction on reachable.*)
  induction p.
  (*
  (*Discard base case as initiality contradicts the state predicate*)
  initNet_contra U.
  (*Discrete inductive case- lets backtrack from ovReady*)
  lets OPN : ovReady_prev_net U s. ex_flat. or_flat.
  (*Where the previous case is ovReadySate follows by induction,
  case analysis of the disjunction, and application of the
  appropriate constructor.*)
  lets IH : IHp OR. or_flat.
  (*A previous cas of pending gives a next case of pending.*)
  left. eapply pendingReady; eassumption.
  (*A previous cas of nextSince gives nextSince.*)
  ex_flat. right. eexists. constructor. eassumption.
  eapply ovReady_nextSince_state; eassumption.
  (*So we're left with the discrete case where the previous state is
  ovWaitState m t x y. Then we use (ovWait_nextSince_pending) to show that
  the previous state was either pending or nextSince*)
  ex_flat. lets ONP : ovWait_nextSince_pending H0.
  (*case analyse, and apply the right constructor to get the same for this
  state.*)
  (*Delay inductive case fails by progress [salvaged?].*)
  Admitted. (*C- Need to combine with ovWait_nextSince_pending by some sort
  of mutual induction. See ovWait_nextSince_pending for details.*)*)
  Admitted. (*R*)

Lemma pending_urgent i n n' p d :
  pending i n p -> n -ND- d -ND> n' -> False. Admitted. (*5*) 
(**Proof: Induction on pending. BaseType case: ovWait is ready to input a position,
and so is urgent. This readiness is not perverted by any other discreet action,
so the ovWait-ovWait inductive case follows. Both inductive cases with ovReady
as the current state follows immediately from the fact that ovWaitState is
itself urgent*)

(*If we are in the ovWait state with the parameter x = 0,
then the nextSince relation holds.*)
Theorem ovWait_zero_nextSince (n : Network) (m : Mode) (t y : Time) (i : nat)
  (p : reachableNet n) : ovWaitStateNet m t zeroTime y i n ->
  exists t, nextSince m t i n p. Admitted. (*2*)
(**Proof: Induction on reachable. BaseType case fails. For the inductive case(s),
case analyse- is the last state ovWait? If yes, then the result follows easily
by induction. If not, then use (...ovWait_prev...) to get the possible shapes of
the previous state. Well, it can't be initState m, because this would give us
x = tw(m0, m) + period m, which is greater than 0. But x = 0. So our previous
state must have been ovReady m (t + period m) l. Then by (ovReady_nextSince_pending),
the previous state was either pending or nextSince. In either case, there is a
constructor of nextSince that allows us to prove nextSince holds for the current state.*)

(*If we are in the switchBc state, then the nextSince relation holds.*)
Theorem switchBc_nextSince (n : Network) (m : Mode) (i : nat)
  (p : reachableNet n) : switchBcStateNet m i n -> exists t, nextSince m t i n p.
  Admitted. (*2*)
(**Proof: By induction on reachable. Eliminate the easy cases, leaving us with the
discrete inductive case with the previous state not switchBcState. Then we use
(...switchBc_prev...) to give us ovWait m t 0 y as the predecessor state- we know
the parameter x is 0 because the transition would have to have been enabled.
Then by (ovWait_nextSince_pending & elimination of the pending case somehow) we have that the previous state was nextSince and so by
application of the nextSince discrete constructor so is this one.*)

(*If we are in the switchCurr state, then the nextSince relation holds.	*)
Theorem switchCurr_nextSince (n : Network) (m : Mode) (i : nat)
  (p : reachableNet n) : switchCurrStateNet i n ->
  exists t, nextSince m t i n p. Admitted. (*2*)
(**Proof: By induction on reachable and (...switchCurr_prev...) to give us switchBc m
as the predecessor state. Then by (swtichBc_nextSince) and application of the nextSince
discrete constructor our results follows.*)

(* Let's say in a reachable network, an entity is in non-fail-safe mode m.
Then that entity has been currSince m t.*)
Theorem nonFS_currSince (m : Mode) (i : nat) (n : Network) 
  (p : reachableNet n) : currModeNet m i n -> ~failSafe m ->
  exists t, currSince m t i n p.
  intros.
  (**Proof: Induction on the proof of reachability of n.*)
  induction p.
  (*In the base case, we have that n is initial. Hence all its constituent entities
  are in fail safe modes. So the assumption that entity i is in mode m which is not
  fail safe is contradictory, case closed.*)
  apply currMode_ent_ex in H. decompose [ex] H. clear H. rename x into e.
  invertClear H1. rewrite <- H2 in H0. apply False_ind. apply H0.
  eapply initial_failSafe. apply i0. apply H.
  (*Which leaves us the inductive cases. We start with the discrete inductive case.
  Here, we do a case analysis on whether the previous state was currMode m.*)
  addHyp (currModeNet_dec m i n). invertClear H1.
  (*If it was, then by the inductive hypothesis, we get currSince m t for
  the previous state*)
  apply IHp in H2. invertClear H2. rename x into t.
  (*Which immediately follows on to this state by the inductive definition of currSince.*)
  exists t. eapply currSinceDisc. apply H1. assumption.
  (*Otherwise, the previous state was not currMode m. And so it must have been currMode m'
  for some m' <> m (Basics::currMode_pres_bkwd).*)
  addHyp (currMode_pres_bkwd n n' a m i s H). invertClear H1. rename x into m'.
  assert (m' <> m). unfold not. intros. rewrite H1 in H3. apply H2. assumption.
  (*And so we can show that since the current mode has changed between states,
  the entity i must have performed a tau transition.*)
  addHyp H. rewrite (currMode_ent_ex m i n') in H4.
  addHyp H3. rewrite (currMode_ent_ex m' i n) in H5.
  invertClear H4. invertClear H5. invertClear H4. invertClear H6.
  rename x0 into e. rename x into e'.
  addHyp (curr_switch_ent_tau n n' a e e' i m' m s H5 H4 H7 H8 H1).
  (*We can also show that the software component contributed an output on mCurr and the
  mode-state contributed an input (EA::curr_switch_proc).*)
  rename p into X. destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  addHyp (currMode_ent_mState p l h k m' H7). addHyp (currMode_ent_mState p' l' h' k' m H8).
  assert (currModeMState k <> currModeMState k'). rewrite H9. rewrite H10. assumption.
  addHyp (curr_switch_proc p p' l l' h h' k k' H6 H11). invertClear H12.
  (*Now, we since n is reachable, so is p, and so p is a triple of processes*)
  addHyp (reachable_net_prot n i p l h k X H5). apply reachableProt_triple in H12.
  invertClear H12. rewrite <- H18 in H13. 
  (*And so one of the sub components P1, P2 or P3 must have performed this output.*)
  link_partripdiscex_tac Y p1' p2' p3'. rewrite Y in H13.
  link_partripout_tac U;[
  (*We eliminate the possibility P1 by (bc_mCurr_out_not)*)
  false; eapply bc_mCurr_out_not; [apply U | assumption] | |
  (*and we eliminate P3 with (listen_mCurr_not).*)
  false; eapply listen_mCurr_out_not; [apply U | assumption]].  
  (*Then by (...ovlp_mCurr_out...) we show that P2 was in the state switchCurrState,
  while the next state had P2' in switchListenState*)
  lets OO : ovlp_mCurr_out U H16.
  (*We can eliminate the tfs case because failSafe m contradicts our hypothesis.*)
  elim_intro OO SW TF. Focus 2.
  assert (tfsBcStateEnt ([|p', l', h', k'|])). constructor. rewrite Y.
  constructor. apply TF. apply tfsBc_failSafe in H12.
  simpl in H12. rewrite H10 in H12. false.
  (*This allows us to conclude that the previous state was nextSince m t i n for some t
  (switchCurr_nextSince)*)
  assert (switchCurrStateEnt ([|p, l, h, k|])).
  constructor. rewrite <- H18. constructor. apply SW.
  assert (switchCurrStateNet i n). econstructor. apply H12. assumption.
  addHyp (switchCurr_nextSince n m i X H19). invertClear H20.
  rename x into t.
  (*Now finally, by the base case of currSince, we can show that
  currSince m t i n holds.*)
  exists t. constructor. assumption. assumption. econstructor.
  constructor. constructor. apply SW. rewrite Y in H4. apply H4.
  (*For the delay inductive case, we first notice that delay preserves the current mode*)
  addHyp (currMode_del_pres_bkwd n n' d m i s H).
  (*Then we apply the I.H. to get that the previous mode was currSince.*)
  apply IHp in H1. invertClear H1. rename x into t.
  (*And now as our existential we take t + d*. And by the delay constructor of
  currSince, we're done.*)
  exists (t +dt+ d). constructor. assumption. Qed.