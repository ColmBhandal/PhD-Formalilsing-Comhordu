(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".  
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.ProtAuxResults.

(***************************** Misc *****************************)

(*Requires reachableEnt to be defined before it is proved.*)
Lemma reachable_ent_prot p l h k : reachableEnt ([| p, l, h, k |]) ->
  reachableProt p. intros. Admitted. (*D*)

Lemma nextModeEnt_not_stable m1 m2 p l h :
  nextModeEnt m1 ([|p, l, h, m2|]) -> False. intros. Admitted. (*D*)
(*Proof: immediate once nextModeEnt is defined.*)

(*Perhaps proof of this relies on a simpler proof from Mode State language?*)
Lemma mst_tout_mCurr_in m1 m2 :
  discActEnabledMState (chanMCurr *?) (<| m1, m2, zeroTime |>). intros.
  repeat econstructor. Qed.

(***************************** Lifted tracking *****************************)

(*Most results here should be provable with a simple enough lifting tactic-
and should be tagged accordingly with "back-track-lift-ent".*)

Lemma tfsNext_prev_ent m e e' a : tfsNextStateEnt m e' ->
  e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
  Admitted. (*#back-track-lift-ent*)
(*Proof: Lift backtracking results at process level. *)

(***************************** Inter-Component Relationships *****************************)
(**In here, I'd like results that relate the states of things within a reachable entity e.g. the state of the software component and the mode state.*)

Lemma currEq_mode m m'' e :
  currEqStateEnt m m'' e -> m = currModeEnt e. Admitted.

Lemma ovAbort_unstable e : reachableEnt e -> ovAbortStateEnt e -> unstable (mstEnt e).  
  (*Proof: Use some general inter-component tactics- at least pre-tactics anyway.*)
  introz U. Admitted. (*#inter-component*)
  
(**If an entity is in the tfsCurr state, then the mext mode exists and is failsafe.*)
Lemma tfsCurr_failSafe (e : Entity) (m : Mode) :
  tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m.
  Admitted. (*#inter-component*)
(**GENERAL TACTICS WOULD BE USEFUL HERE, BECAUSE THERE ARE 3 FAIRLY SMILAR THEOREMS TO COME.
Proof: Look at the overlap component. Upon entering this state, it must have written out a fail safe mode
to the mode state- in particular, the successor to the current mode.*)

(*CHANGE: Here and at application in NARNonFS_currSince.v.
Add reachability of entity as a hypothesis*)
(**If an entity is in the tfsBc state, then the current mode of that entity
is failsafe.*)
Lemma tfsBc_failSafe (e : Entity) :
  tfsBcStateEnt e -> failSafe (currModeEnt e).
  (**Proof: Backtracking gives that the previous state was tfsCurrState*)
  introz U. Admitted. (*C*)
(*then tfsCurr_failSafe gives that the next mode there was failsafe.
Finally, backtracking also gives that the transition was an output to
the mode state causing a mode switch, so the next mode of the previous state,
which was failsafe, is now the current mode.*)

Lemma tfsNext_currMode e m :
  reachableEnt e -> tfsNextStateEnt m e -> currModeEnt e = m.
  introz U.
  (*Proof: Induction on reachableEnt.*)
(*Base case fails. So we're left with
the case where there was a previous state. Now, either this is tfsNext or
it is not. If it is not, then we can see by tracking that the action to get
here was a read of the current mode from the mode state and so the two
must coincide. If the previous state is also tfsNext, it can be shown that
no mode state change is possible because only the overlap component is capable
of doing this.*) Admitted. (*D- reachableEnt*)

(**If we're in the state switchCurr m', then the next mode is m'.
Corollary: switchCurr is urgent.*)
Theorem switchCurr_mState (e : Entity) :
  reachableEnt e -> switchCurrStateEnt e -> exists m m',
  mstEnt e = <| m, m', zeroTime |>. Admitted. (*D- reachableEnt*)
(**Proof: Inductgion on reachabledEnt.
Relies on a chain of support of similar results for switchBc, ovWait,
ovReady and init. Each one relying on the last. The ovWait and ovReady ones
would need to be proved by mutual induction.*)

(** If an entity is in a state ready to output some m l from the broadcast component,
then it is in the position l.*)
Theorem bcReady_pos (e : Entity) (m : Mode) (l : Position) :
  reachableEnt e -> bcReadyStateEnt m l e -> inPosEnt l e. Admitted. (*D- reachableEnt*)  
(**Proof: Induction on reachableEnt. The only way to enter bcReady m l is
by reading the current position l, and by urgency no time can pass in the state,
and then by disc_pre_pos [salvaged] the position is the same. *)

(** If an entity is in a state ready to output some m l from the overlap component,
then it is in the position l.*)
Theorem ovReady_pos (e : Entity) (m : Mode) (t : Time) (l : Position) :
  reachableEnt e -> ovReadyStateEnt m t l e -> inPosEnt l e. Admitted. (*D- reachableEnt*)
(**Proof: Analogous to that of bcReady_pos.*)

Lemma tfsListen_paused p1 p2 p3 :
   tfsListenStateProt (p1 $||$ p2 $||$ p3) -> pausedStateProt (p1 $||$ p2 $||$ p3).
  Admitted. (*C*)(*Need to add process reachability as a hypothesis*)

(** If an entity inputs a message then that message is incoming.*)
Lemma input_incomingEnt (v : list Base) (e e' : Entity) (l : Position) (r : Distance) :
  e -EA- ([-v, l, r-]) #? ->> e' -> incomingEnt v e'.
  (*Proof: Obvious from the definition of incoming.*)
  introz U. inversion U. constructor. inversion H5.
  constructor. inversion H8. constructor.
  reflexivity. inversion H10. Qed.


(***************************** Urgency *****************************)
(**Here we prove simple urgency results which will refer to individual states rather
than more complicated predicates such as msgBadPath. The urgency results usually follow
one of two patterns. Either a synchronisation happens between two of the sub-terms in
the software process, or it happens between the software process and another component
i.e. the mode state or the interface component.*)

(*** Urgency Pre-processing Tactics ***)

Ltac urgency_pre_tac := 
  let U := fresh "U" in
  (try match goal with [ |- forall e : Entity, _] =>
  intros e e' d; introz U end); destrEnts_norm;
  match goal with [ RE : reachableEnt _ |- _] =>
  apply reachable_ent_prot in RE end; let q := fresh "Q" in reachprot q;
  inversion q as [p1 p2 p3 BC OV LI TR]; symmetry in TR.

(** SE SP and S are the names of the state predicates involved- the entity,
the protocol and the standard ones respectively.*)
Ltac urgency_pre_tac2 SE SP S :=
  urgency_pre_tac;
  match goal with
  | [ _ : SE ([|?p0, ?l0, ?h0, ?k0|]) |- _] =>
    assert (SP p0) as TP;
    [inversion U0; assumption | ];
    match goal with
    | [ TR : p0 = ?p1 $||$ ?p2 $||$ ?p3, TP : SP p0 |- _] =>
      rewrite TR in TP end
  end;
  match goal with [ _ : SP (?p1 $||$ ?p2 $||$ ?p3) |- _]
  (*The state predicate could come from either the broadcast, overlap, or listener.
   Try all three. Only one should succeed.*)
  => try (assert (S p1) as TS; [inversion TP; assumption | ]);
     try (assert (S p2) as TS; [inversion TP; assumption | ]);
     try (assert (S p3) as TS; [inversion TP; assumption | ]) end.

(** Same as urgency_pre_tac2 but the state predicate has 1 parameter.*)
Ltac urgency_pre_tac2_1 SE SP S :=
  urgency_pre_tac;
  match goal with
  | [ _ : SE ?x1 ([|?p0, ?l0, ?h0, ?k0|]) |- _] =>
    assert (SP x1 p0) as TP;
    [inversion U0; assumption | ];
    match goal with
    | [ TR : p0 = ?p1 $||$ ?p2 $||$ ?p3, TP : SP x1 p0 |- _] =>
      rewrite TR in TP end
  end;
  match goal with [ _ : SP ?x1 (?p1 $||$ ?p2 $||$ ?p3) |- _]
  (*The state predicate could come from either the broadcast, overlap, or listener.
   Try all three. Only one should succeed.*)
  => try (assert (S x1 p1) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 p2) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 p3) as TS; [inversion TP; assumption | ]) end.

(** Same as urgency_pre_tac2 but the state predicate has 2 parameters.*)
Ltac urgency_pre_tac2_2 SE SP S :=
  urgency_pre_tac;
  match goal with
  | [ _ : SE ?x1 ?x2 ([|?p0, ?l0, ?h0, ?k0|]) |- _] =>
    assert (SP x1 x2 p0) as TP;
    [inversion U0; assumption | ];
    match goal with
    | [ TR : p0 = ?p1 $||$ ?p2 $||$ ?p3, TP : SP x1 x2 p0 |- _] =>
      rewrite TR in TP end
  end;
  match goal with [ _ : SP ?x1 ?x2 (?p1 $||$ ?p2 $||$ ?p3) |- _]
  (*The state predicate could come from either the broadcast, overlap, or listener.
   Try all three. Only one should succeed.*)
  => try (assert (S x1 x2 p1) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 x2 p2) as TS; [inversion TP; assumption | ]);
     try (assert (S x1 x2 p3) as TS; [inversion TP; assumption | ]) end.

(*** Urgency Results ***)

Lemma gotMsgStateEnt_urgent (e e' : Entity) (d : Delay) m l :
  reachableEnt e -> gotMsgStateEnt m l e -> e -ED- d ->> e' -> False.
  Admitted.

Lemma gotRangeStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  reachableEnt e -> gotRangeStateEnt m r e -> e -ED- d ->> e' -> False.
  Admitted.

Lemma currCompStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  reachableEnt e -> currCompStateEnt m r e -> e -ED- d ->> e' -> False.
  Admitted. (*Relies on the result that the mode state can always
EITHER output on next or stable. #modif-urgent*)

Lemma abortOvlpStateEnt_urgent (e e' : Entity) (d : Delay) :
  reachableEnt e -> abortOvlpStateEnt e -> e -ED- d ->> e' -> False.
  Admitted.

Lemma tfsStartStateEnt_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsStartStateEnt e -> e -ED- d ->> e' -> False.
  urgency_pre_tac2 tfsStartStateEnt tfsStartStateProt tfsStartState.
  (*Now we proceed by activation and noSynch.*)
  lets MC : modeState_curr_enabled k0.
  remember (chanMCurr ;? [baseMode (currModeMState k0)]) as a.
  assert (discActEnabled p2 a). rewrite Heqa.
  apply tfsStart_mCurr_in. assumption.
  del_noSyncNow_tac NS. eapply NS.
  (*Now it remains to show that the action a and its complement are enabled for
  p0 and the mode state respectively.*)
  rewrite TR. apply daeParR. apply daeParL. assumption. rewrite Heqa.
  assumption. Qed.

Lemma tfsListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsListenStateEnt e -> e -ED- d ->> e' 
  -> False.
  (*Some pre-tactics*)
  urgency_pre_tac2 tfsListenStateEnt tfsListenStateProt tfsListenState.
  del_triple_sort_tac.
  (**It can be shown that tfsListen is only reached by the overlap when the listener
  component is paused. This in turn implies the listener component is listening on the
  channel unpause. Since the overlap component can clearly output on this channel, a
  synch is possible, and so by maximal progress delay cannot happen.*)
  lets PA : tfsListen_paused TP. assert (pausedState p3). inversion PA.
  assumption. lets PAP : paused_unpause_in_sort H.
  lets TAP : tfsListen_unpause_out_sort TS. apply SORT2_3 in TAP.
  apply TAP. apply PAP. Qed.

Lemma tfsNext_urgent : forall (m : Mode) (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsNextStateEnt m e -> e -ED- d ->> e' -> False.
  intro m. intros e e' d. introz U.
  (*Need to ensure the current mode equals the parameter to tfsNext.*)
  lets TCM : tfsNext_currMode U U0.
  (*Some pre-processing*)
  urgency_pre_tac2_1 tfsNextStateEnt tfsNextStateProt tfsNextState.
  lets FS : failSafeSucc_successor m.
  assert (k0 -mtr-> failSafeSucc m) as FS2. simpl in TCM.
  rewrite TCM. assumption.
  lets MS : mState_stable_next_enabled FS2. noSyncNow_tac. 
  (*Two cases for input of mode state.*) elim_intro MS MS1 MS2.
  (*MStable case.*)
  lets TF : tfsNext_mStable_out TS.
  assert (discActEnabled p0 (chanMStable;! [])) as DA.
  rewrite TR. apply parTriple_dae_intro2. assumption.
  apply NS in DA. decompAnd2 DA NDA1 NDA2. apply NDA2.
  assumption.
  (*MNext case.*)
  lets TF : tfsNext_mNext_out TS.
  assert (discActEnabled p0 (chanMNext;! [baseMode (failSafeSucc m)]))
  as DA. rewrite TR. apply parTriple_dae_intro2. assumption.
  apply NS in DA. decompAnd2 DA NDA1 NDA2. apply NDA2.
  apply MS2. Qed.

Lemma bcReady_urgent (m : Mode) (l : Position) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> bcReadyStateEnt m l e -> e -ED- d ->> e' 
  -> False. urgency_pre_tac2_2 bcReadyStateEnt bcReadyStateProt bcReadyState.
  (**Proof: By activation, the bcReady state can be shown to be capable of outputting on
  chanOutProc. Separately, the interface component can be shown to always be available for
  input on this channel, i.e. it can always buffer a message from the software component.
  Thus, a synch between software and interface is possible, violating the "noSynch" condition
  that must hold for the entity to delay. Hence delay cannot happen.*)
  noSyncNow_tac. lets BO : bcReady_outProc_out TS.
  assert (discActEnabled p0 (chanOutProc;! [baseMode m, basePosition l])) as DA.
  rewrite TR. apply parTriple_dae_intro1. assumption.
  lets IO : interface_outProc_in h0 [baseMode m, basePosition l].
  apply NS in DA. decompAnd2 DA NDA1 NDA2. apply NDA1. assumption.
  Qed.

Lemma ovAbort_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> ovAbortStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U.
  lets OUS : ovAbort_unstable U U0.
  urgency_pre_tac2 ovAbortStateEnt ovAbortStateProt ovAbortState.
  (**Proof: Show that the mode state is not stable whenever we
  get into this state, which will require showing that the mode state is unstable
  for init, ovWait, and ovReady- by induction on reachableEnt I suppose. Then
  we show that stable! is activated on ovAbort, and hence a synch can happen with
  the mode state, so by progress there is no delay possible.*)
  noSyncNow_tac. lets OAS : ovAbort_stable_out TS.
  lets US : unstable_stable_in OUS.
  assert (discActEnabled p0 (chanMStable *!)) as DA.
  rewrite TR. apply parTriple_dae_intro2. assumption.
  apply NS in DA. decompAnd2 DA NDA1 NDA2. apply NDA2.
  assumption. Qed.

Lemma tfsBc_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsBcStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2 tfsBcStateEnt tfsBcStateProt tfsBcState.
  lets TOT : tfsBc_trans_out TS.
  (*Case analysis on the state of the broadcast component.*)
  inversion BC.
  (*If it is in either the sleeping or the wait state, then an input on trans
  is possible, which can synch with the output on trans from tfsBc.*)
  lets BIT : bcWait_trans_in H. del_triple_sort_tac. eapply enabledInSort_in in BIT.
  apply SORT1_2 in BIT. apply BIT. apply enabledInSort_out. assumption.
  lets SIT : sleep_trans_in H. del_triple_sort_tac. eapply enabledInSort_in in SIT.
  apply SORT1_2 in SIT. apply SIT. apply enabledInSort_out. assumption. 
  (*Otherwise, the broadcast component is in the ready state, in which case we
  already have urgency from bcReady-urgent.*)
  assert (bcReadyStateEnt m l1 ([|p0, l0, h0, k0|])) as BCE. constructor.
  rewrite TR. constructor. assumption. lets BCU : bcReady_urgent U BCE. 
  apply BCU. apply U1. Qed.

Lemma switchBc_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchBcStateEnt m e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2_1 switchBcStateEnt switchBcStateProt switchBcState.
  lets TOT : switchBc_wake_out TS.
  (*Case analysis on the state of the broadcast component.*)
  inversion BC.
  (*If it is in either the sleeping or the wait state, then an input on wake
  is possible, which can synch with the output on wake from switchBc.*)
  lets BIT : bcWait_wake_in H. del_triple_sort_tac. eapply enabledInSort_in in BIT.
  apply SORT1_2 in BIT. apply BIT. apply enabledInSort_out. apply TOT.
  lets SIT : sleeping_wake_in H. del_triple_sort_tac. eapply enabledInSort_in in SIT.
  apply SORT1_2 in SIT. apply SIT. apply enabledInSort_out. apply TOT.
  (*Otherwise, the broadcast component is in the ready state, in which case we
  already have urgency from bcReady-urgent.*)
  assert (bcReadyStateEnt m0 l1 ([|p0, l0, h0, k0|])) as BCE. constructor.
  rewrite TR. constructor. assumption. lets BCU : bcReady_urgent U BCE. 
  apply BCU. apply U1. Qed.

Lemma swithcCurr_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchCurrStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2 switchCurrStateEnt switchCurrStateProt switchCurrState.
  (*Apply (switchCurr-next-Mode) to assert that there is some next mode.*)  
  lets SMS : switchCurr_mState U U0. decompEx2 SMS m1 m2 MS.
  (*Then it is easy to show that the mode state is capable of inputting
  on mCurr, which complements the output that is enabled in this state,
  and so we're urgent.*)
  lets NIM : mst_tout_mCurr_in m1 m2.
  lets SOM : switchCurr_mCurr_out TS.
  assert (discActEnabled p0 (chanMCurr *!)) as DA.
  rewrite TR. apply parTriple_dae_intro2. assumption.
  noSyncNow_tac. apply NS in DA. decompAnd2 DA NDA1 NDA2.
  apply NDA2. simpl in MS. rewrite MS. assumption. Qed.

Lemma switchListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchListenStateEnt e -> e -ED- d ->> e' 
  -> False. urgency_pre_tac2 switchListenStateEnt switchListenStateProt
  switchListenState.
  (*We use (paused_switch) to show that the listener component is paused*)
  assert (switchStateProt p0) as SP. rewrite TR. constructor. apply switLisSt.
  assumption. lets PS : paused_switch U. rewrite <- PS in SP. rewrite TR in SP.
  (*Now a synchronisation is shown on unpause.*)
  del_triple_sort_tac. assert (pausedState p3) as PS3. inversion SP. assumption.
  lets PIU : paused_unpause_in_sort PS3. lets SOU : switchListen_unpause_out_sort TS.
  apply SORT2_3 in SOU. apply SOU. apply PIU. Qed.


(***************************** Path predicates *****************************)
(**In here, results about the path predicates. Mostly what we're concerned
with is preservation of the path predicates.*)

(*IF THIS SECTION GETS LARGE, WE CAN MIGRATE TO A SEPARATE PATH PREDICATE FILE*)

(*Develop general tactics for the path predicates?*)

Lemma msgAbortPathEnt_urgent e e' d :
  reachableEnt e -> msgAbortPathEnt e ->
  e -ED- d ->> e' -> False. intro.
  introz U. inversion U; subst.
  (*Inversion and then lift individual-stae urgency results.*)
  assert (gotMsgStateEnt m'' l' ([|p, l, h, k|])).
  econstructor; eassumption.
  eapply gotMsgStateEnt_urgent; eassumption.
  assert (gotRangeStateEnt m'' r ([|p, l, h, k|])).
  econstructor; eassumption.
  eapply gotRangeStateEnt_urgent; eassumption.
  assert (currCompStateEnt m'' r ([|p, l, h, k|])).
  econstructor; eassumption.  
  eapply currCompStateEnt_urgent; eassumption.
  assert (abortOvlpStateEnt ([|p, l, h, k|])).
  econstructor; eassumption.  
  eapply abortOvlpStateEnt_urgent; eassumption. Qed.

(** The interface component is irrelevant to the msgAbortPath.*)
Lemma msgAbort_inter_irrel p l h h' k :
  msgAbortPathEnt ([|p, l, h, k|]) ->
  msgAbortPathEnt ([|p, l, h', k|]). Admitted.  

(***************************** Delay Behaviour *****************************)

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening_pre (e e' : Entity) (d : Delay) :
  reachableEnt e -> e -ED- d ->> e' -> 
  abortOvlpStateEnt e \/ badOvlpStateEnt e \/ listeningStateEnt e \/ pausedStateEnt e.
  introz U. Admitted. (*D- reachableEnt*)
(**Proof: Since the entity is reachable, we know it has a listener
component (...reachableProt_triple...), so we do a case analysis as to what the location
of the listener component is. In most cases, we can show by simple urgency results that
a discrete action is possible via the listener synchronising with another component of
the entity. The remaining cases that aren't urgent are exactly the conclusion to this
result, and we're done.*)

(*Gives the possible states of the overlap component if a delay is possible.*)
Theorem del_ovlp (e e' : Entity) (d : Delay) : 
  reachableEnt e -> e -ED- d ->> e' ->
  dormantStateEnt e \/ tfsCurrStateEnt e \/
  exists m, exists t, exists x, exists y, ovWaitStateEnt m t x y e . Admitted. (*D- reachableEnt*)
(**Proof: Case analyse the overlap component of the software
process in e and eliminate most other possibilities by simple urgency results.
For the tfsListen case, apply (del_listening_pre). A corollary of this is that
the listener component is always capable of input on unpause or output on bad
or abort, and since tfsListen can do all three, a synch is always possible,
hence our urgency by progress. This should cover all states except those in our
conclusion, and we're done.*)

(**A reachable entity that can delay is in the listening state.*)
Theorem del_listening (e e' : Entity) (d : Delay) :
  reachableEnt e -> e -ED- d ->> e' -> listeningStateEnt e. Admitted. (*D- reachableEnt*)
(**Proof: First we apply (del_listening_pre), to get that
we are either in abortOvlp, badOvlp, paused or listening. If the last case
is true, then we are done. From here, we apply (del_ovlp) to further get
dormant, tfsCurr or ovWait as possibilities for the current state. Now,
if we are paused, then by (paused_switch) we are switchState- but this
contradicts the three possibilities for an overlap state, so it must be
thrown away. Hence we are either abortOvlp or badOvlp. But all three overlap
possibilities can input on both abort and bad, so in all six cases a synchronisation
is possible. Hence we arrive at our contradiction and conclude listening.
>Could use more automation in the tactic maybe? Pull out the software component,
apply the two previous results, and run some sort of auto that eliminates all the
cases that can synch.*)

(***************************** Lifted State Predicate Results *****************************)

Lemma switchCurr_switch_ent (e : Entity) :
  switchCurrStateEnt e -> switchStateEnt e. intros. 
  inversion H. inversion H0. do 2 constructor.
  apply switCurSt. assumption. Qed.

(*LOCAL TIDY*)

(** If the software components of an entity transition are not equal, then
the transition is necessarily a tau action, and either the process performs a tau,
synchs with the interface, synchs with the mode state or reads the current position.*)
Lemma link_ent_proc_neq_disc p p' h h' l l' k k' a :
  p <> p' -> [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  a = aeTau /\ ( 
  p -PA- tauAct -PA> p' \/
  (exists h' c v, p -PA- c ;! v -PA> p' /\ h -i- c {? v -i> h') \/
  (exists h' c v, p -PA- c ;? v -PA> p' /\ h -i- c {! v -i> h') \/
  (exists k' c m, p -PA- c ;! [baseMode m] -PA> p' /\ k -ms- c .? m -ms> k') \/
  (exists k' c m, p -PA- c ;? [baseMode m] -PA> p' /\ k -ms- c .! m -ms> k') \/
  (exists k' c, p -PA- c *! -PA> p' /\ k -ms- c @? -ms> k') \/
  (exists k' c, p -PA- c *? -PA> p' /\ k -ms- c @! -ms> k') \/
  p -PA- chanPos ;? [basePosition l] -PA> p').
  intros. inversion H0; (split;[ try reflexivity | ]);
  try (subst; contradict H; reflexivity).
  left; repeat eexists; eassumption.
  right; left; repeat eexists; eassumption.
  right. right. left. repeat eexists; eassumption.
  right. right. left. repeat eexists; eassumption.
  do 6 right. left. repeat eexists; eassumption.
  do 5 right. left. repeat eexists; eassumption.
  do 4 right. left. repeat eexists; eassumption.
  do 3 right. left. repeat eexists; eassumption.
  do 4 right. left. repeat eexists; eassumption.
  repeat right. repeat eexists; eassumption.
  Qed.


Lemma nextEq_mode (m' m'' : Mode) (e : Entity) :
  nextEqStateEnt m' m'' e -> nextModeEnt m' e.
  introz U. inversion U. Admitted. (*D*)

Lemma nextMode_ent_mState p l h k m :
  nextModeEnt m ([|p, l, h, k|]) -> nextModeMState k = Some m.
  introz U. Admitted. (*D*)

Lemma stepEnt_disc_pres_pos (e e' : Entity) a :
  e -EA- a ->> e' -> posEnt e = posEnt e'. intros.
  destruct e, e'. inversion H; reflexivity. Qed.

Ltac ent_disc_pres_pos_tac := match goal with
  [V : [|_, ?l, _, _|] -EA- ?b ->> [|_, ?l', _, _|] |- _ ] =>
  let EDP := fresh "EDP" in
  lets EDP : stepEnt_disc_pres_pos V; simpl in EDP end.

Lemma gotMsg_gotRange_track_ent (m m' : Mode) (l l' l1 : Position)
  (r : Distance) (p p' : ProcTerm) h h' k k' a :
  gotMsgStateEnt m l1 ([|p, l, h, k|]) ->
  gotRangeStateEnt m' r ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  l = l' /\ m = m' /\
  r = {| distance := dist2d l l1 -nn- speedMax *nn* msgLatency |}.
  Admitted.
(*Proof: Entity tracking result: possibly use generic tactic? Use software tracking
result? Use inter-component relationship result/tactics?*)
(*+*)
Lemma gotRange_currPincCheck_track_ent (m2 m1' m2' : Mode) (l l' : Position)
  (r r' : Distance) (p p' : ProcTerm) h h' k k' a :
  gotRangeStateEnt m2 r ([|p, l, h, k|]) ->
  currPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  m2 = m2' /\ r = r' /\ m1' = currModeMState k.
  Admitted.
(*+*)
Lemma currComp_listening_track_ent m'' r l l' p p' h h' k k' a :
  currCompStateEnt m'' r ([|p, l, h, k|]) ->
  listeningStateEnt ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  k -ms- chanMStable @! -ms> k' /\ h = h'. Admitted.
  (*Add entity-level tracking result.*)
(*+*)
Lemma currComp_nextPincCheck_track_ent (m2 m1' m2' : Mode) (l l' : Position)
  (r r' : Distance) (p p' : ProcTerm) h h' k k' a :
  currCompStateEnt m2 r ([|p, l, h, k|]) ->
  nextPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  m2 = m2' /\ r = r' /\ nextModeMState k = Some m1'.
  Admitted.

Lemma ovReady_ovWait_track_ent m m' t t' x' y' l0 a
  p p' l l' h h' k k' :
  ovReadyStateEnt m t l0 ([|p, l, h, k|]) ->
  ovWaitStateEnt m' t' x' y' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p -PA- chanOutProc ;! [baseMode m, basePosition l0] -PA> p' /\
  h -i- chanOutProc {? [baseMode m, basePosition l0] -i> h' /\
  k = k' /\ m = m' /\ l = l0.
  (*Some aspects of the proof e.g. l = l0 may require separate results.
  Maybe they already exist?*)Admitted.

Lemma tfsStart_next_ent e e' a :
  e -EA- a ->> e' -> tfsStartStateEnt e ->
  tfsStartStateEnt e' \/ exists m, tfsNextStateEnt m e'.
  Admitted. (*#fwd-track-lift-ent*)
  
Lemma tfsNext_next_ent e e' a m :
  e -EA- a ->> e' -> tfsNextStateEnt m e ->
  tfsNextStateEnt m e' \/ tfsCurrStateEnt e'.
  Admitted. (*#fwd-track-lift-ent*)

Lemma tfsCurr_next_ent e e' a :
  e -EA- a ->> e' -> tfsCurrStateEnt e ->
  tfsCurrStateEnt e' \/ tfsBcStateEnt e'.
  Admitted. (*#fwd-track-lift-ent*)

Lemma tfsBc_next_ent e e' a :
  e -EA- a ->> e' -> tfsBcStateEnt e ->
  tfsBcStateEnt e' \/ tfsListenStateEnt e'.
  Admitted. (*#fwd-track-lift-ent*)

Lemma tfsListen_next_ent e e' a :
  e -EA- a ->> e' -> tfsListenStateEnt e ->
  tfsListenStateEnt e' \/ dormantStateEnt e'.
  Admitted. (*#fwd-track-lift-ent*)

(*A simpl linking theorem from entity to output list, saying that either
interfaces are equal or one transitions to the other by some input or
some output.*)
Lemma link_ent_outList p p' l l' k k' li li' lo lo' ln ln' b :
  [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
  [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
  lo = lo' \/ exists v, outList lo -tl- v ?? -tl> outList lo'
  \/ outList lo -tl- v !! -tl> outList lo'. Admitted. (*5*)
  (*Proof idea: Use existing ent_inter link, use some auto tactic to eliminate
  a load of cases, then prove the rest by some interface linking tactic. #interface-linking*)

(*- LOCAL TIDY*)