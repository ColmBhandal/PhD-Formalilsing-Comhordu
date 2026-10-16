(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.ProtocolBridge.

(***************************** Misc *****************************)

(*Requires reachableEnt to be defined before it is proved.*)
Lemma reachable_ent_prot p l h k : reachableEnt ([| p, l, h, k |]) ->
  reachableProt p. intros. Admitted. (*D*)

Lemma nextModeEnt_not_stable m1 m2 p l h :
  nextModeEnt m1 ([|p, l, h, m2|]) -> False. intros. Admitted. (*D*)
(*Proof: immediate once nextModeEnt is defined.*)

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
Lemma input_incomingEnt (v : list BaseType) (e e' : Entity) (l : Position) (r : Distance) :
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

(* begin helpers for gotRangeStateEnt_urgent *)
(** A process in the gotRange state can read any mode on the channel mCurr.*)
Lemma gotRangeStateEnt_urgent_aux1 (p : ProcTerm) (m m0 : Mode) (r : Distance) :
  gotRangeState m r p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
  activation_tac. Qed.
(* end helpers *)

Lemma gotRangeStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  reachableEnt e -> gotRangeStateEnt m r e -> e -ED- d ->> e' -> False.
Proof.
  intros RE GS DEL. destruct e as [p l h k].
  inversion GS; subst.
  match goal with [H : gotRangeStateProt _ _ _ |- _] => inversion H; subst end.
  eapply ent_del_mCurr_in_not; [ | eassumption].
  intro m0. dae_listener.
  eapply gotRangeStateEnt_urgent_aux1. eassumption.
Qed.

(* begin helpers for currCompStateEnt_urgent *)
(** A process in the currComp state can input on mStable.*)
Lemma currCompStateEnt_urgent_aux1 (p : ProcTerm) (m : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMStable *?).
  activation_tac. Qed.

(** A process in the currComp state can input any mode on mNext.*)
Lemma currCompStateEnt_urgent_aux2 (p : ProcTerm) (m m0 : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMNext ;? [baseMode m0]).
  activation_tac. Qed.
(* end helpers *)

Lemma currCompStateEnt_urgent (e e' : Entity) (d : Delay) m r :
  reachableEnt e -> currCompStateEnt m r e -> e -ED- d ->> e' -> False.
Proof.
  intros RE CS DEL. destruct e as [p l h k].
  inversion CS; subst.
  match goal with [H : currCompStateProt _ _ _ |- _] => inversion H; subst end.
  eapply ent_del_mStable_mNext_in_not; [ | | eassumption].
  - dae_listener. eapply currCompStateEnt_urgent_aux1. eassumption.
  - intro m0. dae_listener.
    eapply currCompStateEnt_urgent_aux2. eassumption.
Qed. (*Relies on the result that the mode state can always
EITHER output on next or stable. #modif-urgent*)

Lemma abortOvlpStateEnt_urgent (e e' : Entity) (d : Delay) :
  reachableEnt e -> abortOvlpStateEnt e -> e -ED- d ->> e' -> False.
  Admitted.

Lemma tfsStartStateEnt_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsStartStateEnt e -> e -ED- d ->> e' -> False.
  urgency_pre_tac2 tfsStartStateEnt tfsStartStateProt tfsStartState.
  (*The overlap reads the current mode, which the mode state always offers.*)
  eapply ent_del_sync_mState_not; [ | | eassumption].
  - rewrite TR. dae_overlap. eapply tfsStart_mCurr_in. eassumption.
  - apply modeState_curr_enabled.
Qed.

Lemma tfsListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsListenStateEnt e -> e -ED- d ->> e' 
  -> False.
  (*Some pre-tactics*)
  urgency_pre_tac2 tfsListenStateEnt tfsListenStateProt tfsListenState.
  (**It can be shown that tfsListen is only reached by the overlap when the listener
  component is paused. This in turn implies the listener component is listening on the
  channel unpause. Since the overlap component can clearly output on this channel, a
  synch is possible, and so by maximal progress delay cannot happen.*)
  lets PA : tfsListen_paused TP. assert (pausedState p3) as P3 by (inversion PA; assumption).
  lets DP : link_ent_soft_del U1. rewrite TR in DP.
  triple_del_sync_not DP (tfsListen_unpause_out _ TS) (paused_unpause_in _ P3).
Qed.

Lemma tfsNext_urgent : forall (m : Mode) (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsNextStateEnt m e -> e -ED- d ->> e' -> False.
  intro m. intros e e' d. introz U.
  (*Need to ensure the current mode equals the parameter to tfsNext.*)
  lets TCM : tfsNext_currMode U U0.
  urgency_pre_tac2_1 tfsNextStateEnt tfsNextStateProt tfsNextState.
  lets FS : failSafeSucc_successor m.
  assert (k0 -mtr-> failSafeSucc m) as FS2. simpl in TCM.
  rewrite TCM. assumption.
  (*The mode state reads either mStable or the fail-safe successor on mNext, and the
  overlap offers both.*)
  destruct (mState_stable_next_enabled _ _ FS2) as [MS | MS];
  (eapply ent_del_sync_mState_not; [ | | eassumption]).
  - rewrite TR. dae_overlap. eapply tfsNext_mStable_out. eassumption.
  - exact MS.
  - rewrite TR. dae_overlap. eapply tfsNext_mNext_out. eassumption.
  - exact MS.
Qed.

Lemma bcReady_urgent (m : Mode) (l : Position) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> bcReadyStateEnt m l e -> e -ED- d ->> e' 
  -> False. urgency_pre_tac2_2 bcReadyStateEnt bcReadyStateProt bcReadyState.
  (**Proof: By activation, the bcReady state can be shown to be capable of outputting on
  chanOutProc. Separately, the interface component can be shown to always be available for
  input on this channel, i.e. it can always buffer a message from the software component.
  Thus, a synch between software and interface is possible, violating the "noSynch" condition
  that must hold for the entity to delay. Hence delay cannot happen.*)
  eapply ent_del_sync_inter_not; [ | | eassumption].
  - rewrite TR. dae_broadcast. eapply bcReady_outProc_out. eassumption.
  - apply interface_outProc_in.
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
  eapply ent_del_sync_mState_not; [ | | eassumption].
  - rewrite TR. dae_overlap. apply ovAbort_stable_out. assumption.
  - apply unstable_stable_in. exact OUS.
Qed.

Lemma tfsBc_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> tfsBcStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2 tfsBcStateEnt tfsBcStateProt tfsBcState.
  lets TOT : tfsBc_trans_out TS. lets DP : link_ent_soft_del U1. rewrite TR in DP.
  (*Case analysis on the state of the broadcast component. If it is in either the
  wait or the sleeping state, then an input on trans is possible, which can synch with
  the output on trans from tfsBc.*)
  inversion BC as [m x BW | SL | m l1 BR].
  - triple_del_sync_not DP (bcWait_trans_in _ _ _ BW) TOT.
  - triple_del_sync_not DP (sleep_trans_in _ SL) TOT.
  (*Otherwise, the broadcast component is in the ready state, in which case we
  already have urgency from bcReady-urgent.*)
  - assert (bcReadyStateEnt m l1 ([|p0, l0, h0, k0|])) as BCE. constructor.
    rewrite TR. constructor. assumption. lets BCU : bcReady_urgent U BCE.
    apply BCU. apply U1.
Qed.

Lemma switchBc_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchBcStateEnt m e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2_1 switchBcStateEnt switchBcStateProt switchBcState.
  lets TOT : switchBc_wake_out TS. lets DP : link_ent_soft_del U1. rewrite TR in DP.
  (*Case analysis on the state of the broadcast component. If it is in either the
  wait or the sleeping state, then an input on wake is possible, which can synch with
  the output on wake from switchBc.*)
  inversion BC as [m0 x BW | SL | m0 l1 BR].
  - triple_del_sync_not DP (bcWait_wake_in m _ _ _ BW) TOT.
  - triple_del_sync_not DP (sleeping_wake_in m _ SL) TOT.
  (*Otherwise, the broadcast component is in the ready state, in which case we
  already have urgency from bcReady-urgent.*)
  - assert (bcReadyStateEnt m0 l1 ([|p0, l0, h0, k0|])) as BCE. constructor.
    rewrite TR. constructor. assumption. lets BCU : bcReady_urgent U BCE.
    apply BCU. apply U1.
Qed.

Lemma swithcCurr_urgent (m : Mode) : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchCurrStateEnt e -> e -ED- d ->> e' 
  -> False. intros e e' d. introz U. lets Q : U.
  urgency_pre_tac2 switchCurrStateEnt switchCurrStateProt switchCurrState.
  (*Apply (switchCurr-next-Mode) to assert that there is some next mode.*)  
  lets SMS : switchCurr_mState U U0. decompEx2 SMS m1 m2 MS.
  (*Then it is easy to show that the mode state is capable of inputting
  on mCurr, which complements the output that is enabled in this state,
  and so we're urgent.*)
  eapply ent_del_sync_mState_not; [ | | eassumption].
  - rewrite TR. dae_overlap. apply switchCurr_mCurr_out. assumption.
  - simpl in MS. rewrite MS. apply mst_tout_mCurr_in.
Qed.

Lemma switchListen_urgent : forall (e e' : Entity) (d : Delay),
  reachableEnt e -> switchListenStateEnt e -> e -ED- d ->> e' 
  -> False. urgency_pre_tac2 switchListenStateEnt switchListenStateProt
  switchListenState.
  (*We use (paused_switch) to show that the listener component is paused*)
  assert (switchStateProt p0) as SP. rewrite TR. constructor. apply switLisSt.
  assumption. lets PS : paused_switch U. rewrite <- PS in SP. rewrite TR in SP.
  assert (pausedState p3) as PS3. inversion SP. assumption.
  (*Now a synchronisation is shown on unpause.*)
  lets DP : link_ent_soft_del U1. rewrite TR in DP.
  triple_del_sync_not DP (switchListen_unpause_out _ TS) (paused_unpause_in _ PS3).
Qed.


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
  msgAbortPathEnt ([|p, l, h', k|]).
Proof.
  intro H. inversion H; subst.
  - eapply mapMsg; try reflexivity; eassumption.
  - eapply mapGrng; try reflexivity; eassumption.
  - eapply mapCuco; eassumption.
  - eapply mapAbort; eassumption.
Qed.  

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

Lemma nextEq_mode (m' m'' : Mode) (e : Entity) :
  nextEqStateEnt m' m'' e -> nextModeEnt m' e.
  introz U. inversion U. Admitted. (*D*)

Lemma nextMode_ent_mState p l h k m :
  nextModeEnt m ([|p, l, h, k|]) -> nextModeMState k = Some m.
  introz U. Admitted. (*D*)

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
  
(* begin helpers for tfsNext_next_ent *)
Lemma tfsNext_next_ent_currN : ProcEquiv.bisimulation (tfsCurrN $([])$) tfsCurr.
Proof. apply app_bisim_nil. reflexivity. Qed.

Lemma tfsNext_next_ent_nextN (m : Mode) :
  ProcEquiv.bisimulation (tfsNextN $([eBase (baseMode m)])$) (tfsNext m).
Proof.
  replace (tfsNext m)
    with (subProcTerm (listsToSub [vM] [eBase (baseMode m)]) (tfsNext (eVar vM))).
  - apply app_bisim_def. reflexivity.
  - unfold tfsNext. simpl. unfold update. unfold varEq.
    destruct (varEqDec vM vM) as [_ | C]; [reflexivity | contradiction C; reflexivity].
Qed.

Lemma tfsNext_next_ent_proc m p p' b : tfsNextState m p -> p -PA- b -PA> p' ->
  tfsNextState m p' \/ tfsCurrState p'.
Proof.
  unfold tfsNextState, tfsCurrState. intros B T.
  destruct (bisim_step_disc _ _ _ _ B T) as [q [Tq Bq]].
  unfold tfsNext in Tq. inversion Tq; subst.
  - match goal with [V : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    right. eapply ProcEquiv.bisim_trans; [eassumption | apply tfsNext_next_ent_currN].
  - match goal with [V : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    left. eapply ProcEquiv.bisim_trans; [eassumption | apply tfsNext_next_ent_nextN].
Qed.
(* end helpers *)

Lemma tfsNext_next_ent e e' a m :
  e -EA- a ->> e' -> tfsNextStateEnt m e ->
  tfsNextStateEnt m e' \/ tfsCurrStateEnt e'.
Proof.
  intros T N. destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  inversion N as [p0 l0 h0 k0 NP]; subst.
  inversion NP as [p1 p2 p3 NP2]; subst.
  destruct (link_ent_soft_disc _ _ _ _ _ _ _ _ _ T) as [E | [b TP]].
  - subst. left. constructor. constructor. assumption.
  - link_partripdiscex_tac E p1' p2' p3'. subst.
    link_partripdiscW2_tac TP W. destruct W as [E2 | [b' T2]]; subst.
    + left. constructor. constructor. assumption.
    + destruct (tfsNext_next_ent_proc _ _ _ _ NP2 T2) as [X | X].
      * left. constructor. constructor. assumption.
      * right. constructor. constructor. assumption.
Qed.

(* begin helpers for tfsCurr_next_ent *)
(** Support for the #fwd-track-lift-ent family (tfsCurr/tfsBc/tfsListen _next_ent):
forward tracking of an overlap-component state predicate, lifted from single
process terms (where the state predicates are bisimilarity classes) to entities.*)

(** Generic lifting: a forward-tracking result for an overlap state predicate X
lifts from process terms to entities.*)
Lemma tfsCurr_next_ent_lift (X Y : ProcTerm -> Prop) e e' a :
  (forall q q' b, q -PA- b -PA> q' -> X q -> X q' \/ Y q') ->
  e -EA- a ->> e' -> liftProcEnt (liftOverlap X) e ->
  liftProcEnt (liftOverlap X) e' \/ liftProcEnt (liftOverlap Y) e'.
Proof.
  intros F S L. inversion L as [p l h k LO]; subst.
  inversion LO as [p1 p2 p3 X2]; subst.
  destruct e' as [p' l' h' k'].
  destruct (link_ent_soft_disc _ _ _ _ _ _ _ _ _ S) as [E | [b B]].
  - subst p'. left. constructor. constructor. assumption.
  - link_partripdiscex_tac E p1' p2' p3'. subst p'.
    link_partripdiscW2_tac B W. destruct W as [E | [b' B']].
    + subst p2'. left. constructor. constructor. assumption.
    + destruct (F _ _ _ B' X2) as [Z | Z]; [left | right];
      constructor; constructor; exact Z.
Qed.

(** Closes a goal [S p'] (S a bisimilarity-class state predicate) from a
hypothesis [p' ~p~ n $(l)$] by unfolding the application.*)
Ltac tfsCurr_next_ent_close_tac :=
  match goal with [B1 : ProcEquiv.bisimulation ?p' ?q' |- _] =>
    hnf; eapply ProcEquiv.bisim_trans; [exact B1 | ];
    eapply ProcEquiv.bisim_trans; [apply app_bisim | ];
    rewrite unfoldApp_body; clean_proc; apply ProcEquiv.bisim_refl
  end.

(** Process-level forward tracking for a goal of the form
[p -PA- b -PA> p' -> S p -> S1 p' \/ ... \/ Sn p'], where S, S1..Sn are
bisimilarity-class state predicates and the body of S is a sum of prefixes
whose continuations are name applications.*)
Ltac tfsCurr_next_ent_fwd_tac :=
  let S := fresh "S" in let B := fresh "B" in
  intros S B; hnf in B;
  let q' := fresh "q'" in let S1 := fresh "S1" in let B1 := fresh "B1" in
  destruct (bisim_step_disc _ _ _ _ B S) as [q' [S1 B1]];
  clear S B;
  try unfold tfsCurr in S1; try unfold tfsBc in S1; try unfold tfsListen in S1;
  repeat invert_trans; simpl in B1;
  repeat match goal with [ |- _ \/ _ ] =>
    first [left; solve [tfsCurr_next_ent_close_tac] | right] end;
  tfsCurr_next_ent_close_tac.

(** Process-level forward tracking from the tfsCurr state.*)
Lemma tfsCurr_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsCurrState p -> tfsCurrState p' \/ tfsBcState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsCurr_next_ent e e' a :
  e -EA- a ->> e' -> tfsCurrStateEnt e ->
  tfsCurrStateEnt e' \/ tfsBcStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsCurrState tfsBcState _ _ _ tfsCurr_next_ent_aux S T).
Qed.

(* begin helpers for tfsBc_next_ent *)
(** Process-level forward tracking from the tfsBc state
(uses the #fwd-track-lift-ent support from tfsCurr_next_ent).*)
Lemma tfsBc_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsBcState p -> tfsBcState p' \/ tfsListenState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsBc_next_ent e e' a :
  e -EA- a ->> e' -> tfsBcStateEnt e ->
  tfsBcStateEnt e' \/ tfsListenStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsBcState tfsListenState _ _ _ tfsBc_next_ent_aux S T).
Qed.

(* begin helpers for tfsListen_next_ent *)
(** Process-level forward tracking from the tfsListen state
(uses the #fwd-track-lift-ent support from tfsCurr_next_ent).*)
Lemma tfsListen_next_ent_aux p p' b :
  p -PA- b -PA> p' -> tfsListenState p -> tfsListenState p' \/ dormantState p'.
Proof. tfsCurr_next_ent_fwd_tac. Qed.
(* end helpers *)

Lemma tfsListen_next_ent e e' a :
  e -EA- a ->> e' -> tfsListenStateEnt e ->
  tfsListenStateEnt e' \/ dormantStateEnt e'.
Proof.
  intros S T.
  exact (tfsCurr_next_ent_lift tfsListenState dormantState _ _ _ tfsListen_next_ent_aux S T).
Qed.

(*- LOCAL TIDY*)