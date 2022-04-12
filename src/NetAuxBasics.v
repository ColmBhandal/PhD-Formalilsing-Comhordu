(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import Reals.
Require Import List.
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.GenTacs.

(*IDEA: MIGRATE SOME OF THE CONTENTS OF THE FILE OVER VARIUOS NAB (NET-AUX-BASICS)
PREFIXED FILES, THEN *EXPORT* THEM HERE, SO THAT THIS FILE JUST ACTS AS A
HUB RELAYING THE CONTENTS OF THOSE FILES. WHY? IT'S GETTING JOLLY BIG!*)

(********************************* Some basic definitions *********************************)

Inductive initialNet : Network -> Prop :=
  | initNtNil : initialNet []
  | initNtCons e n : initialEnt e -> initialNet n ->
    initialNet (e :: n).
  
Inductive reachableNet : Network -> Type :=
  | reachNetInit (n : Network) : initialNet n -> reachableNet n
  | reachNetDisc (n n' : Network) (a : ActDiscNet) : reachableNet n ->
    n -NA- a -NA> n' -> reachableNet n'
  | reachNetDel (n n' : Network) (d : Delay) : reachableNet n ->
    n -ND- d -ND> n' -> reachableNet n'.

Lemma link_net_prot_reach n p l h k i :
  reachableNet n ->  [|p, l, h, k|] @ i .: n -> reachableProt p.
  Admitted. (*6*)
(**Proof: Intermediate results from net to ent and ent to prot.*)


Ltac link_netprotreach_tac U :=
  match goal with
  [H : reachableNet ?n, H0 : [|_, _, _, _|] @ _ .: ?n |- _] =>
  let U1 := fresh U in lets U1 : link_net_prot_reach H H0
  end.

Parameter currModeNet : Mode -> nat -> Network -> Prop.
(**Idea: Lift currModeEnt*)

(*transGuard t i n says that the entity at position i in n is transitioning
 from one mode to another and the guard on the transition is t.*)
Inductive transGuard (t : Time) (i : nat) (n : Network) : Prop :=
  | tgWitness (p : ProcTerm) (l : Position) (h : Interface) (m m' : Mode) :
    [| p , l , h , <| m , m' , t |> |] @ i .: n -> transGuard t i n.

Parameter nextModeNet : Mode -> nat -> Network -> Prop.
(**Idea: Lift nextModeEnt*)

(*inPosNet l i n says that the entity number i in n has position l.*)
Inductive inPosNet (l : Position) (i : nat) (n : Network) : Prop :=
  | ipWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
    [| p , l , h , k |] @ i .: n -> inPosNet l i n.

(*dist2d i i' n x says that the entities i and i' are separated by x in n.*)
Inductive distNet (i i' : nat) (n : Network) : Distance -> Prop :=
  | dnWitness (l l' : Position) : inPosNet l i n -> inPosNet l' i' n ->
    distNet i i' n (distFun l l').	

(*outgoing v t i n says that the message v with timestamp t is in the output queue of the interface component of the entity i in the network n.*)
Inductive outgoing (v : list Base) (t : Time) (i : nat) (n : Network) : Prop :=
  | ogWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , t )>) (outList lo) -> outgoing v t i n.

(*incomingNet v i n says that the message v is in the input queue of the interface component of the entity i in the network n.
Note: Even though the input queue is effectively untimed messages, it is modelled as a timed list, with 
timestamps simply set to 0, hence "v in Li" becomes "<v, 0> in Li" to be more pedantic about it.*)
Inductive incomingNet (v : list Base) (i : nat) (n : Network) : Prop :=
  | icWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , zeroTime )>) (inList li) -> incomingNet v i n.


(*incomingNetNotif v t i n says that the message v with timestamp t is in the
notification queue of the interface component of the entity i in the network n.*)
Inductive incomingNetNotif (v : list Base) (t : Time) (i : nat) (n : Network) : Prop :=
  | icnWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , t )>) (notifList ln) -> incomingNetNotif v t i n.
			 
Inductive mState_in_net (k : ModeState) (i : nat) (n : Network) : Prop :=
  minet (p : ProcTerm) (l : Position) (h : Interface) :
  [|p, l, h, k|] @ i .: n -> mState_in_net k i n.



(********************************* Lifting Protocol Predicates *********************************)

(**The lifting function we use to lift predicates from the protocol level to the
entity level.*)
Inductive liftEntNet (X : Entity -> Prop) (i : nat) (n : Network) : Prop :=
  | lenWitness (e : Entity) : X e -> e @ i .: n -> liftEntNet X i n.

(*----------------Simple Lifted Predicates----------------*)

(**Broadcast*)
Definition bcWaitStateNet m x := liftEntNet (bcWaitStateEnt m x).
Definition sleepingStateNet := liftEntNet sleepingStateEnt.
Definition bcReadyStateNet m l := liftEntNet (bcReadyStateEnt m l).


(**Overlap*)
Definition dormantStateNet := liftEntNet dormantStateEnt.
Definition tfsStartStateNet := liftEntNet tfsStartStateEnt.
Definition initStateNet m := liftEntNet (initStateEnt m).
Definition ovWaitStateNet m t x y := liftEntNet (ovWaitStateEnt m t x y).
Definition ovReadyStateNet m t l := liftEntNet (ovReadyStateEnt m t l).
Definition switchCurrStateNet := liftEntNet switchCurrStateEnt.
Definition switchListenStateNet := liftEntNet switchListenStateEnt.
Definition switchBcStateNet m := liftEntNet (switchBcStateEnt m).
Definition tfsCurrStateNet := liftEntNet tfsCurrStateEnt.
Definition tfsBcStateNet := liftEntNet tfsBcStateEnt.
Definition tfsListenStateNet := liftEntNet tfsListenStateEnt.
Definition pausedStateNet := liftEntNet pausedStateEnt.
Definition tfsNextStateNet m := liftEntNet (tfsNextStateEnt m).

(**Listener*)
Definition listeningStateNet := liftEntNet listeningStateEnt.
Definition currCompStateNet m'' r := liftEntNet (currCompStateEnt m'' r).
Definition badOvlpStateNet := liftEntNet badOvlpStateEnt.
Definition rangeBadStateNet m := liftEntNet (rangeBadStateEnt m).
Definition currEqStateNet m m'' := liftEntNet (currEqStateEnt m m'').


(*----------------Compound Lifted Predicates----------------*)


(**Broadcast*)
Definition broadcastStateNet :=  liftEntNet broadcastStateEnt.

(**Overlap*)
Definition overlapStateNet := liftEntNet overlapStateEnt.
Definition tfsStateNet := liftEntNet tfsStateEnt.
Definition nextSinceStateNet := liftEntNet (nextSinceStateEnt).
Definition switchStateNet := liftEntNet switchStateEnt.

(**Listener*)
Definition listenerStateNet := liftEntNet listenerStateEnt.
Definition ovAbortStateNet := liftEntNet ovAbortStateEnt.


(********************************* State Predicate Results *********************************)

Conjecture tfsStateNet_dec : forall (i : nat) (n : Network), decidable (tfsStateNet i n).
(**Proof: Obvious*)

Conjecture tfsCurrNet_dec : forall (i : nat) (n : Network),
  decidable (tfsCurrStateNet i n).
(**Proof: Obvious*)

(*Pre-requisite: some sort of lifting tactic*)
Lemma tfsCurrStateNet_bktrk_net : forall (n n' : Network) (i : nat) (a : ActDiscNet),
  tfsCurrStateNet i n' -> n -NA- a -NA> n' ->
  tfsCurrStateNet i n \/
  (exists m mF, exists p,
  tfsNextStateNet m i n /\ failSafe mF /\
  mState_in_net (<| m, mF, modeTransTime m mF p |>) i n'). Admitted. (*6*)
(**Proof: Lift Back tracking and inter component relationships*)  

(*Pre-requisite: some sort of lifting tactic- maybe a generic lifting tactic taking
any predicate over a ProcTerm and lifting it to work over a network predicate?*)
Conjecture tfsCurrState_del_pres_net : forall (n n' : Network) (d : Delay) (i : nat),
  n -ND- d -ND> n' ->
  (tfsCurrStateNet i n <-> tfsCurrStateNet i n').
(**Proof: #del-pres-fwd-net #del-pres-bkwd-net*)

(*The only two possibilities for a change in mode state as per a discrete
transition are the standard mode switch or the mode switch to fail safe.*)
Lemma mState_switch_states : forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k k' : ModeState), reachableNet n -> k <> k' ->
  n -NA- a -NA> n' -> mState_in_net k i n -> mState_in_net k' i n' ->
  (tfsCurrStateNet i n /\ tfsBcStateNet i n') \/
  (switchCurrStateNet i n /\ switchListenStateNet i n'). Admitted. (*3*)
(**Proof: The mState_in_net predicates can be taken apart to show that there's an entity in the network. Then because the
network is reachable, the software component of this entity is a protocolState process. Also, it can be shown from the semantics of
entities that the only law (what about init?) that changes the mode state is that in which the software component outputs on mCurr.
Brute force analysis of the possible states of each 3 components of the softare component show that the only matching cases for this are
the two disjuncts. That is, the only capability a protocol process has of writing on mCurr is from the overlap component in those specific
states.*)

Conjecture tfsState_del_pres_net : forall (n n' : Network) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> (tfsStateNet i n <-> tfsStateNet i n').
(**Proof: #del-pres-fwd-net #del-pres-bkwd-net*)

Lemma switch_states_mState : forall (n n' : Network) (i : nat) (a : ActDiscNet)
  (m : Mode), n -NA- a -NA> n' -> switchCurrStateNet i n ->
  switchListenStateNet i n' -> nextModeNet m i n -> currModeNet m i n'. Admitted. (*3*)
(**Proof: Tracking shows us that the action must be tau, composed of an output from the software process on mCurr and an input
on the same by the mode state. Then it can be shown separately that an input on the mode state that is nextMode m yields a mode
state that it currMode m. Which can be lifted to currModeNet.*)

(** A network transition which sees a software component of some entity
transform to a different software term is necessarily a tau transition.*)
Lemma procNeq_tau_net p p' l l' h h' k k' n n' a i :
  [|p, l, h, k|] @ i .: n -> [|p', l', h', k'|] @ i .: n' ->
  n -NA- a -NA> n' -> p <> p' -> a = anTau. Admitted. (*7*)

(** The action linking a change from switchCurr to switchListen is always a tau.*)
Lemma switchCurr_listen_trans_tau (n n' : Network) (a : ActDiscNet) (i : nat) :
  n -NA- a -NA> n' -> switchCurrStateNet i n -> switchListenStateNet i n' ->
  a = anTau. introz U.
  (*First of all, let's set up the fact that there are entities with unequal software
  components.*)
  state_pred_net_destr U0. state_pred_net_destr U1.
  assert (p <> p0). unfold not; intro. subst.
  (*The rest follows from a more general result that if the software component changes state, then
  the action must be a tau. This in turn is true because all the other transitions preserve the
  software process- this more general result should be simple enough to prove*)
  Focus 2.
  eapply procNeq_tau_net. apply H0.
  eassumption. eassumption. eassumption.
  (*Solve the remaining goal by state-pred-elim and remove Focus*)
  Admitted.

(*LOCAL TIDY*)

Lemma tfsStart_tfs_net i n :
  tfsStartStateNet i n -> tfsStateNet i n. Admitted. (*#tfsNetLift #complexNetLift*)

Lemma tfsNext_tfs_net m i n :
  tfsNextStateNet m i n -> tfsStateNet i n. Admitted. (*#tfsNetLift #complexNetLift*)

Lemma tfsCurr_tfs_net i n :
  tfsCurrStateNet i n -> tfsStateNet i n. Admitted. (*#tfsNetLift #complexNetLift*)

Lemma tfsBc_tfs_net i n :
  tfsBcStateNet i n -> tfsStateNet i n. Admitted. (*#tfsNetLift #complexNetLift*)

Lemma tfsListen_tfs_net i n :
  tfsListenStateNet i n -> tfsStateNet i n. Admitted. (*#tfsNetLift #complexNetLift*)

(** The following three tactics are mostly simply auxiliaries to the main
result of fwd_track_net_tac.*)
(*Applies eexists up to 5 times (or not at all) before applying t- until
the application works.*)
Ltac first_eexists_5 t := first [t | (do 1 eexists);t | (do 2 eexists);t |
  (do 3 eexists);t | (do 4 eexists);t | (do 5 eexists);t].
Ltac econstr_easssump := econstructor; eassumption.
Ltac first_ex_econ_eass := first_eexists_5 econstr_easssump.

(** RE is the entity level result upon which this tactic works. Essentially,
this tactic lifts RE from the entity to the network level. Note that the tactic
assumes a disjunctive goal of two branches and may not work otherwise.*)
Ltac fwd_track_net_tac RE :=
  let U := fresh in let U0 := fresh in
  (*Destruct a load of things and set up the link*)
  intros U U0; destruct U0;
  let e' := fresh "e'" in let b := fresh "b" in
  let LNE := fresh "LNE" in
  link_netentdiscfwd_tac e' b LNE;
  (*The case of equality of entities is easy, we just substitute.*)
  [subst; left | match goal with [LNE1 : _ -EA- b ->> e', e : Entity,
  H0 : _ ?e |- _] =>
  (*Apply an underlying (lower-level) result*)
  lets LOW : RE LNE1 H0;
  or_flat; ex_flat; [left | right] end];
  first_ex_econ_eass.

Lemma tfsStart_next_net n n' a i :
  n -NA- a -NA> n' -> tfsStartStateNet i n ->
  tfsStartStateNet i n' \/ exists m, tfsNextStateNet m i n'.
  fwd_track_net_tac tfsStart_next_ent. Qed.

Lemma tfsNext_next_net m n n' a i :
  n -NA- a -NA> n' -> tfsNextStateNet m i n ->
  tfsNextStateNet m i n' \/ tfsCurrStateNet i n'.
  fwd_track_net_tac tfsNext_next_ent. Qed.

Lemma tfsCurr_next_net n n' a i :
  n -NA- a -NA> n' -> tfsCurrStateNet i n ->
  tfsCurrStateNet i n' \/ tfsBcStateNet i n'.
  fwd_track_net_tac tfsCurr_next_ent. Qed.

Lemma tfsBc_next_net n n' a i :
  n -NA- a -NA> n' -> tfsBcStateNet i n ->
  tfsBcStateNet i n' \/ tfsListenStateNet i n'.
  fwd_track_net_tac tfsBc_next_ent. Qed.

Lemma tfsListen_next_net n n' a i :
  n -NA- a -NA> n' -> tfsListenStateNet i n ->
  tfsListenStateNet i n' \/ dormantStateNet i n'.
  fwd_track_net_tac tfsListen_next_ent. Qed.

Lemma rangeBad_next_net m m'' i n n' a :
  n -NA- a -NA> n' -> rangeBadStateNet m'' i n -> currModeNet m i n ->
  rangeBadStateNet m'' i n' \/ currEqStateNet m m'' i n'.
  (*Proof: If it wasn't for the currModeNet entanglement, you'd just be able
  to do: fwd_track_net_tac rangeBad_next_ent, but something else needs to be
  done to account for this extra little feature of the proof.*)
  Admitted. (*D- rangeBad_next_ent*)

Lemma badOvlp_next_net i n n' a :
  n -NA- a -NA> n' -> badOvlpStateNet i n ->
  badOvlpStateNet i n' \/ listeningStateNet i n'.
  Admitted. (*D- badOvlp_next_ent*)
(*Proof: fwd_track_net_tac badOvlp_next_ent*)

Ltac netState_auto_pre := match goal with [U : [|_, _, _, _|] = _,
  U1 : _ $||$ _ $||$ _ = _ |- _] =>
  eapply lenWitness;[ | eassumption];
  rewrite <- U; eapply lifpe; rewrite <- U1 end; constructor.

(** Assume a network state predicate as the goal, and enough information in the
hypothesis to prove it: an entInNet, an equality between that entity and its
various components, and an equality between a process triple and the process of
that entity. Then this tactic should solve the goal.*)
Ltac netState_auto_tac :=
  netState_auto_pre; eassumption.

Lemma tfsState_elim_net i n :
  tfsStateNet i n -> tfsStartStateNet i n \/
  (exists m, tfsNextStateNet m i n) \/
  tfsCurrStateNet i n \/ tfsBcStateNet i n \/
  tfsListenStateNet i n. intro. inversion H. inversion H0.
  inversion H2. inversion H4.
  left. netState_auto_tac.
  right. left. eexists. netState_auto_tac.
  right. right. left. netState_auto_tac.
  right. right. right. left. netState_auto_tac.
  right. right. right. right. netState_auto_tac.
  Qed.

Lemma tfsListen_failSafe_net m i n :
  tfsListenStateNet i n -> currModeNet m i n -> failSafe m.
(*Proof: Similar result for tfsBc, and one for tfsCurr but for the next mode
rather than the curr mode- perhaps inter-component results will be lifted
for these?*) Admitted. (*#inter-component-lift-net*)

(*-LOCAL TIDY*)

Lemma tfs_currMode_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode) :
  n -NA- a -NA> n' -> currModeNet m i n -> ~ failSafe m ->
  tfsStateNet i n -> tfsStateNet i n'. introz U.
  (*Destruct the tfs state into its components and apply an array of
  network level fwd-tracking results.*)
  apply tfsState_elim_net in U2. or_flat; ex_flat; [ |
  rename H into OR | ..];[eapply tfsStart_next_net in OR |
  eapply tfsNext_next_net in OR | eapply tfsCurr_next_net in OR |
  eapply tfsBc_next_net in OR | ];
  try eassumption; or_flat; ex_flat.
  (*Now we're left with a nubmber of cases where, in the hypotheses,
  you have that some tfs<..>StateNet holds. From here, we use lifting
  results previously defined*)
  apply tfsStart_tfs_net; assumption.
  eapply tfsNext_tfs_net; eassumption.
  eapply tfsNext_tfs_net; eassumption.
  apply tfsCurr_tfs_net; assumption.
  apply tfsCurr_tfs_net; assumption.
  apply tfsBc_tfs_net; assumption.
  apply tfsBc_tfs_net; assumption.
  apply tfsListen_tfs_net; assumption.
  (*The only case that differs is where we are tfsListen. In this case
  we observe that the currMode is failSafe.*)
  false. apply U1. eapply tfsListen_failSafe_net; eassumption.
  Qed. 

Lemma paused_switch_net (n : Network) (i : nat) :
  reachableNet n -> (pausedStateNet i n <-> switchStateNet i n). Admitted. (*4*)
(**Proof: Lift result from entity level ultimately- analogous theorems except with
reachableProt and prot level state predicates.*)

Lemma bcWaitNet_del_bkwd (n n' : Network) (m : Mode) (x : Time)
  (i : nat) (d : Delay) : n -ND- d -ND> n' ->
  bcWaitStateNet m x i n' -> bcWaitStateNet m (x +dt+ d) i n.
  Admitted. (*4*)
(**Proof: Well, a backwards delay preservation would give us bcWaitState m x' i n for some x'. But forward tracking would then give us that
in the derivative state the second parameter is x' - d. So x = x' - d and so x' = x + d, as required.*)

(** An entity in an initial network is itself initial.*)
Lemma initialNet_ent e i n : initialNet n -> e @ i .: n ->
  initialEnt e. intro. generalize dependent i.
  induction H; intro i. intro. inversion H.
  intro. inversion H1. assumption. eapply IHinitialNet.
  eassumption. Qed.

(** Looks for an initial network in the hypotheses and also an entity in
that network and adds the hypothesis that the entity in question is initial.*)
Ltac initNet_ent_tac := let U0 := fresh in
  match goal with [U : initialNet ?n,
  U1 : ?e @ ?i .: ?n |- _] => lets U0 : initialNet_ent U U1 end.

(**Tactic for contradiction between initialNet and some state predicate.
Basically what it does is get the goal to the stage where there is a
hypothesis that says <...>StateProt dormant/sleeping/listening, which is
immediately solvable by inversion because none of these initial processes
match the state predicate in quesion.*)
Ltac initNet_contra U := 
  inversion U as [e U1 U2]; inversion U1;
  initNet_ent_tac; match goal with [U3 : [|_, _, _, _|] = ?e,
  U4 : initialEnt ?e |- _] => rewrite <- U3 in U4;
  inversion U4 end; match goal with [U5 : initialProc _ |- _] =>
  inversion U5 end; match goal with [U6 : procProtocol = _ |- _] =>
  symmetry in U6; subst_all U6 end; match reverse goal with
  [U7 : context[procProtocol] |- _] => inversion U7 end; subst;
  match goal with
  | [U8 : context[dormant] |- _] => inversion U8
  | [U8 : context[sleeping] |- _] => inversion U8
  | [U8 : context[listening] |- _] => inversion U8
  end.

Lemma initial_not_bcWait_net (n : Network) (m : Mode) (x : Time) (i : nat) :
  initialNet n -> bcWaitStateNet m x i n -> False.
  introz U.
  (*Solve by init_net_contra*)
  Admitted.

(** If we're nextSince & we can delay, then we're in the ovWait state.*)
Lemma nextSince_del_ovWait (n n' : Network) (i : nat) (d : Delay) :
  n -ND- d -ND> n' -> nextSinceStateNet i n ->
  exists m t x y, ovWaitStateNet m t (delToTime (x +dt+ d)) (delToTime (y +dt+ d)) i n. Admitted. (*3*)
(**Proof: Apply nextSince_rel_state and then eliminate bcReady other urgent states. Also eliminate
the ovWaitStates whos time parameter is less than d (a weak sort of urgency)- have a weak urgency
result for this- it will depend on a timed out urgency. In general, the pattern is roughly that,
we prove P(0) is urgent, then show that P(d) can delay by at most d, this in turn rests on a proof
about delay prefixes, saying that e(d)P can only delay by d', where d is less than d', when P can
delay by d' - d.*)

(*This particular state combo means that the action must be tau & the interfaces of
the entity in question being preserved.*)
Lemma switchCurr_switchListen_net_link (n n' : Network) (i : nat)
  (a : ActDiscNet) (e e' : Entity) : 
  switchCurrStateEnt e -> switchListenStateEnt e' ->
  e @ i .: n -> e' @ i .: n' -> n -NA- a -NA> n' ->
  a = anTau /\ interEnt e = interEnt e'. Admitted. (*5*)
(**Proof: Lift some EA::intercomponent & maybe some linking theorems
OR
Use some existing/new inversion tactics for destructing the state predicates and entities.*)

Lemma init_nextMode_net m i n :
  reachableNet n -> initStateNet m i n -> nextModeNet m i n.
  Admitted. (*7*)

(*LOCAL TIDY*)

Lemma ovReady_prev_net_strong m t l n n' i a : 
  ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
  ovReadyStateNet m t l i n \/
  (exists x0 y0, ovWaitStateNet m t x0 y0 i n).
  Admitted. (*#lift-track-net #strong*)

Lemma ovWait_prev_net_strong m t x y n n' i a : 
  ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
  ovWaitStateNet m t x y i n \/
  (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
  initStateNet m i n. Admitted. (*#lift-track-net #strong*)

Lemma nextMode_pres_fwd_net m i n n' a :
  reachableNet n -> nextModeNet m i n -> 
  ~(switchCurrStateNet i n \/ ovAbortStateNet i n \/
  tfsCurrStateNet i n) ->
  n -NA- a -NA> n' -> nextModeNet m i n'. Admitted. (*3*)
(**Proof: Brute force? Inter-component relationships? Is there any
machinery that you can use to help you prove this one?*)

Lemma ovWait_del_pres_bkwd_net_strong n n' d m t x y i :
  n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
  ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n. Admitted. (*#del-pres-net #strong*)

Lemma ovReady_del_pres_bkwd_net n n' d m t l i :
  n -ND- d -ND> n' -> ovReadyStateNet m t l i n' ->
  ovReadyStateNet m t l i n. Admitted. (*#del-pres-net*)

Lemma nextModeNet_del_pres n n' d m i :
  n -ND- d -ND> n' -> nextModeNet m i n -> nextModeNet m i n'.
  Admitted. (*6*)
(**Proof: Follows from the semantics. Perhaps there is a similar result
for the current mode that can be consulted for inspiration*)
  
(*-LOCAL TIDY*)

Lemma ovWait_ovReady_nextMode_net m t x y l i n :
  reachableNet n -> ovWaitStateNet m t x y i n \/ ovReadyStateNet m t l i n ->
  nextModeNet m i n.
  (*Proof: Induction on reachable using the auxialiary result init_nextMode_net.*)
  introz U. genDep5 m t x y l. induction U; intros l y x t m; introz V.
  (*
  (*Base case fails because neither ovWait nor ovReady is initial*)
  elim_intro V CON CON; initNet_contra CON.   
  Focus 2.  
  (*In the discrete inductive case, we show first that the previous state
  was either ovWait, ovReady, or init.*)
  assert ((exists t0 x0 y0, ovWaitStateNet m t0 x0 y0 i n) \/
  (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
  initStateNet m i n) as PREV.
  elim_intro V OVW OVR.
  lets OWP : ovWait_prev_net_strong OVW s. elim_intro OWP OWL OWR.
  left. do 3 eexists. eassumption. right. or_flat; ex_flat.
  left. do 2 eexists. eassumption. right. eassumption.
  lets ORP : ovReady_prev_net_strong OVR s. or_flat.
  right. left. do 2 eexists. eassumption.
  left. ex_flat. do 3 eexists. eassumption.
  (*Now we have that the previous state was either ovWait, ovReady or init,
  and so I.H. or the result init_nextMode_net will do*)
  clear V.
  (*First lets convert our goal to showing that the previous state had a next
  mode of m. We do this via a preservation tactic.*)
  cut (nextModeNet m i n). intro NM.
  (*The main thing to show here is that the previous state was not one
  that could have allowed a mode change.*)
  assert (~(switchCurrStateNet i n \/ ovAbortStateNet i n \/
  tfsCurrStateNet i n)) as NMC. unfold not. intro. or_flat; ex_flat;
  try rename H0 into H; try rename OR1 into OR; try rename OR2 into H;
  solve [state_pred_elim H OR; entnetuniq2 EN n; state_pred_elim H2 H0;
  subst; state_pred_elim H4 H6; state_pred_elim H5 H8].
  (*And from here we can show our (sub)goal.*)
  eapply nextMode_pres_fwd_net; eassumption.
  (*So now the proof burden that remains is to show the the next mode
  holds for the previous state.*)
  or_flat; ex_flat.
  (*In the ovWait and ovReady cases this follwos from the IH.*)
  lets IH : IHU l x2 x1 x0 m. apply IH. left. assumption.
  lets IH : IHU x1 y x x0 m. apply IH. right. assumption.
  (*Otherwise the auxialiary result init_nextMode_net works.*)
  eapply init_nextMode_net; eassumption.
  (*Now onto the delay case. For this we first use backward preservation of the state predicates
  to show that one holds in the previous case.*)
  assert (ovWaitStateNet m t x y i n \/ ovReadyStateNet m t l i n) as PREV.
  or_flat. left.
  (*Then we show by the inductive hypothesis that nextMode holds for 
  the previous case.*)
  (*Finally, forward preservation of the nextModeNet predicate by the
  delay relation gives us our goal.*)
  (*Going to have to fix this- apply new strong version of del_pres?*)
  eapply ovWait_del_pres_bkwd_net; eassumption.
  right. eapply ovReady_del_pres_bkwd_net; eassumption.
  eapply nextModeNet_del_pres; try eassumption.
  lets IH : IHU l y x t m. apply IH; assumption.
  Qed.*)
  Admitted. (*#bism-redo*)

Lemma ovWaitState_nextMode_net (n : Network) (m : Mode) (t x y : Time) (i : nat):
  reachableNet n -> ovWaitStateNet m t x y i n -> nextModeNet m i n.
  (*Proof: Use the more general result ovWait_ovReady_nextMode_net.*)
  introz U. eapply ovWait_ovReady_nextMode_net with (l := mkPosition 0 0).
  assumption. left. eassumption. Qed.

(*If a delay is possible, then every entity is in the listening state.*)
Theorem del_listening_net (n n' : Network) (d : Delay) (e : Entity) (i : nat) :
  reachableNet n -> n -ND- d -ND> n' -> e @ i .: n -> listeningStateNet i n.
  Admitted. (*7*)
(**Proof: Well if the network delays, then any member entity must also be able
to delay [del link theorem- salvaged?]. And then we can lift the result
(EA::del-listening-ent) to get that e is in the listening state, and we're done.*)



(********************************* Basic Results *********************************)

(*If the entity i is in position l in either network across a discrete transition,
then it is also in this position in the other network.*)
Theorem inPos_pres_disc (n n' : Network) (a : ActDiscNet) (l : Position) (i : nat) :
  n -NA- a -NA> n' ->
  (inPosNet l i n <-> inPosNet l i n').
  (*Proof: Follows directly from the entity semantics*)
  introz U. split; introz U. destruct U0.
  link_netentdiscfwd_tac e' b U. subst. econstructor; eassumption.
  inversion U2; subst; econstructor; eassumption.
  destruct U0.
  link_netentdiscbkwd_tac e b U. subst. econstructor; eassumption.
  inversion U2; subst; econstructor; eassumption.
  Qed.

(*If the curr mode of entity i is m in a derivative network,
then there is some curr mode for that entity in any source network.*)
Theorem currMode_pres_bkwd (n n' : Network) (a : ActDiscNet) (m' : Mode) (i : nat) :
  n -NA- a -NA> n' -> currModeNet m' i n' ->
  exists m, currModeNet m i n. Admitted. (*7*)
(**Proof: Well currMode m' i n' means that there is some e' @ i .: n'.
Then we can show by (...salvaged linking theorem of some sort...) that
there is some e @ i .: n. It is easy then to show that every entity has
some current mode, and so e has one, call it m, and we're done (after a bit of lifting).*)


(*If the curr mode of entity i is m in a network, then there
 is some curr mode for that entity in any derivative network.*)
Theorem currMode_pres_fwd (n n' : Network) (a : ActDiscNet) (m : Mode) (i : nat) :
  n -NA- a -NA> n' -> currModeNet m i n ->
  exists m', currModeNet m' i n'. Admitted. (*7*)
(**Proof: Analogous to the previous proof except we use some
(...salvaged linking theorem of some sort...) to show that the number of
entities are preserved forwards in a network.*)

(*If v is outgoing with timestamp t, and the network can delay, then in
the derivative network v is outgoing with timestamp t - d.
A useful corollary of this is that if t = 0, then delay is impossible.*)
Theorem outgoing_del (n n' : Network) (d : Delay) (v : list Base) (t : Time) (i : nat) : 
  n -ND- d -ND> n' -> outgoing v t i n ->
  {p : d <= t | outgoing v (minusTime t d p) i n'}. Admitted. (*5*)
(**Proof: Idea is to invert/destruct outgoing to [p, l, {li, lo, ln}, k] @ i.: n & v, t : lo
apply ent-interface del linking tactic
apply interface-list del linkiing tactic
*now we have that lo delays to some lo'*
result & accompanying tactic about timed lists v, t : l & l -d- l' then d <= t &
v (t - d) : l'
contstructor & assumption
.*)

Corollary outgoing_del_contra (n n' : Network) (d : Delay)
  (v : list Base) (i : nat) : n -ND- d -ND> n' ->  outgoing v zeroTime i n -> False. intros. 
  addHyp (outgoing_del n n' d v zeroTime i H H0). invertClear H1.
  eapply Rle_not_lt. apply x. simpl. delPos. Qed.

(*If v is outgoing with non-zero timestamp t, and the network performs a
discrete action, then v is still outgoing in the derivative network.*)	 
Theorem outgoing_disc_pres (n n' : Network) (a : ActDiscNet) (v : list Base) (t : Time) (i : nat) :
  n -NA- a -NA> n' -> outgoing v t i n -> 0 < t ->
  outgoing v t i n'. introz U.
  inversion U0.
  (*Apply net-ent disc linking tactic*)
  link_netentdiscfwd_tac e' b LE.
  (*Case entities are equal: constructor & rewrite*)
  subst. econstructor; eassumption.
  (*else destruct the derivative entity*)
  destr_ent_inter e' p' l' k' li' lo' ln'.
  (*apply a linking theorem from entities to output lists*)
  lets LEO : link_ent_outList LE1. or_flat.
  (*Equality case follows easily.*)
  subst. econstructor; eassumption.
  (*Else we need to apply some more support lemmas*)
  ex_flat. or_flat.
  econstructor. eassumption. eapply outList_in_input_pres;
  eassumption.
  econstructor. eassumption. eapply outList_in_output_pres;
  eassumption. Qed.

(*If v is incomingNetNotif with timestamp t, and the network can delay, then in
the derivative network v is incomingNetNotif with timestamp t - d.
Corollary is that whenever t = 0 delay is impossible.*)
Theorem incomingNetNotif_del (n n' : Network) (d : Delay) (v : list Base)
  (t : Time) (i : nat) : 
  reachableNet n -> n -ND- d -ND> n' -> incomingNetNotif v t i n ->
  {p : d <= t | incomingNetNotif v (minusTime t d p) i n'}.
  (*invert/destruct incomingNotif to [p, l, {li, lo, ln}, k] @ i.: n & v, t : ln*)
  intro RN. introz U. destruct U0.
  (*Set up the derivaive entity.*)
  link_netentdelfwd_tac e' Y. destr_ent_inter e' p' l' k' li' lo' ln'.
  (*Apply ent-interface del linking tactic*)
  link_entinterdel_tac Y.
  (*Invert the delay to the lists.*)
  inversion_clear Y1.
  (*From here we split proof into two based on where d <= t or not*)
  Rleltcases d t IQ.
  (*In the case of d <= t we use a support lemma for the t - d stamp of the message*)
  exists IQ. econstructor. apply Y.
  eapply notifList_del_le. apply H3. assumption.
  (*In the case of t < d, proceed by contradiction on noSynchProcInter. We know that since
  a delay is possible for the entity, noSynch must be true between the entity components.*)
  false. assert (noSync p {| li := li; lo := lo; ln := ln |} k d) as NSY. inversion Y0.
  assumption. assert (p -PD- d -PD> p') as PDD. inversion Y0. assumption.
  (*So it suffices to falsify this to get the contradiction i.e. show a synch between proc
  and inter either now or after some delay less than d.*)
  lets NS : NSY (chanAN ;? v). decompAnd2 NS NSN NSD.
  (*Now we split into two subcases based on whether 0 < t or t = 0*)
  remember ([|p, l, {| li := li; lo := lo; ln := ln |}, k|]) as e0.
  timezerolteq t Q.
  (*If 0 < t then there is some delay d' = t*)
  clear NSN. mkdel t Q d'. assert (d' < d) as DD. rewrite Heqd'. assumption.
  (*Let's turn the inequality into an equation*)
  Rlttoplus DD x DP. mkdel x DP0 d''. assert (d = d' +d+ d'') as ED.
  rewrite Rplus_comm in DP. apply delayEqR. simpl. my_applys_eq DP.
  f_equal. rewrite Heqd''. reflexivity.
  (*Then by the property of time splitting, we get that there was an intermediate entity
  network from the original with delay d'. Call this n1.*)
  lets TNX : timeSplit_net U ED. decompExAnd TNX n1 ND1 ND2.
  (*Now, we know there must be some entity e1 in n1 which is delay linked to e0.*)
  link_netentdelfwd_tac e1 ED. 
  (*Now we do some inversion on this transiton to get the corresponding delay of the
  notification list.*)
  rewrite Heqe0 in ED1. destr_ent_inter e1 p1 l1 k1 li1 lo1 ln1.
  link_entinterdel_tac U. inversion U0. assert (d' <= t) as DT. rewrite Heqd'.
  simpl. apply Rle_refl.
  (*Once we have this delay, we can show that the notifList relation continues on,
  and since d' = t, the timestamp is now 0.*)
  lets ND : notifList_del_le DT H13 H0. assert (minusTime t d' DT = zeroTime) as TDZ.
  apply timeEqR. simpl. rewrite Heqd'. simpl. ring. rewrite TDZ in ND. clear TDZ.  
  (*Now we bring to our hypotheses the noSync condition for the intermediate state.*)
  assert (p -PD- d' -PD> p1 /\ k -ms- d' -ms> k1 /\
  {| li := li; lo := lo; ln := ln |} -i- d' -i> {| li := li1; lo := lo1; ln := ln1 |}).
  inversion ED1; (repeat split); assumption. andflat HY.
  lets NSF : NSD DD HY HY2 HY1.
  (*Then ahead we go to show the synchronisation on chanAN of v does exist.*)
  unfold noSyncNow in NSF. assert (discActEnabled p1 (chanAN;? v)) as DAE.
  apply listening_AN_prot. assert (listeningStateNet i n1) as LSN. eapply del_listening_net.
  eapply reachNetDel. apply RN. apply ND1. apply ND2. apply ED0. inversion LSN as [e IV1 IV2].
  inversion IV1 as [p4 l4 h4 k4 IV3 IV4]. my_applys_eq IV3. rewrite <- IV4 in IV2.
  entnetuniq2 EU n1. inversion EU. reflexivity. apply NSF in DAE. decompAnd2 DAE DI DM.
  apply DI. apply notif_timeout_enabled. assumption.
  (*If t = 0, then we have our contradiction with noSyncNow, just like the last step
  of the previous case.*)
  clear NSD. unfold noSyncNow in NSN. assert (discActEnabled p (chanAN;? v)) as DAE.
  apply listening_AN_prot. assert (listeningStateNet i n) as LSN. eapply del_listening_net.
  apply RN. apply U. apply H. inversion LSN. inversion H4. my_applys_eq H6.
  cut (e = e0). intros. rewrite H8 in H7. rewrite Heqe0 in H7. inversion H7.
  reflexivity. entnetuniq U e e0. assumption. apply NSN in DAE. decompAnd2 DAE DI DM.
  apply DI. assert (t = zeroTime) as TZ. apply timeEqR. rewrite <- Q.
  reflexivity. rewrite TZ in H0. apply notif_timeout_enabled. assumption. Qed.

(*If v is incomingNetNotif with non-zero timestamp t, and the network performs a discrete
action, then v is still incomingNetNotif in the derivative network.*)
Theorem incomingNetNotif_disc_pres (n n' : Network) (a : ActDiscNet) (v : list Base) (t : Time) (i : nat) :
  n -NA- a -NA> n' -> incomingNetNotif v t i n -> 0 < t ->
  incomingNetNotif v t i n'. Admitted. (*4*)
(**Proof: Analogous to (outgoing_disc_pres).*)

(*If an entity is inPosNet l' i n', and there is some n such that it delays to n' via d,
then i is in inPosNet l i n for some l and the difference between the positions is at most
speedMax*d*)
Lemma inPos_del_bound_bkwd (n n' : Network) (d : Delay) (l' : Position) (i : nat) :
  inPosNet l' i n' -> n -ND- d -ND> n' -> exists l,
  inPosNet l i n /\ dist2d l l' <= speedMax * d. Admitted. (*5*)
(**Proof: Salvaged from old Coq model (pos_bound?).*)

Conjecture currMode_intro : forall (m : Mode) (e : Entity) (i : nat) (n : Network),
  m = currModeEnt e -> e @ i .: n -> currModeNet m i n.
(**Proof: Obvious- lift currModeEnt to currModeNet*)

Conjecture inPos_ex : forall (i : nat) (n : Network) (e : Entity),
  e @ i .: n -> exists l, inPosNet l i n.
(**Proof: Obvious- every entity has a position*)

Conjecture distNet_intro : forall (e1 e2 : Entity) (i j : nat) (n : Network) (x : Distance),
  e1 @ i .: n -> e2 @ j .: n -> x = mkDistance (dist2d e1 e2) -> distNet i j n x.
(**Proof: Obvious from definitions of things*)

Conjecture inPos_pos : forall (e : Entity) (i : nat) (l : Position) (n : Network),
  e @ i .: n -> inPosNet l i n -> posEnt e = l.
(**Proof: Obvious- invert/deconstruct inPostNet*)

Conjecture reachable_net_ent : forall (n : Network) (e : Entity) (i : nat),
  reachableNet n -> e @ i .: n -> reachableEnt e.
(**Proof: Obvious- inversion on reachableNet*)

(*There are already proofs like this about distance in networks, just not using distNet*)
Conjecture disc_pres_distNet_bkwd : forall (n n' : Network) (a : ActDiscNet)
  (i j : nat) (x : Distance),
  n -NA- a -NA> n' -> distNet i j n' x -> distNet i j n x.
(**Proof: Obvious- Lift other proofs which say essentially the same thing and apply constructor for distNet*)

(*There are already proofs like this about distance in networks, just not using distNet*)
Conjecture del_link_distNet_bkwd : forall (n n' : Network) (d : Delay)
  (i j : nat) (x' : Distance),
  n -ND- d -ND> n' -> distNet i j n' x' ->
  exists x, distNet i j n x /\ x <= x' + 2*speedMax*d.
(**Proof: Obvious- Lift similar proofs & apply distNet constructor*)

Conjecture distNet_elim : forall (i j : nat) (n : Network) (x : Distance),
  distNet i j n x -> exists e1 e2,
  e1 @ i .: n /\ e2 @ j .: n /\ x = {| distance := dist2d e1 e2 |}. 

(*Delay link from network to entity.*)
Lemma del_net_ent (e : Entity) (i : nat) (n n' : Network) (d : Delay) :
  e @ i .: n -> n -ND- d -ND> n' -> exists e', e -ED- d ->> e'.
  intros. genDep2 i n'. induction n; intros n' H0 i H.
  inversion H. inversion H0. inversion H.
  eexists. eassumption. eapply IHn. eassumption.
  eassumption. Qed.

(*If a network accepts some value*)
Lemma inRange_acc_input (n n' : Network) (v : list Base) (l : Position)
  (r : Distance) (i : nat) (e : Entity) :
  n -NA- ([-v, l, r-]) /?: -NA> n' -> e @ i .: n -> dist2d l (posEnt e) <= r ->
  exists e', e -EA- ([-v, l, r-]) #? ->> e' /\ e' @ i .: n'. Admitted. (*7*)

(*Any entity within range of a broadcast inputs that broadcast.*)
Lemma inRange_out_input (n n' : Network) (v : list Base) (l : Position)
  (r x: Distance) (i j : nat) (e : Entity) :
  n -NA- ([-v, l, r-]) /! i -NA> n' -> e @ j .: n -> i <> j -> distNet i j n' x ->
  x <= r -> exists e', e -EA- ([-v, l, r-]) #? ->> e' /\ e' @ j .: n'.
  genDep3 n' i j. induction n; intros. inversion H0.
  inversion H. (*Use inRange_acc_input from here*) Admitted. (*7*)

Conjecture transGuard_disc_pres : forall (n n' : Network)
  (a : ActDiscNet) (t : Time) (i : nat),
  n -NA- a -NA> n' -> transGuard t i n -> transGuard t i n'.
(**Proof: Obvious: discrete action preserves guard on mode state, immediate from mode state semantics*)

Conjecture transGuard_elim : forall (t : Time) (i : nat) (n : Network),
  transGuard t i n -> exists m m',
  mState_in_net (<| m, m', t |>) i n.
(**Proof: Obvious: transGuard definition*)

Conjecture transGuard_intro : forall (t : Time) (i : nat) (n : Network)
  (m m' : Mode), mState_in_net (<| m, m', t |>) i n ->
  transGuard t i n.
(**Proof: Immediate from definition of transGuard*)

Conjecture mState_disc_pres : forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k  : ModeState), n -NA- a -NA> n' -> mState_in_net k i n ->
  exists k', mState_in_net k' i n'.
(**Proof: Obvious- inversion on mState_in_net, get that there's an entity, apply linking tactic to get entity in derivative,
then once there's an entity there's going to be a mode state, so mState_in_net is satisfied.*)

Conjecture transGuard_del : forall (n n' : Network)
  (d : Delay) (t : Time) (i : nat),
  n -ND- d -ND> n' -> transGuard t i n -> 
  exists p, transGuard (minusTime t d p) i n'.
(**Proof: Obvious- transGuard definition and mode state semantics*)

Conjecture currModeNet_del_pres : forall (n n' : Network) (d : Delay)
  (m : Mode) (i : nat), n -ND- d -ND> n' ->
  (currModeNet m i n <-> currModeNet m i n').
(**Proof: Obvious- delay preservation tactic*)

Conjecture currModeNet_dec : forall (m : Mode) (i : nat) (n : Network),
  currModeNet m i n \/ ~currModeNet m i n.
(**Proof: Obvious- not important to prove as it's just law of excluded middle*)

Lemma initial_failSafe (n : Network) (e : Entity) (i : nat) :
  initialNet n -> e @ i .: n -> failSafe e.
  (*Proof: Follows directly from the definition of initial*)
  introz U. generalize dependent i. induction n; intros i U0.
  inversion U0. inversion U. subst. inversion U0. subst.
  inversion H1. assumption. eapply IHn; eassumption. Qed.

Lemma curr_switch_ent_tau (n n' : Network) (a : ActDiscNet)
  (e e' : Entity) (i : nat) (m m' : Mode) :
  n -NA- a -NA> n' -> e @ i .: n -> e' @ i .: n' ->
  currModeEnt e = m -> currModeEnt e' = m' -> m <> m' ->
  e -EA- aeTau ->> e'. Admitted. (*5*)
(**Proof: EXISITNG THEOREMS OF A SIMILAR NATURE TO HELP YOU SOLVE THIS? LOOK FOR M <> M'
Case analyse the action a and in all cases where the action isn't tau, the mode states are equal, giving a contradiction. This leaves only the case where a is a tau. In this case, we apply a linking theorem to get that the tau was done by some entity while the rest of the entities were preserved. Well, then, the entity that did the tau must be our entity e, because otherwise its preservation would imply the equality of the modes, which is a contradiction.*)

(**Broadly speaking, a linking theorem.*)
Lemma reachable_net_prot : forall (n : Network) (i : nat)
  (p : ProcTerm) (l : Position) (h : Interface) (k : ModeState),
  reachableNet n -> [|p, l, h, k|] @ i .: n ->
  reachableProt p. Admitted. (*6*)
(**Proof: DOES THEOREM LIKE THIS ALREADY EXIST? Induction on reachableNet and some linking results*)

(**Delay preserves the current mode*)
Lemma currMode_del_pres_bkwd (n n' : Network) (d : Delay) (m : Mode) (i : nat) :
  n -ND- d -ND> n' -> currModeNet m i n' -> currModeNet m i n. Admitted. (*6*)
(**Proof: Follows directly from mode state semantics, and linking of delay from network to entity to modestate*)

Conjecture inPos_ent_net : forall (l : Position) (e : Entity) (i : nat) (n : Network),
  inPosEnt l e -> e @ i .: n -> inPosNet l i n.
(**Proof: Obvious from definitions*)

Conjecture inPos_unique : forall (l l' : Position) (i : nat) (n : Network),
  inPosNet l i n -> inPosNet l' i n -> l = l'.
(**Proof: Obvious- inversion and apply entInNetUnique*)

(*An output by entity i from the network n means that the message is now pending
notification with timestamp AN.*)
Lemma outNet_incomingNetNotif (n n' : Network) (v : list Base) (r : Distance)
  (l : Position) (i : nat) : n -NA- ([-v, l, r-]) /! i -NA> n' ->
  incomingNetNotif ((baseDistance r)::v) adaptNotif i n'. Admitted. (*5*)
(**Proof: Follows from interface semantics.*)

(** Linking theorem.*)
Lemma incoming_net_ent (v : list Base) (i : nat) (n : Network) :
  incomingNet v i n -> exists e, incomingEnt v e /\ e @ i .: n. intro U.
  invertClear U. exists ([|p, l, {| li := li; lo := lo; ln := ln |}, k|]).
  split. repeat constructor. assumption. assumption. Qed.

(** Linking theorem.*)
Lemma incoming_ent_net (v : list Base) (e : Entity) (i : nat) (n : Network) :
  incomingEnt v e -> e @ i .: n -> incomingNet v i n.
  (*Proof: Follows directly from the definition*)
  introz U. inversion U. subst. destruct h. econstructor. eassumption.
  inversion U. subst. inversion H1. assumption. Qed.

Ltac inposdp :=
  match goal with
  [ w : ?n -NA- _ -NA> ?n', H : inPosNet ?l ?i ?n' |- inPosNet ?l ?i ?n] =>
  eapply inPos_pres_disc; [apply w | assumption]
  end.

(**Can be used directly for this particular protocol with 3 software components. Constructs the derivative triple and all the
delays between the corresponding components, as well as the position bound. Specification is somewhat crude, but easy to manipulate,
particularly with a tactic.*)
Lemma net_del_elim q q0 q1 l h k i n n' d :
  [|q $||$ q0 $||$ q1, l, h, k|] @ i .: n ->
  n -ND- d -ND> n' ->
  exists q' q0' q1' l' h' k',
  [|q' $||$ q0' $||$ q1', l', h', k'|] @ i .: n' /\
  q -PD- d -PD> q' /\ q0 -PD- d -PD> q0' /\ q1 -PD- d -PD> q1' /\
  h -i- d -i> h' /\ k -ms- d -ms> k' /\
  dist2d l l' <= speedMax * d. Admitted. (*7*)
(**Proof: First apply linking theorem for the entity. Then destruct the derivative entity. Then show that the delay between the entities
can only happen when the interface and mode state components also delay, and the distance inequality condition holds, giving the final three goals.
The first four goals then follow from an application of a result for software components: triples of processes always delay to triples, with each
individual component delaying to the corresponding component*)

Conjecture currMode_ent_ex : forall (m : Mode) (i : nat) (n : Network),
  currModeNet m i n <-> exists e, e @ i .: n /\ currModeEnt e = m.
(**Proof: Obvious from definitions*)

Conjecture nextMode_ent_ex : forall (m : Mode) (i : nat) (n : Network),
  nextModeNet m i n <-> exists e, e @ i .: n /\ nextModeEnt m e.
(**Proof: Obvious from definitions*)

Ltac currMode_ent_ex_tac e U :=
  let Q := fresh in let U1 := fresh U in let U2 := fresh U in
  match goal with
  [H : currModeNet ?m ?i ?n |- _ ] => lets Q : H; rewrite currMode_ent_ex in Q;
  decompExAnd Q e U1 U2
  end.

Ltac nextMode_ent_ex_tac e U :=
  let Q := fresh in let U1 := fresh U in let U2 := fresh U in
  match goal with
  [H : nextModeNet ?m ?i ?n |- _ ] => lets Q : H; rewrite nextMode_ent_ex in Q;
  decompExAnd Q e U1 U2
  end.

(*LOCAL TIDY*)

Lemma mState_in_net_unique k k' i n : 
  mState_in_net k i n -> mState_in_net k' i n -> k = k'.
  intros. inversion H. inversion H0. entnetuniq2 EN n.
  inversion EN. reflexivity. Qed.

(** Given a network state predicate as the goal and the corresponding
entity state predicate in the hypotheses, this solves things using
lenWitness.*)
Ltac netState_ent_net_tac := eapply lenWitness;
  [eassumption | eassumption].

Lemma tfsNext_currModeNet_eq m1 m2 i n : currModeNet m1 i n ->
  tfsNextStateNet m2 i n -> m1 = m2. Admitted. (*5*)
(*Proof: On initially entering this state, the mode is read from the mode state,
giving the equality. In the discrete inductive case it can be shown by
currModeNet_switch_states that the mode state doesn't change- (?) because if it were to change
that would imply a contradictory condition on the state predicates?. In the delay inductive
case, delay preservation for both mode state and tfsNext prevail.*)

(** The nextSinceState relation can be broken down into the following cases.*)
Lemma nexSinceStateNet_cases i n :
  nextSinceStateNet i n ->
  (exists m t x y, ovWaitStateNet m t x y i n) \/
  (exists m t l, ovReadyStateNet m t l i n) \/
  (exists m, switchBcStateNet m i n) \/
  (switchCurrStateNet i n). intros. inversion H.
  inversion H0. inversion H2. subst. inversion H4.
  left. (*repeat eexists; eassumption. 
  right. left. repeat eexists; eassumption.
  right. right. left. repeat eexists; eassumption.
  right. right. right. repeat eexists; eassumption.
  Qed.*)
  Admitted. (*R*)

Lemma link_net_ent_disc :
  forall (n n' : Network) (e e' : Entity) (i : nat) (a : ActDiscNet),
  n -NA- a -NA> n' -> e @ i .: n -> e' @ i .: n'->
  (e = e' \/ (exists a', e -EA- a' ->> e')). Admitted. (*6*)
(**Proof: Case analyse the network transition and this follows from the semantics*)

Ltac link_netentdisc_tac b :=
  match goal with
  | [ U1 : ?n -NA- ?a -NA> ?n', U2 : ?e @ ?i .: ?n,
  U3 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc U1 U2 U3;
    let H2 := fresh in let H3 := fresh in
    elim_intro H1 H2 H3; [subst_all H2 |
    let H4 := fresh in invertClearAs2 H3 b H4]
  end.

(** Does some pre-processing on the proof of a backracking theorem at the
network level. Works where the backtracking has two predecessor cases.
Probably needs to be slightly altered if there's a need to handle more cases. *)
Ltac backtrack_net_pre U :=
  let U1 := fresh in let e := fresh "e" in let b := fresh "b" in
  state_pred_net_destr U; link_netentdiscbkwd_tac0 e b U1;
  let EQ := fresh "EQ" in let EX := fresh in
  match goal with [U2 : _ \/ _ |- _ ] =>
  elim_intro U2 EQ EX; [left; econstructor | ];
  [eassumption |  | ]; [ subst; assumption | ex_flat] end.

(** Tactic for eliminating two contradictory state predicates H and H1*)
Ltac state_pred_elim_net H H1 :=
  let e := fresh "e" in let e' := fresh "e'" in
  let U1 := fresh in let U2 := fresh in let U3 := fresh in
  let U1' := fresh in let U2' := fresh in
  inversion H as [e U1 U2]; inversion H1 as [e' U1' U2'];
  assert (e' = e) as U3;[eapply entInNetUnique; eassumption | ];
  subst_all U3; destruct e as [p0 l0 h0 k0]; inversion U1;
  inversion U1'; subst; 
  match goal with [SP1 : context[p0], SP2 : context[p0] |- _] =>
  inversion SP1; inversion SP2 end; subst;
  match goal with [PT : _ $||$ _ $||$ _ = ?p1 $||$ ?p2 $||$ ?p3 |- _] =>
  inversion PT; subst;
  repeat match goal with [PT : context[_ $||$ _ $||$ _] |- _] =>
  clear PT end;
  match goal with
  | [SP1 : context[p1], SP2 : context[p1] |- _] =>
    inversion SP1; subst; inversion SP2
  | [SP1 : context[p2], SP2 : context[p2] |- _] =>
    inversion SP1; subst; inversion SP2
  | [SP1 : context[p3], SP2 : context[p3] |- _] =>
    inversion SP1; subst; inversion SP2
  end
  end.

(***************************** Lifted results *****************************)

Lemma tfsStart_prev_net i n n' a : tfsStartStateNet i n' ->
  n -NA- a -NA> n' -> tfsStartStateNet i n \/
  exists m t x y, ovWaitStateNet m t x y i n.
  Admitted. (*#lift-track-net*)

Lemma ovReady_prev_net m t l i n n' a :
  ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
  ovReadyStateNet m t l i n \/
  exists x y, ovWaitStateNet m t x y i n. Admitted. (*#lift-track-net*)

(*Organise these, write tactics for them, pull in results from elsewhere in
the file that belong here.*)

Lemma ovWait_del_pres_net m t x y i n n' d : n -ND- d -ND> n' ->
  (ovWaitStateNet m t x y i n <-> ovWaitStateNet m t x y i n'). Admitted. (*4*)
(*Standard delay preservation tactic at network level, which itself
lifts from lower levels.*)

Lemma tfsNext_prev_net m i n n' a : tfsNextStateNet m i n' ->
  n -NA- a -NA> n' -> tfsNextStateNet m i n \/ tfsStartStateNet i n.
  intros.
  backtrack_net_pre H.
  lets TPE : tfsNext_prev_ent H1 H5.
  elim_intro TPE TN TS;[left | right]; netState_ent_net_tac.
  Qed.  

Lemma del_pres_bkwd_tfsNext m i n n' d :
  n -ND- d -ND> n' -> tfsNextStateNet m i n' -> tfsNextStateNet m i n.
  Admitted. (*4*)
(*Proof: Lift delay preservation- write tactic for this*)  

Lemma del_pres_bkwd_tfsStart i n n' d :
  n -ND- d -ND> n' -> tfsStartStateNet i n' -> tfsStartStateNet i n.
  Admitted. (*4*)

Lemma tfsNext_urgent_net m i n n' d : 
  tfsNextStateNet m i n -> n -ND- d -ND> n' -> False.
(*Lift urgency- use tactic*) Admitted. (*5*)

Lemma tfsStart_urgent_net i n n' d : 
  tfsStartStateNet i n -> n -ND- d -ND> n' -> False.
(*Lift urgency- use tactic*) Admitted. (*5*)

Lemma ovReady_wait_track_net m t l i m' t' x y n n' a :
  ovReadyStateNet m t l i n -> ovWaitStateNet m' t' x y i n' ->
  n -NA- a -NA> n' -> m = m' /\
  (exists p, t' = minusTime t (period m) p) /\ x = t' /\ y = period m.
  Admitted. (*5*)
(*Proof: #lift-track-net*)

Lemma ovWait_track_net m m' t t' x x' y y' i n n' a :
  ovWaitStateNet m t x y i n -> ovWaitStateNet m' t' x' y' i n' ->
  n -NA- a -NA> n' -> m = m' /\ t = t' /\ x = x' /\ y = y'. Admitted. (*5*)
(**Proof: Apply a tactic to extract the underlying process state predicates- at the
lowest level e.g. ovWaitState p2 (tactic already exists I think?).
Then apply a matching tactic at this level, and you should be done.*)

(*Perhaps modify this to get rid of the "t + period m" and replace it with some existential
instead. Then do a separate tracking result to get the "t + period m".*)
Lemma ovWait_prev_net m t x y i n n' a : ovWaitStateNet m t x y i n' ->
  n -NA- a -NA> n' ->
  ovWaitStateNet m t x y i n \/
  (exists l, ovReadyStateNet m (t +t+ period m) l i n) \/
  initStateNet m i n.
  Admitted. (*#lift-track-net*)

Ltac reach_net_prot_tac :=
  match goal with [RN : reachableNet ?n,
  EIN : [|_, _, _, _|] @ _ .: ?n |- _] =>
  let RNP := fresh "RNP" in
  let RPT := fresh "RPT" in
  lets RNP : reachable_net_prot RN EIN;
  lets RPT : reachableProt_triple RNP end.

(*-LOCAL TIDY*)
