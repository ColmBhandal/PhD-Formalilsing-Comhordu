(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require Import ComhCoq.lang.InterfaceLanguage.
Require Import ComhCoq.lang.ModeStateLanguage.
Require Import ComhCoq.lang.EntityLanguage.
Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.lang.ProcEquiv.
Require Import ComhCoq.protocol.ProtAuxDefs.
Require Import ComhCoq.protocol.ProtAuxResults.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.EntAuxResults.
Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.protocol.ProtocolBridge.

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

(** An entity in an initial network is itself initial.*)
Lemma initialNet_ent e i n : initialNet n -> e @ i .: n ->
  initialEnt e. intro. generalize dependent i.
  induction H; intro i. intro. inversion H.
  intro. inversion H1. assumption. eapply IHinitialNet.
  eassumption. Qed.

Lemma link_net_prot_reach n p l h k i :
  reachableNet n ->  [|p, l, h, k|] @ i .: n -> reachableProt p.
Proof.
  intros RN. revert p l h k i.
  induction RN as [n IN | n n' a RN IH ST | n n' d RN IH ST];
    intros p l h k i E.
  - (* initial network *)
    assert (initialEnt ([|p, l, h, k|])) as IE
      by (eapply initialNet_ent; eassumption).
    inversion IE; subst.
    match goal with [V : initialProc _ |- _] => inversion V end.
    apply reachprBase.
  - (* discrete step *)
    destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST E) as [e [E0 [Eq | [a' S]]]].
    + subst e. eapply IH; eassumption.
    + destruct e as [p0 l0 h0 k0].
      inversion S; subst;
      first [ solve [eapply IH; eassumption]
            | solve [eapply reachprDisc; [eapply IH; eassumption | eassumption]] ].
  - (* delay step *)
    destruct (link_net_ent_del_bkwd _ _ _ _ _ ST E) as [e [E0 S]].
    destruct e as [p0 l0 h0 k0].
    inversion S; subst.
    eapply reachprDel; [eapply IH; eassumption | eassumption].
Qed.
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
Inductive outgoing (v : list BaseType) (t : Time) (i : nat) (n : Network) : Prop :=
  | ogWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , t )>) (outList lo) -> outgoing v t i n.

(*incomingNet v i n says that the message v is in the input queue of the interface component of the entity i in the network n.
Note: Even though the input queue is effectively untimed messages, it is modelled as a timed list, with 
timestamps simply set to 0, hence "v in Li" becomes "<v, 0> in Li" to be more pedantic about it.*)
Inductive incomingNet (v : list BaseType) (i : nat) (n : Network) : Prop :=
  | icWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , zeroTime )>) (inList li) -> incomingNet v i n.


(*incomingNetNotif v t i n says that the message v with timestamp t is in the
notification queue of the interface component of the entity i in the network n.*)
Inductive incomingNetNotif (v : list BaseType) (t : Time) (i : nat) (n : Network) : Prop :=
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

(* begin helpers for tfsStateNet_dec *)
From Stdlib Require Import Classical_Prop.
(* end helpers *)

Lemma tfsStateNet_dec : forall (i : nat) (n : Network), decidable (tfsStateNet i n).
Proof.
  intros i n. unfold decidable. apply Classical_Prop.classic.
Qed.
(**Proof: Obvious*)

Lemma tfsCurrNet_dec : forall (i : nat) (n : Network),
  decidable (tfsCurrStateNet i n).
Proof.
  intros i n. unfold decidable. apply Classical_Prop.classic.
Qed.
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

(** The action linking a change from switchCurr to switchListen is always a tau.*)
Lemma switchCurr_listen_trans_tau (n n' : Network) (a : ActDiscNet) (i : nat) :
  n -NA- a -NA> n' -> switchCurrStateNet i n -> switchListenStateNet i n' ->
  a = anTau.
Proof.
  intros S U V.
  destruct U as [e U1 U2]. destruct V as [e' V1 V2].
  destruct U1 as [p l h k P]. destruct V1 as [p' l' h' k' P'].
  eapply procNeq_tau_net; [exact U2 | exact V2 | exact S | ].
  intro EQ; subst p'.
  destruct P as [p1 p2 p3 Q].
  inversion P' as [p1' p2' p3' Q' EQ]; subst.
  lets D : switchCurr_mCurr_out Q.
  lets D' : bisim_dae Q' D.
  destruct D' as [q T]. unfold switchListen in T. inversion T.
Qed.

(*LOCAL TIDY*)

(* begin helpers for tfsStart_tfs_net *)
(** Lifts an overlap-component inclusion into tfsState (given by the
tfsState constructor C) through the entity and network lifting layers.*)
Ltac tfsStart_tfs_net_tac C :=
  let H := fresh "H" in let e := fresh "e" in
  let He := fresh "He" in let Hin := fresh "Hin" in
  intro H; destruct H as [e He Hin]; apply lenWitness with (e := e); [ | exact Hin];
  let p := fresh "p" in let l := fresh "l" in let h := fresh "h" in
  let k := fresh "k" in let Hp := fresh "Hp" in
  destruct He as [p l h k Hp]; constructor;
  let p1 := fresh "p1" in let p2 := fresh "p2" in let p3 := fresh "p3" in
  let Hq := fresh "Hq" in
  destruct Hp as [p1 p2 p3 Hq]; constructor; eapply C; exact Hq.
(* end helpers *)

Lemma tfsStart_tfs_net i n :
  tfsStartStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsStaSt.
Qed.

Lemma tfsNext_tfs_net m i n :
  tfsNextStateNet m i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsNexSt.
Qed.

Lemma tfsCurr_tfs_net i n :
  tfsCurrStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsCurSt.
Qed.

Lemma tfsBc_tfs_net i n :
  tfsBcStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsBcSt.
Qed.

Lemma tfsListen_tfs_net i n :
  tfsListenStateNet i n -> tfsStateNet i n.
Proof.
  tfsStart_tfs_net_tac tfsLisSt.
Qed.

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
Proof.
  intros TR B. destruct B as [e Be Ein].
  destruct (link_net_ent_disc_fwd n n' e i a TR Ein) as [e' [E'in [Eq | [a' Ste]]]].
  - subst. left. econstructor; eassumption.
  - destruct Be as [p l h k Bp]. destruct e' as [p' l' h' k'].
    destruct (link_ent_soft_disc p p' l l' h h' k k' a' Ste) as [Peq | [b Stp]].
    + subst. left. econstructor; [ | exact E'in]. constructor. exact Bp.
    + destruct Bp as [p1 p2 p3 B3].
      link_partripdiscex_tac Peq p1' p2' p3'.
      subst p'.
      link_partripdiscW3_tac Stp W. destruct W as [E3 | [a3 St3]].
      * subst. left. econstructor; [ | exact E'in]. constructor. constructor. exact B3.
      * right. econstructor; [ | exact E'in]. constructor. constructor.
        eapply badOvlp_next; eassumption.
Qed.
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

(* begin helpers for initial_not_bcWait_net *)
(** The sleeping process can never input on the position channel, so it is
not bisimilar to any process that can.*)
Local Lemma initial_not_bcWait_net_aux1 q q' v :
  ComhCoq.lang.ProcEquiv.bisimulation sleeping q -> q -PA- chanPos ;? v -PA> q' -> False.
Proof.
  intros S T. destruct (bisim_step_disc _ _ _ _ (bisim_symm _ _ S) T) as [p' [Sp _]].
  unfold sleeping in Sp. invert_disc_prefixes.
Qed.

(** The sleeping process delays only to itself.*)
Local Lemma initial_not_bcWait_net_aux2 d s :
  sleeping -PD- d -PD> s -> s = sleeping.
Proof.
  revert d s. unfold sleeping. del_self_tac.
Qed.

(** The sleeping process is not bisimilar to any bcWait process: the latter
can (possibly after a delay) input on the position channel.*)
Local Lemma initial_not_bcWait_net_aux m x : bcWaitState m x sleeping -> False.
Proof.
  unfold bcWaitState. intro S.
  destruct x as [[x xnn]].
  destruct (Rle_lt_or_eq_dec 0 x xnn) as [Hlt | Heq].
  - set (d := mkDelay (mkposreal x Hlt)).
    assert (exists q', bcWait m (mkTime (mknonnegreal x xnn)) -PD- d -PD> q' /\
      exists q'', q' -PA- chanPos ;? [baseTime zeroTime] -PA> q'') as [q' [TD [q'' TP]]].
    { eexists. split.
      - unfold bcWait. apply stepTpSum; [apply stepTpSum | apply stepTpIn]; [apply stepTpIn | ].
        eapply (stepTpDelSub _ d _ (mkTime (mknonnegreal x xnn)) (Rle_refl x)).
        reflexivity.
      - eexists. apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpTimeOut.
        apply stepDpIn. reflexivity.
        unfold evalExpFunTime. simpl. f_equal. apply timeEqR. simpl. ring. }
    destruct S as [_ S2]. apply stepPTimed in TD. apply S2 in TD.
    destruct TD as [s [Ss Bs]]. inversion Ss; subst.
    match goal with H : sleeping -PD- _ -PD> _ |- _ =>
      apply initial_not_bcWait_net_aux2 in H; subst end.
    eapply initial_not_bcWait_net_aux1; eassumption.
  - subst x.
    assert (exists q'', bcWait m (mkTime (mknonnegreal 0 xnn)) -PA-
      chanPos ;? [baseTime zeroTime] -PA> q'') as [q'' TP].
    { eexists. unfold bcWait. apply stepDpChoiceL. apply stepDpChoiceR.
      apply stepDpTimeOut. apply stepDpIn. reflexivity.
      unfold evalExpFunTime. simpl. f_equal. apply timeEqR. simpl. reflexivity. }
    eapply initial_not_bcWait_net_aux1; eassumption.
Qed.
(* end helpers *)

Lemma initial_not_bcWait_net (n : Network) (m : Mode) (x : Time) (i : nat) :
  initialNet n -> bcWaitStateNet m x i n -> False.
Proof.
  intros I B. destruct B as [e Be Ein].
  lets IE : initialNet_ent I Ein.
  destruct Be as [p l h k Bp]. inversion IE as [p0 l0 h0 k0 IP FS]; subst.
  inversion IP; subst. unfold procProtocol in Bp. inversion Bp; subst.
  eapply initial_not_bcWait_net_aux; eassumption.
Qed.

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
(* begin helpers for switchCurr_switchListen_net_link *)
(** No process is bisimilar to both switchCurr and switchListen.*)
Lemma switchCurr_switchListen_net_link_aux2 (p : ProcTerm) :
  switchCurrState p -> switchListenState p -> False.
Proof.
  intros S1 S2. lets D : switchCurr_mCurr_out S1.
  lets D2 : bisim_dae S2 D. inversion D2 as [q T].
  unfold switchListen in T. inversion T.
Qed.

(** If a triple whose overlap component is switchCurr performs a visible action that
switchCurr cannot perform, and the derivative's overlap component is switchListen,
then we have a contradiction.*)
Lemma switchCurr_switchListen_net_link_aux3 (p1 p2 p3 q1 q2 q3 : ProcTerm) (a : DiscAct) :
  switchCurrState p2 -> switchListenState q2 ->
  p1 $||$ p2 $||$ p3 -PA- a -PA> q1 $||$ q2 $||$ q3 -> a <> tauAct ->
  (forall q, switchCurr -PA- a -PA> q -> False) -> False.
Proof.
  intros S1 S2 T NT NSC. inversion T; subst; try (apply NT; reflexivity).
  - eapply switchCurr_switchListen_net_link_aux2; eassumption.
  - match goal with [H : p2 $||$ p3 -PA- a -PA> q2 $||$ q3 |- _] =>
      inversion H; subst; try (apply NT; reflexivity) end.
    + match goal with [H : p2 -PA- a -PA> q2 |- _] =>
        lets BM : bisim_disc_match S1 H end.
      destruct BM as [q BM]. eapply NSC. eassumption.
    + eapply switchCurr_switchListen_net_link_aux2; eassumption.
Qed.

(** A silent entity step from a switchCurr entity to a switchListen entity preserves
the interface.*)
Lemma switchCurr_switchListen_net_link_aux4 (p1 p2 p3 q1 q2 q3 : ProcTerm)
  (l l' : Position) (h h' : Interface) (k k' : ModeState) :
  switchCurrState p2 -> switchListenState q2 ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- aeTau ->> [|q1 $||$ q2 $||$ q3, l', h', k'|] ->
  h = h'.
Proof.
  intros S1 S2 T. inversion T; subst; try reflexivity; exfalso;
  (eapply switchCurr_switchListen_net_link_aux3;
    [ apply S1 | apply S2 | eassumption | discriminate
    | intros q TQ; unfold switchCurr in TQ; invert_disc_prefixes ]).
Qed.
(* end helpers *)

Lemma switchCurr_switchListen_net_link (n n' : Network) (i : nat)
  (a : ActDiscNet) (e e' : Entity) : 
  switchCurrStateEnt e -> switchListenStateEnt e' ->
  e @ i .: n -> e' @ i .: n' -> n -NA- a -NA> n' ->
  a = anTau /\ interEnt e = interEnt e'.
Proof.
  intros SC SL E E' STEP.
  destruct e as [p l h k]; destruct e' as [p' l' h' k'].
  inversion SC; subst.
  match goal with [H : switchCurrStateProt _ |- _] => inversion H; subst end.
  inversion SL; subst.
  match goal with [H : switchListenStateProt _ |- _] => inversion H; subst end.
  destruct a.
  (*Non-silent actions preserve the software component: contradiction.*)
  1-4: exfalso;
    lets PE : stepDiscNet_nonTau_pres_proc STEP E E';
    [ discriminate | ];
    simpl in PE; inversion PE; subst;
    eapply switchCurr_switchListen_net_link_aux2; eassumption.
  (*Silent action.*)
  split; [reflexivity | ].
  destruct (tauLink _ _ STEP) as [j [e0 [e0' [E0 [E0' [T R]]]]]].
  destruct (Nat.eq_dec j i) as [EQ | NEQ].
  - subst j.
    lets EA : entInNetUnique E0 E. lets EB : entInNetUnique E0' E'.
    subst e0 e0'. simpl. eapply switchCurr_switchListen_net_link_aux4; eassumption.
  - lets E1 : R NEQ E'.
    lets EQ : entInNetUnique E E1. inversion EQ; subst.
    exfalso. eapply switchCurr_switchListen_net_link_aux2; eassumption.
Qed.
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
Theorem outgoing_del (n n' : Network) (d : Delay) (v : list BaseType) (t : Time) (i : nat) : 
  n -ND- d -ND> n' -> outgoing v t i n ->
  {p : d <= t | outgoing v (minusTime t d p) i n'}.
Proof.
  intros ND OG. destruct OG as [p l li lo ln k EIN INO].
  link_netentdelfwd_tac e' Y. destr_ent_inter e' p' l' k' li' lo' ln'.
  link_entinterdel_tac Y. inversion Y1 as [? ? ? ? ? ? ? IL OL NL | | | | | ]; subst.
  inversion OL as [ | ? ? ? TL]; subst.
  exists (timedList_del_ge _ _ _ _ _ TL INO). econstructor. apply Y. simpl.
  eapply timedList_del_le; [apply TL | apply INO].
Qed.
(**Proof: Idea is to invert/destruct outgoing to [p, l, {li, lo, ln}, k] @ i.: n & v, t : lo
apply ent-interface del linking tactic
apply interface-list del linkiing tactic
*now we have that lo delays to some lo'*
result & accompanying tactic about timed lists v, t : l & l -d- l' then d <= t &
v (t - d) : l'
contstructor & assumption
.*)

Corollary outgoing_del_contra (n n' : Network) (d : Delay)
  (v : list BaseType) (i : nat) : n -ND- d -ND> n' ->  outgoing v zeroTime i n -> False. intros. 
  addHyp (outgoing_del n n' d v zeroTime i H H0). invertClear H1.
  eapply Rle_not_lt. apply x. simpl. delPos. Qed.

(*If v is outgoing with non-zero timestamp t, and the network performs a
discrete action, then v is still outgoing in the derivative network.*)	 
Theorem outgoing_disc_pres (n n' : Network) (a : ActDiscNet) (v : list BaseType) (t : Time) (i : nat) :
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
Corollary is that whenever t = 0 delay is impossible.
This needs v to have the shape of a notification, [r, m, l], since the listener
can only input a notification of that length.*)
Theorem incomingNetNotif_del (n n' : Network) (d : Delay) (v : list BaseType)
  (t : Time) (i : nat) : 
  reachableNet n -> n -ND- d -ND> n' -> incomingNetNotif v t i n -> length v = 3%nat ->
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
  apply listening_AN_prot; [exact U1 | ]. assert (listeningStateNet i n1) as LSN. eapply del_listening_net.
  eapply reachNetDel. apply RN. apply ND1. apply ND2. apply ED0. inversion LSN as [e IV1 IV2].
  inversion IV1 as [p4 l4 h4 k4 IV3 IV4]. my_applys_eq IV3. rewrite <- IV4 in IV2.
  entnetuniq2 EU n1. inversion EU. reflexivity. apply NSF in DAE. decompAnd2 DAE DI DM.
  apply DI. apply notif_timeout_enabled. assumption.
  (*If t = 0, then we have our contradiction with noSyncNow, just like the last step
  of the previous case.*)
  clear NSD. unfold noSyncNow in NSN. assert (discActEnabled p (chanAN;? v)) as DAE.
  apply listening_AN_prot; [exact U1 | ]. assert (listeningStateNet i n) as LSN. eapply del_listening_net.
  apply RN. apply U. apply H. inversion LSN. inversion H4. my_applys_eq H6.
  cut (e = e0). intros. rewrite H8 in H7. rewrite Heqe0 in H7. inversion H7.
  reflexivity. entnetuniq U e e0. assumption. apply NSN in DAE. decompAnd2 DAE DI DM.
  apply DI. assert (t = zeroTime) as TZ. apply timeEqR. rewrite <- Q.
  reflexivity. rewrite TZ in H0. apply notif_timeout_enabled. assumption. Qed.

(*If v is incomingNetNotif with non-zero timestamp t, and the network performs a discrete
action, then v is still incomingNetNotif in the derivative network.*)
Theorem incomingNetNotif_disc_pres (n n' : Network) (a : ActDiscNet) (v : list BaseType) (t : Time) (i : nat) :
  n -NA- a -NA> n' -> incomingNetNotif v t i n -> 0 < t ->
  incomingNetNotif v t i n'.
Proof.
  introz U. destruct U0 as [p l li lo ln k EIN INN].
  link_netentdiscfwd_tac e' b LE.
  - subst. econstructor; eassumption.
  - destr_ent_inter e' p' l' k' li' lo' ln'.
    econstructor. eassumption.
    eapply stepEnt_disc_pres_notif_pos; eassumption.
Qed.
(**Proof: Analogous to (outgoing_disc_pres).*)

(*If an entity is inPosNet l' i n', and there is some n such that it delays to n' via d,
then i is in inPosNet l i n for some l and the difference between the positions is at most
speedMax*d*)
Lemma inPos_del_bound_bkwd (n n' : Network) (d : Delay) (l' : Position) (i : nat) :
  inPosNet l' i n' -> n -ND- d -ND> n' -> exists l,
  inPosNet l i n /\ dist2d l l' <= speedMax * d.
Proof.
  intros IP ND. destruct IP as [p h k EIN].
  link_netentdelbkwd_tac e Y. lets BM : boundedMovement Y0.
  destruct e as [p0 l0 h0 k0]. exists l0. split.
  - econstructor. eassumption.
  - simpl in BM. rewrite Rmult_comm. destruct d as [[dr dp]]. simpl in *. exact BM.
Qed.
(**Proof: Salvaged from old Coq model (pos_bound?).*)

Conjecture currMode_intro : forall (m : Mode) (e : Entity) (i : nat) (n : Network),
  m = currModeEnt e -> e @ i .: n -> currModeNet m i n.
(**Proof: Obvious- lift currModeEnt to currModeNet*)

Lemma inPos_ex : forall (i : nat) (n : Network) (e : Entity),
  e @ i .: n -> exists l, inPosNet l i n.
Proof.
  intros i n e EIN. destruct e as [p l h k]. exists l. econstructor. eassumption.
Qed.
(**Proof: Obvious- every entity has a position*)

Lemma distNet_intro : forall (e1 e2 : Entity) (i j : nat) (n : Network) (x : Distance),
  e1 @ i .: n -> e2 @ j .: n -> x = mkDistance (dist2d e1 e2) -> distNet i j n x.
Proof.
  intros e1 e2 i j n x E1 E2 EQ. subst x.
  destruct e1 as [p1 l1 h1 k1]. destruct e2 as [p2 l2 h2 k2].
  change (distNet i j n (distFun l1 l2)).
  apply dnWitness; econstructor; eassumption.
Qed.
(**Proof: Obvious from definitions of things*)

Lemma inPos_pos : forall (e : Entity) (i : nat) (l : Position) (n : Network),
  e @ i .: n -> inPosNet l i n -> posEnt e = l.
Proof.
  intros e i l n EIN IP. destruct IP as [p h k EIN'].
  lets EQ : entInNetUnique EIN EIN'. subst e. reflexivity.
Qed.
(**Proof: Obvious- invert/deconstruct inPostNet*)

Conjecture reachable_net_ent : forall (n : Network) (e : Entity) (i : nat),
  reachableNet n -> e @ i .: n -> reachableEnt e.
(**Proof: Obvious- inversion on reachableNet*)

(*There are already proofs like this about distance in networks, just not using distNet*)
Lemma disc_pres_distNet_bkwd : forall (n n' : Network) (a : ActDiscNet)
  (i j : nat) (x : Distance),
  n -NA- a -NA> n' -> distNet i j n' x -> distNet i j n x.
Proof.
  intros n n' a i j x ST DN. destruct DN as [l l' IP IP'].
  apply dnWitness.
  - apply (proj2 (inPos_pres_disc n n' a l i ST)). assumption.
  - apply (proj2 (inPos_pres_disc n n' a l' j ST)). assumption.
Qed.
(**Proof: Obvious- Lift other proofs which say essentially the same thing and apply constructor for distNet*)

(*There are already proofs like this about distance in networks, just not using distNet*)
Lemma del_link_distNet_bkwd : forall (n n' : Network) (d : Delay)
  (i j : nat) (x' : Distance),
  n -ND- d -ND> n' -> distNet i j n' x' ->
  exists x, distNet i j n x /\ x <= x' + 2*speedMax*d.
Proof.
  intros n n' d i j x' ND DN.
  destruct DN as [l1 l2 IP1 IP2].
  destruct IP1 as [p1 h1 k1 E1]. destruct IP2 as [p2 h2 k2 E2].
  destruct (link_net_ent_del_bkwd n n' _ i d ND E1) as [e1 [E1n D1]].
  destruct (link_net_ent_del_bkwd n n' _ j d ND E2) as [e2 [E2n D2]].
  exists (distFun (posEnt e1) (posEnt e2)). split.
  - destruct e1 as [q1 m1 g1 r1]. destruct e2 as [q2 m2 g2 r2].
    apply dnWitness; econstructor; eassumption.
  - pose proof (bndDistLwr n n' e1 e2 _ _ i j d ND E1n E1 E2n E2) as B.
    unfold distFun. cbn [distance]. simpl posEnt in B. lra.
Qed.
(**Proof: Obvious- Lift similar proofs & apply distNet constructor*)

Lemma distNet_elim : forall (i j : nat) (n : Network) (x : Distance),
  distNet i j n x -> exists e1 e2,
  e1 @ i .: n /\ e2 @ j .: n /\ x = {| distance := dist2d e1 e2 |}.
Proof.
  intros i j n x H. destruct H as [l l' H1 H2].
  destruct H1 as [p h k H1]. destruct H2 as [p' h' k' H2].
  exists ([|p, l, h, k|]) ([|p', l', h', k'|]).
  split; [assumption | split; [assumption | reflexivity]].
Qed. 

(*Any entity within range of a broadcast inputs that broadcast.*)
Lemma inRange_out_input (n n' : Network) (v : list BaseType) (l : Position)
  (r x: Distance) (i j : nat) (e : Entity) :
  n -NA- ([-v, l, r-]) /! i -NA> n' -> e @ j .: n -> i <> j -> distNet i j n' x ->
  x <= r -> exists e', e -EA- ([-v, l, r-]) #? ->> e' /\ e' @ j .: n'.
Proof.
  intros OUT EJ NEQ DN XR.
  destruct (outputMatch n n' i ([-v, l, r-]) OUT) as [ei [ei' [EI [EI' STI]]]].
  assert (PL : posEnt ei' = l) by (inversion STI; subst; reflexivity).
  destruct DN as [la lb IPa IPb].
  destruct IPa as [pa ha ka Ea]. destruct IPb as [pb hb kb Eb].
  assert (LA : la = l).
  { rewrite <- (entInNetUnique _ _ _ _ Ea EI') in PL. simpl in PL. exact PL. }
  subst la.
  destruct (outputMismatch n n' _ i j ([-v, l, r-]) OUT Eb NEQ) as [e0 [E0 ST]].
  assert (EQ0 : e0 = e) by (eapply entInNetUnique; eassumption).
  subst e0.
  destruct ST as [ST | ST].
  - exists ([|pb, lb, hb, kb|]). split; assumption.
  - exfalso. inversion ST; subst.
    unfold distFun in XR. cbn [distance] in XR.
    rewrite distSymmetric in XR. lra.
Qed.

Conjecture transGuard_disc_pres : forall (n n' : Network)
  (a : ActDiscNet) (t : Time) (i : nat),
  n -NA- a -NA> n' -> transGuard t i n -> transGuard t i n'.
(**Proof: Obvious: discrete action preserves guard on mode state, immediate from mode state semantics*)

Lemma transGuard_elim : forall (t : Time) (i : nat) (n : Network),
  transGuard t i n -> exists m m',
  mState_in_net (<| m, m', t |>) i n.
Proof.
  intros t i n H. destruct H as [p l h m m' H].
  exists m m'. econstructor. exact H.
Qed.
(**Proof: Obvious: transGuard definition*)

Lemma transGuard_intro : forall (t : Time) (i : nat) (n : Network)
  (m m' : Mode), mState_in_net (<| m, m', t |>) i n ->
  transGuard t i n.
Proof.
  intros t i n m m' H. destruct H as [p l h H].
  econstructor. exact H.
Qed.
(**Proof: Immediate from definition of transGuard*)

Lemma mState_disc_pres : forall (n n' : Network) (i : nat)
  (a : ActDiscNet) (k  : ModeState), n -NA- a -NA> n' -> mState_in_net k i n ->
  exists k', mState_in_net k' i n'.
Proof.
  intros n n' i a k STEP MS. destruct MS as [p l h E].
  destruct (link_net_ent_disc_fwd_ex n n' a STEP _ i E) as [e' E'].
  destruct e' as [p' l' h' k']. exists k'. econstructor. exact E'.
Qed.
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

(* begin helpers for currModeNet_dec *)
From Stdlib Require Import Classical.
(* end helpers *)

Lemma currModeNet_dec : forall (m : Mode) (i : nat) (n : Network),
  currModeNet m i n \/ ~currModeNet m i n.
Proof.
  intros m i n. apply classic.
Qed.
(**Proof: Obvious- not important to prove as it's just law of excluded middle*)

Lemma initial_failSafe (n : Network) (e : Entity) (i : nat) :
  initialNet n -> e @ i .: n -> failSafe e.
  (*Proof: Follows directly from the definition of initial*)
  introz U. generalize dependent i. induction n; intros i U0.
  inversion U0. inversion U. subst. inversion U0. subst.
  inversion H1. assumption. eapply IHn; eassumption. Qed.

(**Broadly speaking, a linking theorem.*)
Lemma reachable_net_prot : forall (n : Network) (i : nat)
  (p : ProcTerm) (l : Position) (h : Interface) (k : ModeState),
  reachableNet n -> [|p, l, h, k|] @ i .: n ->
  reachableProt p.
Proof.
  intros n i p l h k R E. eapply link_net_prot_reach; eassumption.
Qed.
(**Proof: DOES THEOREM LIKE THIS ALREADY EXIST? Induction on reachableNet and some linking results*)

(**Delay preserves the current mode*)
Lemma currMode_del_pres_bkwd (n n' : Network) (d : Delay) (m : Mode) (i : nat) :
  n -ND- d -ND> n' -> currModeNet m i n' -> currModeNet m i n.
Proof.
  intros D C. apply (proj2 (currModeNet_del_pres n n' d m i D)). exact C.
Qed.
(**Proof: Follows directly from mode state semantics, and linking of delay from network to entity to modestate*)

Conjecture inPos_ent_net : forall (l : Position) (e : Entity) (i : nat) (n : Network),
  inPosEnt l e -> e @ i .: n -> inPosNet l i n.
(**Proof: Obvious from definitions*)

Lemma inPos_unique : forall (l l' : Position) (i : nat) (n : Network),
  inPosNet l i n -> inPosNet l' i n -> l = l'.
Proof.
  intros l l' i n H H0. destruct H as [p h k E]. destruct H0 as [p0 h0 k0 E0].
  lets EQ : entInNetUnique E E0. inversion EQ. reflexivity.
Qed.
(**Proof: Obvious- inversion and apply entInNetUnique*)

(*An output by entity i from the network n means that the message is now pending
notification with timestamp AN.*)
Lemma outNet_incomingNetNotif (n n' : Network) (v : list BaseType) (r : Distance)
  (l : Position) (i : nat) : n -NA- ([-v, l, r-]) /! i -NA> n' ->
  incomingNetNotif ((baseDistance r)::v) adaptNotif i n'.
Proof.
  intros H.
  destruct (outputMatch n n' i ([-v, l, r-]) H) as [e [e' [E [E' S]]]].
  inversion S; subst.
  match goal with [HI : _ -i- chanIOEnv _! _ !_ _ -i> _ |- _] => inversion HI; subst end.
  econstructor; [eassumption | ].
  eapply notifList_in_hd. eassumption.
Qed.
(**Proof: Follows from interface semantics.*)

(** Linking theorem.*)
Lemma incoming_net_ent (v : list BaseType) (i : nat) (n : Network) :
  incomingNet v i n -> exists e, incomingEnt v e /\ e @ i .: n. intro U.
  invertClear U. exists ([|p, l, {| li := li; lo := lo; ln := ln |}, k|]).
  split. repeat constructor. assumption. assumption. Qed.

(** Linking theorem.*)
Lemma incoming_ent_net (v : list BaseType) (e : Entity) (i : nat) (n : Network) :
  incomingEnt v e -> e @ i .: n -> incomingNet v i n.
  (*Proof: Follows directly from the definition*)
  introz U. inversion U. subst. destruct h. econstructor. eassumption.
  inversion U. subst. inversion H1. assumption. Qed.

Ltac inposdp :=
  match goal with
  [ w : ?n -NA- _ -NA> ?n', H : inPosNet ?l ?i ?n' |- inPosNet ?l ?i ?n] =>
  eapply inPos_pres_disc; [apply w | assumption]
  end.

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
  (switchCurrStateNet i n).
Proof.
  intros. inversion H. inversion H0. inversion H2. inversion H4.
  left. do 4 eexists. netState_auto_tac.
  right. left. do 3 eexists. netState_auto_tac.
  right. right. left. eexists. netState_auto_tac.
  right. right. right. netState_auto_tac.
Qed.

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
Proof.
  intros U V. inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  assert (currModeNet (currModeEnt ([|p1 $||$ p2 $||$ p3, l, h, k|])) i n) as CM
    by (eapply currMode_intro; [reflexivity | exact EIN]).
  lets EQ : tfsNext_currModeNet_eq CM U. simpl in EQ.
  assert (currModeMState k -mtr-> failSafeSucc m) as FS
    by (rewrite EQ; apply failSafeSucc_successor).
  destruct (mState_stable_next_enabled _ _ FS) as [MS | MS].
  - eapply ent_del_sync_mState_not with (a := chanMStable *!); [ | exact MS | exact ED].
    dae_overlap. eapply tfsNext_mStable_out. exact TS.
  - eapply ent_del_sync_mState_not with (a := chanMNext ;! [baseMode (failSafeSucc m)]);
      [ | exact MS | exact ED].
    dae_overlap. apply tfsNext_mNext_out. exact TS.
Qed.

Lemma tfsStart_urgent_net i n n' d :
  tfsStartStateNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros U V. inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  eapply ent_del_sync_mState_not with (a := chanMCurr ;? [baseMode (currModeMState k)]);
    [ | apply modeState_curr_enabled | exact ED].
  dae_overlap. apply tfsStart_mCurr_in. exact TS.
Qed.

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
