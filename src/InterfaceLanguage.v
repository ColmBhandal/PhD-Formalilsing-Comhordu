(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

Require Import ComhCoq.Extras.LibTactics.

Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.

(***************** Timed lists *****************)

(** A timed element is a vector of base values, along with a timestamp.*)
Record TimedEl : Type := mkTimedEl
{
  msg : list Base;
  stamp : Time
}.
Notation "<( m , t )>" := (mkTimedEl m t) (at level 40).

(** Equality is decidable on timed elements.*)
Lemma eqDecTimedEl : eqDec TimedEl. unfold eqDec.
  destruct x1, x2. addHyp (eqDecTime stamp0 stamp1).
  invertClear H. addHyp (list_eq_dec eqDecBase msg0 msg1).
  invertClear H. left. subst. reflexivity. right.
  unfold not. intros. apply H1. inversion H. reflexivity.
  right. unfold not. intros. apply H0. inversion H. reflexivity.
  Qed.

(** A timed list is a list of timed elements.*)
Definition TimedList : Type := list TimedEl.

(**An action is either a delay, an input or an output.*)
Inductive ActTimedList :=
  | atlDel :> Delay -> ActTimedList
  | atlIn : list Base -> ActTimedList
  | atlOut : list Base -> ActTimedList.

Notation "v ?? " := (atlIn v) (at level 30).
Notation "v !! " := (atlOut v) (at level 30).

Reserved Notation "l -tl- a -tl> l'" (at level 75). 

(** The operational semantics for timed lists. Note that the law "buff" will have
to be defined separately for each of the sub-type lists individually,
because it is parametrised on a time T.*)
Inductive stepTimedList : TimedList -> ActTimedList -> TimedList -> Prop :=
  (** If the head of the list has timed out (zero time) then it can be output.*)
  | stepTlFwdHd : forall (v : list Base) (l : TimedList),
    <(v, zeroTime)> :: l -tl- v!! -tl> l 
  (** If the tail can evolve by outputting an element, then the whole list can evolve as
  such.*)
  | stepTlFwd : forall (l l' : TimedList) (v1 : list Base) (e : TimedEl),
    l -tl- v1!! -tl> l' -> e :: l -tl- v1!! -tl> e :: l'
  (** The empty list can delay by any amount and stay as the empty list.*)
  | stepTlDelEmp : forall d : Delay, [] -tl- d -tl> [] 
  (** If the tail can delay by d, and the timestamp on the head is t + d, then the
  whole list evolves by the tail delaying and the head element timestap reducing to t.
  Note that this differs slightly from the formulation on paper, which asserts that the
  timestamp of the head element is t >= d, and then the resulting timestamp is t - d.
  The reason for this alternative formulation is to avoid subtraction of delays/times.*)
  | stepTlDel : forall (l l' : TimedList) (d : Delay) (v : list Base) (t t' : Time),
    l -tl- d -tl> l' -> t = t' +dt+ d -> <(v, t)> :: l -tl- d -tl> 
    <(v, t')> :: l'
  where "l -tl- a -tl> l'" := (stepTimedList l a l').

(** The delay action preserves the size of a timed list.*)
Lemma delPresSizeTL : forall (l l' : TimedList) (d : Delay),
  l -tl- d -tl> l' -> length l = length l'. intros.
  remember (atlDel d) as a. induction H. inversion Heqa.
  apply IHstepTimedList in Heqa. simpl. rewrite Heqa. reflexivity.
  reflexivity. apply IHstepTimedList in Heqa. simpl.
  rewrite Heqa. reflexivity. Qed.

(** If [] delays to l', then l' = []*)
Lemma empLeftDelTL : forall (l' : TimedList) (d : Delay),
  [] -tl- d -tl> l' -> l' = []. intros. apply delPresSizeTL in H.
  destruct l'. reflexivity. inversion H. Qed.

(** If l delays to [], then l = []*)
Lemma empRightDelTL : forall (l : TimedList) (d : Delay),
  l -tl- d -tl> [] -> l = []. intros. apply delPresSizeTL in H.
  destruct l. reflexivity. inversion H. Qed.

(** If a timed list l can delay by d to l' which in turn can delay by d' to l'',
then l can delay by d+d' to l''.*)
Lemma delAddTL : forall (l l' l'' : TimedList) (d d' : Delay),
  l -tl- d -tl> l' -> l' -tl- d' -tl> l'' ->
  l -tl- d +d+ d' -tl> l''. induction l; intros.
  erewrite empLeftDelTL. constructor. assert (l' = []).
  eapply empLeftDelTL. apply H. rewrite H1 in H0. apply H0.
  destruct a. destruct l'. apply empRightDelTL in H. inversion H.
  rename t into a. destruct a. inversion H. destruct l''.
  apply empRightDelTL in H0. inversion H0.
  destruct t0. inversion H0. rewrite H18 in H9.
  rewrite delTimeAddAssoc in H9. rewrite timeDelAddSwitch in H9.
  rewrite addDelayComm in H9. rewrite H9. constructor.
  eapply IHl. apply H3. assumption. reflexivity. Qed.

Lemma timedList_timeout_enabled v l :
  <( v, zeroTime )> _: l -> exists l', l -tl- v !! -tl> l'.
  introz U. induction l; inversion U. subst.
  exists l. constructor. apply IHl in H.
  ex_flat. eexists. eapply stepTlFwd. eassumption. Qed.

Lemma timedList_del_le l l' d v t q :
   l -tl- atlDel d -tl> l' -> <( v, t )> _: l ->
  <( v, minusTime t d q )> _: l'. Admitted.


(***************** Input, Output & Notification lists *****************)
(*These will be syntactically the same as timed lists, with the exception of
a wrapper. Each will then diverege in their extension of the semantics of timed lists:
lifting the timed list relation and then adding some new laws specific to the type of list
(input, output or notification).*)

Reserved Notation "l -il- a -il> l'" (at level 75). 
Reserved Notation "l -ol- a -ol> l'" (at level 75). 
Reserved Notation "l -nl- a -nl> l'" (at level 75). 

(** Syntactially, an input list is essentially a timed list.*)
Record InputList : Type := mkInputList {inList : TimedList}.

(** Syntactially, an input list is essentially a timed list.*)
Record OutputList : Type := mkOutputList {outList : TimedList}.

(** Syntactially, an input list is essentially a timed list.*)
Record NotifList : Type := mkNotifList {notifList : TimedList}.

(** Semantics for the input list.*)
Inductive stepInputList : InputList -> ActTimedList -> InputList -> Prop :=
  (** Buffer a message and stamp it with zero time.*)
  | stepIlBuff : forall (l : TimedList) (v : list Base),
    mkInputList l -il- v ?? -il> mkInputList (<(v, zeroTime)> :: l)
  (** Delay causes all the messages in the list to be lost. In other words,
  any list can delay and become the empty list.*)
  | stepIlDel : forall (l : InputList) (d : Delay),
    l -il- d -il> mkInputList []
  (** Lift the timed list semantics to these specialised semantics.*)
  | stepIlLift : forall (l l' : TimedList) (a : ActTimedList),
    l -tl- a -tl> l' -> mkInputList l -il- a -il> mkInputList l'
  where "l -il- a -il> l'" := (stepInputList l a l').

Open Scope nat_scope.

(** The size of a list is non-increasing for an input list.*)
Lemma delNonIncSizeIL : forall (l l' : InputList) (d : Delay),
  l -il- d -il> l' -> length (inList l') <= length (inList l).
  intros. inversion H. simpl. apply le_0_n.
  apply delPresSizeTL in H0. simpl. rewrite H0.
  constructor. Qed.

(** If an input list l can delay by d to l' which in turn can delay by d' to l'',
then l can delay by d+d' to l''.*)
Lemma delAddInput : forall (l l' l'' : InputList) (d d' : Delay),
  l -il- d -il> l' -> l' -il- d' -il> l'' ->
  l -il- d +d+ d' -il> l''. intros. destruct l''.
  destruct inList0. constructor. rename t into a.
  destruct l'. destruct inList1. apply delNonIncSizeIL in H0.
  inversion H0. rename t into b. destruct l. destruct inList2.
  apply delNonIncSizeIL in H. inversion H. rename t into c.
  swap a c. inversion H. inversion H0.
  constructor. eapply delAddTL. apply H4. assumption. Qed.
  
(** An input list l is action enabled for the action a iff
there is some derivative list l' such that l transitions to l' via a.*)
Definition actEnabledInList (l : InputList) (a : ActTimedList) : Prop :=
  exists l', l -il- a -il> l'.

(** An input list can always input a message.*)
Lemma inListInEnabled : forall (l : InputList) (v : list Base),
  actEnabledInList l (v??). intros. destruct l as [l].
  exists (mkInputList (<(v, zeroTime)> :: l)). constructor. Qed.

(**Semantics for the output list.*)
Inductive stepOutputList : OutputList -> ActTimedList -> OutputList -> Prop :=
  (** Buffer a message and stamp it with a timestamp of msgLatency.*)
  | stepOlBuff : forall (l : TimedList) (v : list Base),
    mkOutputList l -ol- v?? -ol> mkOutputList (<(v, msgLatency)> :: l)
  (** Lift the timed list semantics to these specialised semantics.*)
  | stepOlLift : forall (l l' : TimedList) (a : ActTimedList),
    l -tl- a -tl> l' -> mkOutputList l -ol- a -ol> mkOutputList l'
  where "l -ol- a -ol> l'" := (stepOutputList l a l').

Lemma delAddOutput : forall (l l' l'' : OutputList) (d d' : Delay),
  l -ol- d -ol> l' -> l' -ol- d' -ol> l'' ->
  l -ol- d +d+ d' -ol> l''. intros. inversion H.
  rewrite <- H4 in H0. inversion H0. constructor.
  eapply delAddTL. apply H1. assumption. Qed.

(**Semantics for the notification list.*)
Inductive stepNotifList : NotifList -> ActTimedList -> NotifList -> Prop :=
  (** Buffer a message and stamp it with a timestamp of adaptNotif.*)
  | stepNlBuff : forall (l : TimedList) (v : list Base),
    mkNotifList l -nl- v?? -nl> mkNotifList (<(v, adaptNotif)> :: l)
  (** If the tail can delay to some l', and the head has timed out, then the whole
  list can delay to l', essentially dropping the head.*)
  | stepNlDrop : forall (l : TimedList) (l' : NotifList)
    (d : Delay) (v : list Base), mkNotifList l -nl- d -nl> l' ->
    mkNotifList (<(v, zeroTime)> :: l) -nl- d -nl> l'
  | stepNlDelAdd : forall (l l' l'' : NotifList) (d d' : Delay),
    l -nl- d -nl> l' -> l' -nl- d' -nl> l'' ->
    l -nl- (d +d+ d') -nl> l''
  (** Lift the timed list semantics to these specialised semantics.*)
  | stepNlLift : forall (l l' : TimedList) (a : ActTimedList),
    l -tl- a -tl> l' -> mkNotifList l -nl- a -nl> mkNotifList l'
  where "l -nl- a -nl> l'" := (stepNotifList l a l').

  Open Scope R_scope.

Lemma notifList_del_le ln ln' d v t q :
  ln -nl- atlDel d -nl> ln' -> <( v, t )> _: notifList ln ->
  <( v, minusTime t d q )> _: notifList ln'. introz U.
  (*Proof: Induction on the proof of the delay of the notifList.*)
  remember (atlDel d). generalize dependent d.
  generalize dependent t. induction U; intros t U0 d2 q EQ; subst.
  (*Eliminate the input case, which is clearly contradictory to the delay.*)
  inversion EQ.
  (*Next case follows by induction and the fact that t is positive.*)
  apply IHU. inversion U0. inversion H.
  clear IHU. rewrite <- H2 in q. false. eapply Rle_not_lt.
  apply q. delPos. assumption. assumption.
  (*The additive case also follows by induction. We basically thread
  one inductive case to the other.*)
  inversion EQ. generalize dependent q. rewrite <- H0.
  intro q. clear EQ H0.
  assert (atlDel d = atlDel d) as EQD; [ reflexivity |].
  assert (atlDel d' = atlDel d') as EQD'; [ reflexivity |].
  assert (d <= t) as DLE. eapply Rle_trans; [ | apply q].
  simpl. Rplus_le_tac. apply Rlt_le. delPos.
  lets IH1 : IHU1 U0 DLE EQD.
  assert (d' <= minusTime t d DLE) as DLE'. simpl.
  apply Rplus_le_swap_lr. rewrite Rplus_comm. apply q.
  lets IH2 : IHU2 IH1 DLE' EQD'. my_applys_eq IH2.
  f_equal. apply timeEqR. simpl. ring.
  (*Finally we have the lifting case, in which case we lift a similar
  (analogous) result for timed lists.*)
  eapply timedList_del_le; eassumption. Qed.

Lemma timeSplit_inputList l l'' (d d' d'' : Delay) :
  l -il- d'' -il> l'' -> d'' = d +d+ d' ->
  exists l', l -il- d -il> l' /\ l' -il- d' -il> l''.
  Admitted. (*#timeSplit-timedList*)

Lemma timeSplit_outputList l l'' (d d' d''  : Delay) :
  l -ol- d'' -ol> l'' -> d'' = d +d+ d' ->
  exists l', l -ol- d -ol> l' /\ l' -ol- d' -ol> l''.
  Admitted. (*#timeSplit-timedList*)

Lemma timeSplit_notifList l l'' (d d' d''  : Delay) :
  l -nl- d'' -nl> l'' -> d'' = d +d+ d' ->
  exists l', l -nl- d -nl> l' /\ l' -nl- d' -nl> l''.
  Admitted. (*#timeSplit-timedList*)

(***************** Interface Syntax & Semantics *****************)

Record Interface : Type := mkInterface
{
  li : InputList;
  lo : OutputList;
  ln : NotifList
}.

(** Equality is decidable on interfaces.*)
Lemma eqDecInterface : eqDec Interface.
  unfold eqDec. destruct x1, x2.
  destruct li0, lo0, ln0, li1, lo1, ln1.
  addHyp (list_eq_dec eqDecTimedEl inList0 inList1).
  addHyp (list_eq_dec eqDecTimedEl outList0 outList1).
  addHyp (list_eq_dec eqDecTimedEl notifList0 notifList1).
  invertClear H. invertClear H0. invertClear H1. left.
  subst. reflexivity. right. unfold not. intros.
  apply H0. invertClear H1. reflexivity. right. unfold not.
  intros. apply H. invertClear H0. reflexivity. right.
  unfold not. intros. apply H2. invertClear H. reflexivity.
  Qed.

(** Actions for the interface semantics. We have delay, input of a list of base values
on a channel, output of the same, and finally output of a list of base values on a
channel augmented with coverage information.*)
Inductive ActInter :=
  | aiDel :> Delay -> ActInter 
  | aiIn : Channel -> list Base -> ActInter
  | aiOut : Channel -> list Base -> ActInter
  (** The final parameter is the coverage.*)
  | aiOutCov : Channel -> list Base -> Distance -> ActInter.

Notation "c !I!" := (aiOut c []) (at level 30).
Notation "c {? v" := (aiIn c v) (at level 30).
Notation "c {! v" := (aiOut c v) (at level 30).
Notation "c _! v !_ r" := (aiOutCov c v r) (at level 30).

Reserved Notation "i -i- a -i> i'" (at level 75).

(** The semantics for the interface.*)
Inductive stepInter : Interface -> ActInter -> Interface -> Prop :=
  | stepIntDel : forall (l1 l1': InputList) (l2 l2': OutputList)
    (l3 l3' : NotifList) (d : Delay), l1 -il- d -il> l1' ->
    l2 -ol- d -ol> l2' -> l3 -nl- d -nl> l3' ->
    (mkInterface l1 l2 l3) -i- d -i> (mkInterface l1' l2' l3')
  | stepIntBuffIn : forall (l1 l1': InputList) (l2 : OutputList)
    (l3 : NotifList) (v : list Base), l1 -il- v?? -il> l1' ->
    (mkInterface l1 l2 l3) -i- chanIOEnv {? v -i> (mkInterface l1' l2 l3)
  | stepIntFwdIn : forall (l1 l1': InputList) (l2 : OutputList)
    (l3 : NotifList) (v : list Base), l1 -il- v!! -il> l1' ->
    (mkInterface l1 l2 l3) -i- chanInProc {! v -i> (mkInterface l1' l2 l3)
  | stepIntBuffOut : forall (l1 : InputList) (l2 l2' : OutputList)
    (l3 : NotifList) (v : list Base), l2 -ol- v?? -ol> l2' ->
    (mkInterface l1 l2 l3) -i- chanOutProc {? v -i> (mkInterface l1 l2' l3)
  | stepIntFwdOut : forall (l1 : InputList) (l2 l2' : OutputList)
    (l3 l3' : NotifList) (v : list Base) (r : Distance),
    l2 -ol- v!! -ol> l2' -> l3 -nl- ((baseDistance r) :: v) ?? -nl> l3' ->
    (mkInterface l1 l2 l3) -i- chanIOEnv _! v !_ r -i> (mkInterface l1 l2' l3')
  | stepIntFwdNotif : forall (l1 : InputList) (l2 : OutputList)
    (l3 l3' : NotifList) (v : list Base), l3 -nl- v!! -nl> l3' ->
    (mkInterface l1 l2 l3) -i- chanAN {! v -i> (mkInterface l1 l2 l3')
  where "i -i- a -i> i'" := (stepInter i a i').

(** An interface i is action enabled for the action a iff
there is some derivative interface i' such that i transitions to i' via a.*)
Definition actEnabledInter (i : Interface) (a : ActInter) : Prop :=
  exists i', i -i- a -i> i'.

(** incomingInter v i means v is in the incoming list of the interface i.*)
Inductive incomingInter (v : list Base) : Interface -> Prop :=
  iciWitness (li : InputList) (lo : OutputList) (ln : NotifList) :
  <( v, zeroTime )> _: inList li ->
  incomingInter v (mkInterface li lo ln).

(** An interface is enabled on a discrete action if it can perform a corresponding
action. The actions in question can be input or output, but there will be no case
for tau because interfaces can't do a tau action.*)
Inductive discActEnabledInter : DiscAct -> Interface -> Prop :=
  | daeiIn : forall (c : Channel) (v : list Base) (i i' : Interface),
    i -i- c {? v -i> i' -> discActEnabledInter (c ;? v) i
  | daeiOut : forall (c : Channel) (v : list Base) (i i' : Interface),
    i -i- c {! v -i> i' -> discActEnabledInter (c ;! v) i.

(***************** Results *****************)

(** An interface is always enabled on an input on the channel chanIOEnv.*)
Theorem interfaceInEnabled : forall (i : Interface) (v : list Base),
  actEnabledInter i (chanIOEnv {? v). destruct i. intros.
  addHyp (inListInEnabled li0 v). invertClear H. rename x into l'.
  exists ({| li := l'; lo := lo0; ln := ln0 |}). constructor.
  assumption. Qed.

Lemma delAddInter : forall (i i' i'' : Interface) (d d' : Delay),
  i -i- d -i> i' -> i' -i- d' -i> i'' ->
  i -i- d +d+ d' -i> i''. destruct i as [l1 l2 l3]. intros.
  destruct i' as [l1' l2' l3']. destruct i'' as [l1'' l2'' l3''].
  invertClear H. invertClear H0. constructor.
  eapply delAddInput. apply H6. assumption.
  eapply delAddOutput. apply H9. assumption.
  eapply stepNlDelAdd. apply H10. assumption. Qed.

Conjecture outList_received_in : forall (l l' : OutputList) (v : list Base),
  l -ol- v ?? -ol> l' -> <(v, msgLatency)> _: outList l'.
(**Proof: Obvious from outList semantics*)

Conjecture inList_received_in : forall (l l' : InputList) (v : list Base),
  l -il- v ?? -il> l' -> <(v, msgLatency)> _: inList l'.
(**Proof: Obvious from inList semantics*)

Conjecture notifList_received_in : forall (l l' : NotifList) (v : list Base),
  l -nl- v ?? -nl> l' -> <(v, msgLatency)> _: notifList l'.
(**Proof: Obvious from notifList semantics*)

(*LOCAL TIDY*)

Lemma inList_pres_input v l l' a :
  <( v, zeroTime )> _: inList l -> l -il- a -il> l' ->
  <( v, zeroTime )> _: inList l' \/ a = v !!. Admitted. (*5*)

(*-LOCAL TIDY*)

(*If the interface component does a step, and there's some timed out message in the input
list, then that message is either still there, or the action was an output of the value in
question on the input channel for the software component.*)
Lemma inList_inter_pres_input v lix lox lnx lix' lox' lnx' a :
  (forall d, a <> aiDel d) -> <(v, zeroTime )> _: inList lix ->
  mkInterface lix lox lnx -i- a -i> mkInterface lix' lox' lnx' ->
  <(v, zeroTime )> _: inList lix' \/
  a = chanInProc{! v. intros.
  (*Proof: Case analyse the interface transition.*)
  inversion H1;
  (*In most of the remaining cases, the input list is preserved, giving the LHS.
  The only cases in which itis not preserved is if an element is buffered or if an
  element leaves the list.*)
  try (subst; left; assumption).
  (*Delay contradicts one of our hypotheses.*)
  false.
  (*Finally we just use an auxiliary result on inList to prove the remaining
  cases.*)
  lets IPI : inList_pres_input H0 H6. elim_intro IPI IL VEQ;
  [left | right; inversion VEQ]; assumption.
  lets IPI : inList_pres_input H0 H6. elim_intro IPI IL VEQ;
  [left | right; inversion VEQ]. assumption. reflexivity.
  Qed.

Lemma timeSplit_inter (h h'' : Interface) (d d' d'' : Delay) :
  h -i- d'' -i> h'' -> d'' = d +d+ d' ->
  exists h', h -i- d -i> h' /\ h' -i- d' -i> h''.
  (*Proof: Follows from time-split results on timed lists*)
  intros. inversion H.
  lets TSI : timeSplit_inputList H2 H0.
  lets TSO : timeSplit_outputList H3 H0.
  lets TSN : timeSplit_notifList H5 H0.
  ex_flat. or_flat. and_flat.
  exists ({| li := x1; lo := x0; ln := x |}).
  split; constructor; eassumption. Qed.

(*A notification list with a timed-out element can output that element.*)
Lemma notif_timeout_enabled_aux v lnx :
  <( v, zeroTime )> _: notifList lnx ->
  exists lnx', lnx -nl- (v !!) -nl> lnx'.
  (*Proof: Lift a more general result on timed lists*)
  introz U. lets TTE : timedList_timeout_enabled U.
  ex_flat. destruct lnx. simpl in H. eexists.
  econstructor. eassumption. Qed.

Lemma notif_timeout_enabled v lix lox lnx :
  <( v, zeroTime )> _: notifList lnx ->
  discActEnabledInter (chanAN ;! v) (mkInterface lix lox lnx).
  (*Proof: Follows from the timeout rule of timed lists
  and the interface semantics.*)
  introz U.
  (*First thing is that we show the transition is possible on the
  notification list.*)
  assert (exists lnx', lnx -nl- (v !!) -nl> lnx') as EXL.
  apply notif_timeout_enabled_aux; assumption. ex_flat.
  eapply daeiOut. eapply stepIntFwdNotif. eassumption.
  Qed.

(*LOCAL TIDY*)

Lemma interface_outProc_in (h : Interface) (v : list Base) :
  discActEnabledInter (chanOutProc ;? v) h.
  (*Proof: Obvious from semantics*)
  destruct h. destruct lo0. repeat econstructor. Qed.

Lemma inter_mStable_in_not h h' : h -i- chanMStable {! [] -i> h' -> False.
  introz U. inversion U. Qed.

Lemma inter_abort_in_not h h' :
  h -i- chanAbort {?[] -i> h' -> False.
  introz U. inversion U. Qed.

Lemma outList_in_input_pres v u t lo lo' :
  <( v, t )> _: outList lo -> outList lo -tl- u ?? -tl> outList lo' ->
  <( v, t )> _: outList lo'. Admitted. (*6*)
(*Prove in bulk: #interface-linking*)

Lemma outList_in_output_pres v u t lo lo' :
  <( v, t )> _: outList lo -> outList lo -tl- u !! -tl> outList lo' ->
  0 < t -> <( v, t )> _: outList lo'. Admitted. (*6*)
(*Prove in bulk: #interface-linking*)

(*-LOCAL TIDY*)
