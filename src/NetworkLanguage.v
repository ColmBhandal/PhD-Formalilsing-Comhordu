(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)


(***************************** Standard Imports *****************************)

Require Import Coq.Program.Equality.
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Export EntityLanguage.
Require Import ComhCoq.EntAuxResults.

(***************Network syntax stuff*********************)

(**A network of entities is a list of entities.*)
Definition Network : Type := list Entity.

Coercion singNet (e : Entity) : Network := [e].

Reserved Notation "e @ i .: n" (at level 50).
(** e @ i :: n says that e is at position i in the network n.
The first position is position 0.*)
Inductive entInNet (e : Entity) : nat -> Network -> Prop :=
  | einConsLeft : forall (n : Network),
    e @ 0 .: (e :: n)
  | einConsRight : forall (i : nat) (e' : Entity) (n : Network),
    e @ i .: n -> e @ (S i) .: (e' :: n)
  where "e @ i .: n" := (entInNet e i n).

(** If an entity is in a network according to the definition of entInNet,
then it is in the list according to In.*)
Theorem entInNet_inList : forall (e : Entity) (n : Network) (i : nat),
  e @ i .: n -> e _: n. intros. induction H. constructor. reflexivity.
  simpl. right. assumption. Qed.

(** If e is at i in n and so is e', then e = e'.*)
Theorem entInNetUnique : forall (e e' : Entity) (i : nat) (n : Network),
  e @ i .: n -> e' @ i .: n -> e = e'. intros. induction H.
  inversion H0. reflexivity. inversion H0. apply IHentInNet. assumption. Qed.

Ltac entnetuniq U e1 e2 :=
  match goal with
  [H1 : e1 @ ?i .: ?n, H2 : e2 @ ?i .: ?n |- _ ] =>
  let U1 := fresh U in lets U1 : entInNetUnique H1 H2
  end.

Ltac entnetuniq2 U n :=
  match goal with
  [H1 : _ @ _ .: n, H2 : _ @ _ .: n |- _ ] =>
  let U1 := fresh U in lets U1 : entInNetUnique H1 H2
  end.

(** There either exists an entity at position i or there doesn't.*)
Theorem decEntInNet : forall (i : nat) (n : Network),
  decidable (exists e, e @ i .: n). unfold decidable.
  intros. generalize dependent i. induction n; intros.
  right. intro. inversion H. inversion H0. destruct i.
  left. exists a. apply einConsLeft. generalize (IHn i); intros; clear IHn.
  inversion H; clear H. inversion H0 as [e He]. left.
  exists e. apply einConsRight. assumption. right. intro.
  inversion H as [e He]. clear H. inversion He. apply H0. exists e.
  assumption. Qed.

Open Scope nat_scope.

(** We define what it means for a network to be safe.*)
Definition safe (n : Network) : Prop := 
  forall (e1 e2 : Entity) (i j : nat), (i < j) ->
  e1 @ i .: n -> e2 @ j .: n -> compatible e1 e2.

(** An alternative definition of safety. The only difference here is that
i <> j rather than i < j.*)
Definition safeAlt (n : Network) : Prop := 
  forall (e1 e2 : Entity) (i j : nat), (i <> j) ->
  e1 @ i .: n -> e2 @ j .: n -> compatible e1 e2.

(** The two definitions of safe are the same.*)
Theorem safeDefsEquiv : forall n : Network,
  safe n <-> safeAlt n. unfold safeAlt; unfold safe; split; intros.
  apply not_eq in H0. inversion H0. apply (H e1 e2 i j); assumption.
  apply compatibleSymmetric. apply (H e2 e1 j i); assumption.
  apply (H e1 e2 i j); try assumption. apply lt_notEq. assumption. Qed.

(** Defining safety for a single entity in a network as follows: e is safe
at i in the network n iff e is at i in n and forall entities e' at j in n
for some j not equal i, e and e' are compatible.*)
Definition safeSing (e : Entity) (i : nat) (n : Network) := 
  e @ i .: n /\
  forall (j : nat) (e' : Entity), j <> i -> e' @ j .: n ->
  e ~~ e'.
Notation "e .! i .: n" := (safeSing e i n) (at level 50, left associativity).

(** A network n is safe iff every entity in the network is singularly
safe.*)
Theorem safeIffSafeSing : forall (n : Network),
  safe n <->
  forall (e : Entity) (i : nat),
  e @ i .: n -> e .! i .: n. intro. unfold safe. unfold safeSing. split; intros.
  split. assumption. intros. apply not_eq in H1. inversion H1. apply compatibleSymmetric.
  apply (H e' e j i); assumption. apply (H e e' i j); assumption. apply H in H2.
  inversion H2. clear H H2. apply lt_notEq in H0. generalize (H4 i e1 H0).
  clear H4. intro. apply compatibleSymmetric. apply H; assumption. Qed.

















































(***************Semantics*********************)

(** A discrete action is either the input, output or ignorance of a message, or
it is the silent value tau. Notice that output actions are indexed by a natural
number- this keeps track of which entity in the network performed the output.*)
Inductive ActDiscNet : Type :=
  | anOut : Message -> nat -> ActDiscNet
  | anIn : Message -> ActDiscNet
  | anIg : Message -> ActDiscNet
  (** The accept relation is essentially the union of the input and output relations. Its purpose is purely to simplify the expression of the semantics.*)
  | anAcc : Message -> ActDiscNet
  | anTau : ActDiscNet.
Notation "b /! i" := (anOut b i) (at level 30).
Notation "b /?" := (anIn b) (at level 30).
Notation "b /:" := (anIg b) (at level 30).
Notation "b /?:" := (anAcc b) (at level 30).



(** Convert an entity action to a network action*)
Coercion entToNetAct (a : ActDiscEnt) : ActDiscNet :=
  match a with
  | aeTagOut m => anOut m 0
  | aeTagIn m => anIn m
  | aeTagIg m => anIg m
  | aeTau => anTau 
  end.

Reserved Notation "n1 -NA- a -NA> n2" (left associativity, at level 50).
Reserved Notation "n1 -ND- d -ND> n2" (left associativity, at level 50).




(** The discrete labelled transition relation on networks.*)
Inductive stepDiscNet : Network -> ActDiscNet -> Network -> Prop :=
  (** The empty network can ignore any value.*)
  | stepDnEmpIg : forall m : Message, [] -NA- m/: -NA> []
  (** For every input, there is a corresponding accept.*)
  | stepDnAccIn : forall (n n' : Network) (m : Message),
    n -NA- m/? -NA> n' -> n -NA- m/?: -NA> n'
  (** For every ignore, there is a corresponding accept.*)
  | stepDnAccIg : forall (n n' : Network) (m : Message),
    n -NA- m/: -NA> n' -> n -NA- m/?: -NA> n'
  | stepDnIgnore : forall (n n' : Network) (e e' : Entity) (m : Message),
    e -EA- m#: ->> e' -> n -NA- m/: -NA> n' ->
    (e :: n) -NA- m/: -NA> (e' :: n')
  | stepDnOutHead : forall (n n' : Network) (e e' : Entity) (m : Message),
    e -EA- m#! ->> e' -> n -NA- m/?: -NA> n' ->
    (e :: n) -NA- m/!0 -NA> (e' :: n')
  | stepDnOutInTail : forall (n n' : Network) (e e' : Entity) (m : Message) (i : nat),
    e -EA- m#? ->> e' -> n -NA- m/!i -NA> n' ->
    (e :: n) -NA- m/!(S i) -NA> (e' :: n')
  | stepDnOutIgTail : forall (n n' : Network) (e e' : Entity) (m : Message) (i : nat),
    e -EA- m#: ->> e' -> n -NA- m/!i -NA> n' ->
    (e :: n) -NA- m/!(S i) -NA> (e' :: n')
  | stepDnInHead : forall (n n' : Network) (e e' : Entity) (m : Message),
    e -EA- m#? ->> e' -> n -NA- m/?: -NA> n' ->
    (e :: n) -NA- m/? -NA> (e' :: n')
  | stepDnInTail : forall (n n' : Network) (e e' : Entity) (m : Message),
    e -EA- m#: ->> e' -> n -NA- m/? -NA> n' ->
    (e :: n) -NA- m/? -NA> (e' :: n')
  | stepDnTauHead : forall (n : Network) (e e' : Entity),
    e -EA- aeTau ->> e' -> (e :: n) -NA- anTau -NA> (e' :: n)
  | stepDnTauTail : forall (n n' : Network) (e : Entity),
    n -NA- anTau -NA> n' -> (e :: n) -NA- anTau -NA> (e :: n')
  where "n1 -NA- a -NA> n2" := (stepDiscNet n1 a n2).

(**An network n is discrete action enabled for the discrete action a iff
there is some derivative network n' such that n transitions to n' via a.*)
Definition discActEnabledNet (n : Network) (a : ActDiscNet) :=
  exists n', n -NA- a -NA> n'.

(** The time-labelled transition relation on networks.*)
Inductive stepTimedNet : Network -> Delay -> Network -> Prop :=
  | stepTnEmp : forall (d : Delay), [] -ND- d -ND> []
  | stepTnCons : forall (n n' : Network) (e e' : Entity) (d : Delay),
    e -ED- d ->> e' -> n -ND- d -ND> n' ->
    (e :: n) -ND- d -ND> (e' :: n')
  where "n1 -ND- d -ND> n2" := (stepTimedNet n1 d n2).







(***************Results*********************)

(** An accept action is always the result of an input or an ignore (as opposed
to say a lift).*)
Lemma accInOrIg : forall (n n' : Network) (m : Message),
  n -NA- m/?: -NA> n' -> (n -NA- m/? -NA> n') \/ (n -NA- m/: -NA> n').
  intros. inversion H. left; assumption. right. assumption. Qed.

Definition emptyNet : Network := [].
Notation "[\]" := emptyNet.

(** Every non-null network is able to accept any message.*)
Theorem accNet : forall (n : Network) (m : Message),
  discActEnabledNet n (m/?:).
  induction n; intros. exists [\]. apply stepDnAccIg. constructor.
  addHyp (inOrIgEnt a m). addHyp (IHn m). clear IHn. invertClear H0.
  rename x into n'. rename a into e.
  invertClear H; invertClear H0; rename x into e'.
  exists (e' :: n'). apply stepDnAccIn. apply stepDnInHead; assumption.
  invertClear H1.
  exists (e' :: n'). apply stepDnAccIn. apply stepDnInTail; assumption.
  exists (e' :: n'). apply stepDnAccIg. apply stepDnIgnore; assumption.
  Qed.

(** The ignore relation preserves networks.*)
Lemma ignoreEqNet : forall (n n' : Network) (m : Message),
  n -NA- m/: -NA> n' -> n = n'. induction n; intros. inversion H.
  reflexivity. inversion H. inversion H3. f_equal. eapply IHn.
  apply H5. Qed.

(** Membership of the singleton network enforces the obvious equality. Also,
the index of the member entity is 0.*)
Lemma entInNetSing : forall (e e' : Entity) (i : nat),
  e @ i .: [e'] -> e = e' /\ i = 0. intros. inversion H. split;
  reflexivity. inversion H2. Qed.

(** If a network ignores a value and there is an entity in the derivative network,
then there was an entity in the original network that also ignores the value.*)
Lemma ignoreLink : forall (n n' : Network) (e : Entity) (i : nat) (m : Message),
  n -NA- m/: -NA> n' -> e @ i .: n' ->
  e @ i .: n /\ e -EA- m#: ->> e. induction n; intros.
  apply ignoreEqNet in H. rewrite <- H in H0. inversion H0.
  invertClear H. rewrite <- H5 in H0. inversion H0.
  addHyp (ignoreEqEnt a e' m H4). rewrite H7. rewrite H7 in H4.
  split. constructor. assumption. addHyp (ignoreEqNet n n'0 m H6).
  rewrite H10. split. constructor. assumption.
  addHyp (IHn n'0 e i0 m H6 H8). invertClear H11. assumption.
  Qed.

(** If a network accepts a value, then the tail of that network accepts the value.*)
Lemma acceptTail : forall (e e' : Entity) (n n' : Network) (m : Message),
  (e :: n) -NA- m/?: -NA> (e' :: n') -> n -NA- m/?: -NA> n'. intros.
  inversion H; inversion H2. assumption. constructor. assumption.
  apply stepDnAccIg. assumption. Qed. 

(** If a network is capable of accepting a message, and there is some entity in
the network, then that entity can either input or ignore the message.*)
Lemma acceptLink : forall (n n' : Network) (e' : Entity) (i : nat) (m : Message),
  n -NA- m/?: -NA> n' -> e' @ i .: n' -> exists e,
  e @ i .: n /\ (e -EA- m#: ->> e' \/ e -EA- m#? ->> e'). induction n; intros.
  inversion H; inversion H3. rewrite <- H7 in H0. inversion H0.
  destruct n'. inversion H0. destruct i.
  (** Case: i is 0, entity is at the head of the list*)
  exists a. split. constructor. invertClear H0. invertClear H;
  inversion H4. right; assumption. left; assumption. left; assumption.
  (** Case: i is not 0, entity is within the smaller list- induct*)
  inversion H0. apply acceptTail in H. addHyp (IHn n' e' i m H H3).
  invertClear H5. invertClear H6. exists x. split. constructor.
  assumption. assumption. Qed.

(** If an network performs an output with index i, then there are entities e and e'
at index i in both the source and derivative networks and e performs the output to
become e'.*)
Lemma outputMatch : forall (n n' : Network) (i : nat) (m : Message),
  n -NA- m/!i -NA> n' -> exists e e',
  e @ i .: n /\ e' @ i .: n' /\ e -EA- m#! ->> e'. induction n; intros.
  inversion H. destruct n'. inversion H. inversion H.
  (** Case: head.*)
  exists a. exists e. split. constructor. split. constructor.
  assumption.
  (** Case: out tail in head.*)
  addHyp (IHn n' i0 m H7). invertClear H8. invertClear H9. invertClear H8.
  invertClear H10. exists x. exists x0. split. constructor. assumption.
  split. constructor. assumption. assumption.
  (** Case: out tail, ig head- the very same as before.*)
  addHyp (IHn n' i0 m H7). invertClear H8. invertClear H9. invertClear H8.
  invertClear H10. exists x. exists x0. split. constructor. assumption.
  split. constructor. assumption. assumption. Qed.

(** If an network performs an output with index i, and there is an entity in the
derivative network at index i', with i <> i', then there is a corresponding entity
at the index i' in the original network, and the two are linked by either an input
or an ignore transition.*)
Lemma outputMismatch : forall (n n' : Network) (e' : Entity) (i i' : nat) (m : Message),
  n -NA- m/!i -NA> n' -> e' @ i' .: n' -> i <> i' -> exists e,
  e @ i' .: n /\ (e -EA- m#? ->> e' \/ e -EA- m#: ->> e'). induction n; intros.
  inversion H. destruct n'. inversion H0. inversion H.
  (** Out head case (haha head-case).*)
  destruct i'. apply False_ind. apply H1. symmetry. assumption.
  inversion H0. addHyp (acceptLink n n' e' i' m H9 H12). invertClear H14.
  invertClear H15. exists x. split. constructor. assumption.
  apply or_comm. assumption.
  (** Out tail, in head case.*)
  inversion H0. exists a. split. constructor. left. assumption.
  assert (i0 <> i1). unfold not. intro. apply H1. rewrite <- H11, <- H6.
  f_equal. assumption. addHyp (IHn n' e' i0 i1 m H9 H12 H14).
  invertClear H15. invertClear H16. exists x. split. constructor.
  assumption. assumption.
  (** Out tail, ig head case- almost the same as before.*)
  inversion H0. exists a. split. constructor. right. assumption.
  assert (i0 <> i1). unfold not. intro. apply H1. rewrite <- H11, <- H6.
  f_equal. assumption. addHyp (IHn n' e' i0 i1 m H9 H12 H14).
  invertClear H15. invertClear H16. exists x. split. constructor.
  assumption. assumption. Qed.

(** If a network outputs a message and there is an entity in the derivative network,
then there is an entity in the same position in the original network and that entity
can either output, input or ignore the same message.*)
Lemma outputLink : forall (n n' : Network) (e' : Entity) (i i' : nat) (m : Message),
  n -NA- m/!i -NA> n' -> e' @ i' .: n' -> exists e,
  e @ i' .: n /\ (e -EA- m#! ->> e' \/ e -EA- m#? ->> e' \/ e -EA- m#: ->> e').
  intros. addHyp (eq_nat_dec i i'). invertClear H1. rewrite H2 in H.
  addHyp (outputMatch n n' i' m H). invertClear H1. invertClear H3.
  exists x. invertClear H1. split. assumption. invertClear H4.
  left. replace e' with x0. assumption. eapply entInNetUnique.
  apply H1. assumption. addHyp (outputMismatch n n' e' i i' m H H0 H2).
  invertClear H1. exists x. invertClear H3. split. assumption.
  right. assumption. Qed.

(** If a network performs a silent action, it is due to exactly one of its component
entities performing a silent action. The rest of the entities remain the same,
unscathed by the muffled action that they cannot see.*)
Lemma tauLink : forall (n n' : Network),
  n -NA- anTau -NA> n' -> exists i e e',
  e @ i .: n /\ e' @ i .: n' /\ e -EA- aeTau ->> e' /\
  (forall (i' : nat) (e1 : Entity), i <> i' -> e1 @ i' .: n' ->
   e1 @ i' .: n). induction n; intros. inversion H.
  destruct n'. inversion H. inversion H. exists 0. exists a. exists e.
  split. constructor. split. constructor. split.
  assumption. intros. inversion H6. apply False_ind.
  apply H5. assumption. constructor. assumption.
  (** Case tau tail*)
  addHyp (IHn n' H3). invertClear H5. invertClear H6. invertClear H5.
  invertClear H6. invertClear H7. rename x into j. exists (S j).
  exists x0. exists x1. split. constructor. assumption. split.
  constructor. assumption. split. invertClear H8.
  assumption. intros. destruct i'. inversion H9. constructor.
  constructor. apply H8. unfold not. intros. apply H7.
  f_equal. assumption. inversion H9. assumption. Qed.

Open Scope R_scope.

(** If an entity evolves by time delay d, then the change in its
position is bounded by d times the assumed maximum speed.*)
Theorem boundedMovement : forall (e e' : Entity) (d : Delay),
  e -ED- d ->> e' -> dist2d e e' <= (d * speedMax). intros.
  destruct e, e'. inversion H. destruct posEnt as [x y].
  destruct delta as [dx dy]. simpl. unfold displacement in H12.
  simpl in H12. rewrite distance_symm. rewrite Rplus_comm.
  replace (y + dy) with (dy + y).
  cut (dist_euc (dx + x) (dy + y) (0 + x) (0 + y) <= d * speedMax).
  repeat rewrite Rplus_0_l. intros. assumption.
  rewrite <- dist_eucAddPres. rewrite Rmult_comm.
  replace (nonneg speedMax * nonneg (time (delToTime d))) with
  (nonneg speedMax * pos (delay d)) in H12. apply H12. destruct d.
  destruct delay. reflexivity. apply Rplus_comm. Qed.

(** The discrete transition relation preserves the position of an entity.*)
Theorem stepDiscPresPos : forall (e e' : Entity) (a : ActDiscEnt),
  e -EA- a ->> e' -> posEnt e = posEnt e'. intros.
  inversion H; destruct a; try solve [inversion H2 | inversion H3 | reflexivity].
  Qed.

(** A discrete action that can be done by an entity can be lifted to
the singleton network.*)
Theorem liftDiscEntNet : forall (e e' : Entity) (a : ActDiscEnt),
  e -EA- a ->> e' -> [e] -NA- a -NA> [e']. intros. destruct a;
  try (constructor; try assumption; try apply stepDnAccIg; constructor).
  Qed.

Lemma link_net_ent_disc_fwd :
  forall (n n' : Network) (e : Entity) (i : nat) (a : ActDiscNet),
  n -NA- a -NA> n' ->
  e @ i .: n ->
  exists e', e' @ i .: n' /\ (e = e' \/ (exists a', e -EA- a' ->> e')). Admitted. (*6*)
(**Proof: Case analyse the network transition and this follows from the semantics*)

Ltac link_netentdiscfwd_tac0 e' U :=
  match goal with
  | [ H : ?n -NA- ?a -NA> ?n', H0 : ?e @ ?i .: ?n |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc_fwd H H0;
    let H2 := fresh in destruct H1 as [e' H2];
    let U1 := fresh U in let H3 := fresh in
    decompAnd2 H2 U1 H3
  end.

Ltac link_netentdiscfwd_tac e' b U :=
  match goal with
  | [ H : ?n -NA- ?a -NA> ?n', H0 : ?e @ ?i .: ?n |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc_fwd H H0;
    let H2 := fresh in destruct H1 as [e' H2];
    let U1 := fresh U in let H3 := fresh in
    decompAnd2 H2 U1 H3; let U2 := fresh U in let H4 := fresh in
    elim_intro H3 U2 H4; 
    [ | let U3 := fresh U in invertClearAs2 H4 b U3]
  end.

(** If a network performs a discrete step to another network, then for all entities
e' in the derivative network, there is an entity e in the original at the same position
as e', and e -a-> e'.*)
Lemma link_net_ent_disc_bkwd : forall (n n' : Network) (e' : Entity) (i : nat) (a : ActDiscNet),
  n -NA- a -NA> n' -> e' @ i .: n' -> exists e, e @ i .: n /\
  (e = e' \/ exists a', e -EA- a' ->> e'). intros.
  destruct a.
  (** Output case.*)
  rename i into i'. rename n0 into i. 
  addHyp (outputLink n n' e' i i' m H H0). invertClear H1. invertClear H2.
  exists x. split. assumption. right. invertClear H3. exists (m#!).
  assumption. invertClear H2. exists (m#?). assumption.
  exists (m#:). assumption.
  (** Input case.*)
  apply stepDnAccIn in H. addHyp (acceptLink n n' e' i m H H0).
  invertClear H1. invertClear H2. exists x. split. assumption.
  right. invertClear H3. exists (m#:). assumption.
  exists (m#?). assumption.
  (** Ignore case- convert to accept and same as last time.*)
  apply stepDnAccIg in H. addHyp (acceptLink n n' e' i m H H0).
  invertClear H1. invertClear H2. exists x. split. assumption.
  right. invertClear H3. exists (m#:). assumption.
  exists (m#?). assumption.
  (** Accept case- same again.*)
  addHyp (acceptLink n n' e' i m H H0). invertClear H1. invertClear H2.
  exists x. split. assumption. right. invertClear H3. exists (m#:).
  assumption. exists (m#?). assumption.
  (** Tau case.*)
  addHyp (tauLink n n' H). invertClear H1. invertClear H2. invertClear H1.
  invertClear H2. invertClear H3. rename x into i'. addHyp (eq_nat_dec i' i).
  invertClear H3. rename x0 into e. exists e. split. rewrite <- H5.
  assumption. right. invertClear H4. replace e' with x1. exists aeTau.
  assumption. eapply entInNetUnique. apply H2. rewrite H5. assumption.
  invertClear H4. addHyp (H6 i e' H5 H0). exists e'. split.
  assumption. left. reflexivity. Qed.

Ltac link_netentdiscbkwd_tac0 e b U :=
  match goal with
  | [ H : ?n -NA- ?a -NA> ?n', H0 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc_bkwd H H0;
    let H2 := fresh in destruct H1 as [e H2];
    let U1 := fresh U in let H3 := fresh in
    decompAnd2 H2 U1 H3
  end.

Ltac link_netentdiscbkwd_tac e b U :=
  match goal with
  | [ H : ?n -NA- ?a -NA> ?n', H0 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_disc_bkwd H H0;
    let H2 := fresh in destruct H1 as [e H2];
    let U1 := fresh U in let H3 := fresh in
    decompAnd2 H2 U1 H3; let U2 := fresh U in let H4 := fresh in
    elim_intro H3 U2 H4; 
    [ | let U3 := fresh U in invertClearAs2 H4 b U3]
  end.

(*Weakend linking theorem*)
Lemma link_net_ent_disc_bkwdW (n n' : Network) (e' : Entity) (i : nat) (a : ActDiscNet) :
  n -NA- a -NA> n' -> e' @ i .: n' -> exists e, e @ i .: n. intros.
  addHyp (link_net_ent_disc_bkwd n n' e' i a H H0). invertClear H1. exists x.
  invertClear H2. assumption. Qed.

(** If a network performs a timed step to another network, then for all entities
e' in the derivative network, there is an entity e in the original at the same position
as e', and e can perform the same timed step to e'.*)
Lemma link_net_ent_del_bkwd : forall (n n' : Network) (e' : Entity) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> e' @ i .: n' -> exists e, e @ i .: n /\ e -ED- d ->> e'.
  induction n; intros; destruct n'; inversion H. inversion H0.
  inversion H0. exists a. split. constructor. assumption.
  addHyp (IHn n' e' i0 d H7 H10). invertClear H12. exists x.
  invertClear H13. split. constructor. assumption. assumption.
  Qed.

Ltac link_netentdelbkwd_tac e U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_del_bkwd H H0;
    let H2 := fresh in destruct H1 as [e H2];
    let U1 := fresh U in let U2 := fresh U in
    decompAnd2 H2 U1 U2
  end.

(** A weakened, but easier to use version of the timed linking theorem.*)
Lemma link_net_ent_delW : forall (n n' : Network) (e e' : Entity) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> e' @ i .: n' -> e @ i .: n -> e -ED- d ->> e'. intros.
  link_netentdelbkwd_tac e0 Y. my_applys_eq Y0. entnetuniq U e0 e. assumption. 
  Qed.

(** If a network performs a timed step to another network, then for all entities
e' in the derivative network, there is an entity e in the original at the same position
as e', and e can perform the same timed step to e'.*)
Lemma link_net_ent_del_fwd : forall (n n' : Network) (e : Entity) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> e @ i .: n -> exists e', e' @ i .: n' /\ e -ED- d ->> e'.
  Admitted. (*7*)
(**Proof: Straightforward from the semantics. Could do induction on the structure of n for the actual proof. Similar to
link_net_ent_disc_fwd but probably simpler.*)

Ltac link_netentdelfwd_tac e' U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : ?e @ ?i .: ?n |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_del_fwd H H0;
    let H2 := fresh in destruct H1 as [e' H2];
    let U1 := fresh U in let U2 := fresh U in
    decompAnd2 H2 U1 U2
  end.

Ltac link_netsoftdel_tac U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : [|?p, ?l, ?h, ?k|] @ ?i .: ?n,
    H1 : [|?p', ?l', ?h', ?k'|] @ ?i .: ?n' |- _] =>
    let U1 := fresh U in lets U1 : link_net_ent_delW H H0 H1;
    apply link_ent_soft_del in U1
  end.

Ltac link_netmstatedel_tac U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : [|?p, ?l, ?h, ?k|] @ ?i .: ?n,
    H1 : [|?p', ?l', ?h', ?k'|] @ ?i .: ?n' |- _] =>
    let U1 := fresh U in lets U1 : link_net_ent_delW H H0 H1;
    apply link_ent_mState_del in U1
  end.

Ltac link_netinterdel_tac U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : [|?p, ?l, ?h, ?k|] @ ?i .: ?n,
    H1 : [|?p', ?l', ?h', ?k'|] @ ?i .: ?n' |- _] =>
    let U1 := fresh U in lets U1 : link_net_ent_delW H H0 H1;
    apply link_ent_inter_del in U1
  end.

(** If a network n delays by d to n', and e1 e2 are separated by x in n,
then e1' e2' are separated by at least x - 2*smax*d in n'. Where e1' e2'
are the derivatives of e1 and e2 respectively.*)
Theorem bndDistLwr :
  forall (n n' : Network) (e1 e2 e1' e2' : Entity) (i j : nat) (d : Delay),
  n -ND- d -ND> n' -> e1 @ i .: n -> e1' @ i .: n' -> e2 @ j .: n -> e2' @ j .: n' ->
  dist2d e1 e2 - (2*d*speedMax) <= dist2d e1' e2'. intros.
  lets H4 : link_net_ent_delW H H1 H0. lets H5 : link_net_ent_delW H H3 H2.
  apply boundedMovement in H4. apply boundedMovement in H5. rewrite Rmult_assoc.
  apply Rplus_le_reg_r with (r := 2 * (d * speedMax)).
  assert (dist2d e1 e2 - 2 * (d * speedMax) + 2 * (d * speedMax) = dist2d e1 e2). ring.
  rewrite H6. destruct d. destruct delay. apply posDiffBound; assumption. Qed.

(** If a network n delays by d to n', and e1 e2 are separated by x in n,
then e1' e2' are separated by at most x + 2*smax*d in n'. Where e1' e2'
are the derivatives of e1 and e2 respectively.*)
Theorem bndDistUpper :
  forall (n n' : Network) (e1 e2 e1' e2' : Entity) (i j : nat) (d : Delay),
  n -ND- d -ND> n' -> e1 @ i .: n -> e1' @ i .: n' -> e2 @ j .: n -> e2' @ j .: n' ->
  dist2d e1' e2' <= dist2d e1 e2 + (2*d*speedMax). intros.
  lets H4 : link_net_ent_delW H H1 H0. lets H5 : link_net_ent_delW H H3 H2.
  apply boundedMovement in H4. apply boundedMovement in H5. rewrite Rmult_assoc.
  destruct d. destruct delay. apply posDiffBound. rewrite distSymmetric.
  assumption. rewrite distSymmetric. assumption. Qed.

Lemma stepNet_tau_pres_pos (n n' : Network) (e e' : Entity) (i : nat) :
  n -NA- anTau -NA> n' -> e @ i .: n -> e' @ i .: n' -> posEnt e = posEnt e'.
  intros. addHyp (tauLink n n' H). decompose [ex] H2. clear H2.
  decompose [and] H3. clear H3. rename x into i'. addHyp (eq_nat_dec i' i).
  invertClear H3. eapply stepEnt_disc_pres_pos. replace e with x0.
  replace e' with x1. eassumption. eapply entInNetUnique. apply H5. rewrite H6.
  assumption. eapply entInNetUnique. apply H2. rewrite H6. assumption.
  addHyp (H7 i e' H6 H1). f_equal. eapply entInNetUnique. apply H0.
  assumption. Qed.

Lemma timeSplit_net n n'' d d' d'' :
  n -ND- d'' -ND> n'' -> d'' = d +d+ d' ->
  exists n', n -ND- d -ND> n' /\ n' -ND- d' -ND> n''. Admitted. (*6*)
(**Proof: Straightforward. Lift time split property for entities. Maybe induction on struct of n.*)