(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)


(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lra.
Require Import ComhCoq.lib.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.lib.GenTacs.
Require Import ComhCoq.lib.StandardResults.
Require Import ComhCoq.lib.GenBasics.
Require Import ComhCoq.model.ComhBasics.
Require Import ComhCoq.lang.LanguageFoundations.
Require Import ComhCoq.lang.SoftwareLanguage.
Require ComhCoq.lang.InterfaceLanguage.
Require ComhCoq.lang.ModeStateLanguage.
Require Export ComhCoq.lang.EntityLanguage.
Reserved Notation "e @ i .: n" (at level 50).
Reserved Notation "n1 -NA- a -NA> n2" (left associativity, at level 50).
Reserved Notation "n1 -ND- d -ND> n2" (left associativity, at level 50).

Section NetworkLanguage.
Context {PNames : ProcNames} {PDefs : ProcDefs} {PGuarded : GuardedDefs}.


(***************Network syntax stuff*********************)

(**A network of entities is a list of entities.*)
Definition Network : Type := list Entity.

Coercion singNet (e : Entity) : Network := [e].

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
  exists e', e' @ i .: n' /\ (e = e' \/ (exists a', e -EA- a' ->> e')).
Proof.
  intros n n' e i a H. revert e i. induction H; intros e0 i0 Hin.
  - inversion Hin.
  - eauto.
  - eauto.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  - inversion Hin; subst.
    + exists e'. split. constructor. right. eauto.
    + exists e0. split. constructor. assumption. left. reflexivity.
  - inversion Hin; subst.
    + eexists. split. constructor. left. reflexivity.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepDiscNet _ _ Hx) as [e1 [He1 Hor]] end.
      exists e1. split. constructor. assumption. assumption.
  Qed.
(**Proof: Case analyse the network transition and this follows from the semantics*)



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


(** A weakened, but easier to use version of the timed linking theorem.*)
Lemma link_net_ent_delW : forall (n n' : Network) (e e' : Entity) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> e' @ i .: n' -> e @ i .: n -> e -ED- d ->> e'.
Proof.
  intros n n' e e' i d D H' H.
  destruct (link_net_ent_del_bkwd n n' e' i d D H') as [e0 [H0 D0]].
  rewrite (entInNetUnique e e0 i n H H0). assumption.
Qed.

(** If a network performs a timed step to another network, then for all entities
e' in the derivative network, there is an entity e in the original at the same position
as e', and e can perform the same timed step to e'.*)
Lemma link_net_ent_del_fwd : forall (n n' : Network) (e : Entity) (i : nat) (d : Delay),
  n -ND- d -ND> n' -> e @ i .: n -> exists e', e' @ i .: n' /\ e -ED- d ->> e'.
Proof.
  intros n n' e i d H. revert e i. induction H; intros e0 i0 Hin.
  - inversion Hin.
  - inversion Hin; subst.
    + exists e'. split. constructor. assumption.
    + match goal with Hx : e0 @ _ .: _ |- _ => destruct (IHstepTimedNet _ _ Hx) as [e1 [He1 Hd]] end.
      exists e1. split. constructor. assumption. assumption.
  Qed.
(**Proof: Straightforward from the semantics. Could do induction on the structure of n for the actual proof. Similar to
link_net_ent_disc_fwd but probably simpler.*)





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
  exists n', n -ND- d -ND> n' /\ n' -ND- d' -ND> n''.
Proof.
  intros H Hd. induction H.
  - exists ([] : Network). split; constructor.
  - destruct (IHstepTimedNet Hd) as [n1 [H1 H2]].
    destruct (timeSplit_ent e e' d d' d0 H Hd) as [e1 [He1 He2]].
    exists (e1 :: n1). split; constructor; assumption.
  Qed.
(**Proof: Straightforward. Lift time split property for entities. Maybe induction on struct of n.*)

(** A network step that is not silent keeps every entity's software component. *)
Lemma stepDiscNet_nonTau_pres_proc (n n' : Network) (a : ActDiscNet) :
  n -NA- a -NA> n' -> a <> anTau ->
  forall (i : nat) (e e' : Entity), e @ i .: n -> e' @ i .: n' -> procEnt e = procEnt e'.
Proof.
  intro STEP. induction STEP; intros NT i0 e0 e0' E0 E0';
  try (exfalso; apply NT; reflexivity);
  try solve [inversion E0];
  try solve [eapply IHSTEP; [discriminate | eassumption | eassumption]];
  inversion E0; subst; inversion E0'; subst;
  try solve [eapply IHSTEP; [discriminate | eassumption | eassumption]];
  match goal with [H : _ -EA- _ ->> _ |- _] => inversion H; subst; reflexivity end.
Qed.

(** A change in an entity's software component across a network step forces the step to be silent. *)
Lemma procNeq_tau_net p p' l l' h h' k k' n n' a i :
  [|p, l, h, k|] @ i .: n -> [|p', l', h', k'|] @ i .: n' ->
  n -NA- a -NA> n' -> p <> p' -> a = anTau.
Proof.
  intros E E' S NE.
  destruct a; try reflexivity; exfalso; apply NE;
  assert (procEnt ([|p, l, h, k|]) = procEnt ([|p', l', h', k'|])) as Q
    by (eapply stepDiscNet_nonTau_pres_proc; [eassumption | discriminate | eassumption | eassumption]);
  simpl in Q; exact Q.
Qed.

(** An index occupied before a discrete step is occupied after it. *)
Lemma link_net_ent_disc_fwd_ex : forall (n n' : Network) (a : ActDiscNet),
  n -NA- a -NA> n' -> forall (e : Entity) (i : nat), e @ i .: n ->
  exists e', e' @ i .: n'.
Proof.
  intros n n' a H e i E.
  destruct (link_net_ent_disc_fwd n n' e i a H E) as [e' [E' _]].
  exists e'. exact E'.
Qed.

(** Across a discrete network step, an entity is either unchanged or steps to its derivative. *)
Lemma link_net_ent_disc :
  forall (n n' : Network) (e e' : Entity) (i : nat) (a : ActDiscNet),
  n -NA- a -NA> n' -> e @ i .: n -> e' @ i .: n'->
  (e = e' \/ (exists a', e -EA- a' ->> e')).
Proof.
  intros n n' e e' i a H H0 H1.
  destruct (link_net_ent_disc_bkwd n n' e' i a H H1) as [e0 [He0 Hor]].
  assert (e0 = e) as Eq by (eapply entInNetUnique; eassumption).
  subst e0. exact Hor.
Qed.

(** A network that delays gives each of its entities a delay. *)
Lemma del_net_ent (e : Entity) (i : nat) (n n' : Network) (d : Delay) :
  e @ i .: n -> n -ND- d -ND> n' -> exists e', e -ED- d ->> e'.
Proof.
  intros E ND.
  destruct (link_net_ent_del_fwd n n' e i d ND E) as [e' [_ S]].
  exists e'. exact S.
Qed.

(** An entity within range of an accepted message inputs it. *)
Lemma inRange_acc_input (n n' : Network) (v : list BaseType) (l : Position)
  (r : Distance) (i : nat) (e : Entity) :
  n -NA- ([-v, l, r-]) /?: -NA> n' -> e @ i .: n -> dist2d l (posEnt e) <= r ->
  exists e', e -EA- ([-v, l, r-]) #? ->> e' /\ e' @ i .: n'.
Proof.
  intros ACC EI DR.
  destruct (link_net_ent_disc_fwd_ex n n' _ ACC e i EI) as [e' EI'].
  destruct (acceptLink n n' e' i ([-v, l, r-]) ACC EI') as [e0 [E0 ST]].
  assert (EQ : e0 = e) by (eapply entInNetUnique; eassumption). subst e0.
  destruct ST as [ST | ST].
  - exfalso. inversion ST; subst. cbn [posEnt] in DR.
    rewrite distSymmetric in DR. lra.
  - exists e'. split; assumption.
Qed.

(** An entity whose current mode changes across a network step has done a silent step. *)
Lemma curr_switch_ent_tau (n n' : Network) (a : ActDiscNet)
  (e e' : Entity) (i : nat) (m m' : Mode) :
  n -NA- a -NA> n' -> e @ i .: n -> e' @ i .: n' ->
  currModeEnt e = m -> currModeEnt e' = m' -> m <> m' ->
  e -EA- aeTau ->> e'.
Proof.
  intros N E E' C C' NE.
  destruct (link_net_ent_disc_bkwd n n' e' i a N E') as [e0 [E0 OR]].
  assert (e0 = e) as EQ0 by (eapply entInNetUnique; eassumption).
  subst e0.
  destruct OR as [EQ | [a' S]].
  - subst. exfalso. apply NE. reflexivity.
  - destruct a'; [ inversion S; subst; simpl in *; exfalso; apply NE; reflexivity .. | exact S ].
Qed.

Import ComhCoq.lang.InterfaceLanguage.
Import ComhCoq.lang.ModeStateLanguage.

(** When a network delays, the entity at index i becomes one whose components have each
delayed by the same amount, and which has moved at most as far as the maximum speed
allows.*)
Lemma net_del_elim p l h k i n n' d :
  [|p, l, h, k|] @ i .: n ->
  n -ND- d -ND> n' ->
  exists p' l' h' k',
  [|p', l', h', k'|] @ i .: n' /\
  p -PD- d -PD> p' /\ h -i- d -i> h' /\ k -ms- d -ms> k' /\
  dist2d l l' <= speedMax * d.
Proof.
  intros E ND.
  destruct (link_net_ent_del_fwd n n' _ i d ND E) as [e' [E' S]].
  lets BM : boundedMovement S.
  inversion S; subst.
  do 4 eexists. split; [eassumption | ].
  split; [eassumption | ]. split; [eassumption | ]. split; [eassumption | ].
  simpl in BM. rewrite Rmult_comm. exact BM.
Qed.


(***************Positions, queues and mode states of a network's entities*********************)

(** inPosNet l i n says that the entity number i in n has position l.*)
Inductive inPosNet (l : Position) (i : nat) (n : Network) : Prop :=
  | ipWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
    [| p , l , h , k |] @ i .: n -> inPosNet l i n.

(** distNet i i' n x says that the entities i and i' are separated by x in n.*)
Inductive distNet (i i' : nat) (n : Network) : Distance -> Prop :=
  | dnWitness (l l' : Position) : inPosNet l i n -> inPosNet l' i' n ->
    distNet i i' n (distFun l l').

(** outgoing v t i n says that the message v with timestamp t is in the output queue of
the interface component of the entity i in the network n.*)
Inductive outgoing (v : list BaseType) (t : Time) (i : nat) (n : Network) : Prop :=
  | ogWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , t )>) (outList lo) -> outgoing v t i n.

(** incomingNet v i n says that the message v is in the input queue of the interface
component of the entity i in the network n. Even though the input queue is effectively
untimed messages, it is modelled as a timed list, with timestamps simply set to 0, hence
"v in Li" becomes "<v, 0> in Li" to be more pedantic about it.*)
Inductive incomingNet (v : list BaseType) (i : nat) (n : Network) : Prop :=
  | icWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , zeroTime )>) (inList li) -> incomingNet v i n.

(** incomingNetNotif v t i n says that the message v with timestamp t is in the
notification queue of the interface component of the entity i in the network n.*)
Inductive incomingNetNotif (v : list BaseType) (t : Time) (i : nat) (n : Network) : Prop :=
  | icnWitness (p : ProcTerm) (l : Position) (li : InputList) (lo : OutputList) (ln : NotifList) (k : ModeState) :
    [| p , l , (mkInterface li lo ln) , k |] @ i .: n -> In (<( v , t )>) (notifList ln) -> incomingNetNotif v t i n.

(** mState_in_net k i n says that the entity number i in n has mode state k.*)
Inductive mState_in_net (k : ModeState) (i : nat) (n : Network) : Prop :=
  minet (p : ProcTerm) (l : Position) (h : Interface) :
  [|p, l, h, k|] @ i .: n -> mState_in_net k i n.

(** transGuard t i n says that the entity at position i in n is transitioning
from one mode to another and the guard on the transition is t.*)
Inductive transGuard (t : Time) (i : nat) (n : Network) : Prop :=
  | tgWitness (p : ProcTerm) (l : Position) (h : Interface) (m m' : Mode) :
    [| p , l , h , <| m , m' , t |> |] @ i .: n -> transGuard t i n.

(** The lifting function we use to lift predicates from the entity level to the
network level.*)
Inductive liftEntNet (X : Entity -> Prop) (i : nat) (n : Network) : Prop :=
  | lenWitness (e : Entity) : X e -> e @ i .: n -> liftEntNet X i n.

(** If the entity i is in position l in either network across a discrete transition,
then it is also in this position in the other network.*)
Theorem inPos_pres_disc (n n' : Network) (a : ActDiscNet) (l : Position) (i : nat) :
  n -NA- a -NA> n' ->
  (inPosNet l i n <-> inPosNet l i n').
Proof.
  intros ST. split; intros IP; destruct IP as [p h k E].
  - destruct (link_net_ent_disc_fwd _ _ _ _ _ ST E) as [e' [E' [EQ | [b S]]]].
    + subst. econstructor; eassumption.
    + inversion S; subst; econstructor; eassumption.
  - destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST E) as [e [E0 [EQ | [b S]]]].
    + subst. econstructor; eassumption.
    + inversion S; subst; econstructor; eassumption.
Qed.
(**Proof: Follows directly from the entity semantics*)

(** If v is outgoing with timestamp t, and the network can delay, then in
the derivative network v is outgoing with timestamp t - d.
A useful corollary of this is that if t = 0, then delay is impossible.*)
Theorem outgoing_del (n n' : Network) (d : Delay) (v : list BaseType) (t : Time) (i : nat) :
  n -ND- d -ND> n' -> outgoing v t i n ->
  {p : d <= t | outgoing v (minusTime t d p) i n'}.
Proof.
  intros ND OG. destruct OG as [p l li lo ln k EIN INO].
  destruct (link_net_ent_del_fwd _ _ _ _ _ ND EIN) as [e' [Y Y0]].
  destr_ent_inter e' p' l' k' li' lo' ln'.
  lets Y1 : link_ent_inter_del Y0.
  inversion Y1 as [? ? ? ? ? ? ? IL OL NL | | | | | ]; subst.
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
  (v : list BaseType) (i : nat) : n -ND- d -ND> n' ->  outgoing v zeroTime i n -> False.
Proof.
  intros. addHyp (outgoing_del n n' d v zeroTime i H H0). invertClear H1.
  eapply Rle_not_lt. apply x. simpl. delPos.
Qed.

(** If v is outgoing with non-zero timestamp t, and the network performs a
discrete action, then v is still outgoing in the derivative network.*)
Theorem outgoing_disc_pres (n n' : Network) (a : ActDiscNet) (v : list BaseType) (t : Time) (i : nat) :
  n -NA- a -NA> n' -> outgoing v t i n -> 0 < t ->
  outgoing v t i n'.
Proof.
  intros ST OG POS. destruct OG as [p l li lo ln k EIN INO].
  destruct (link_net_ent_disc_fwd _ _ _ _ _ ST EIN) as [e' [EIN' [EQ | [b S]]]].
  - subst. econstructor; eassumption.
  - destr_ent_inter e' p' l' k' li' lo' ln'.
    econstructor. eassumption.
    eapply stepEnt_disc_pres_out_pos; eassumption.
Qed.

(** If v is incomingNetNotif with non-zero timestamp t, and the network performs a discrete
action, then v is still incomingNetNotif in the derivative network.*)
Theorem incomingNetNotif_disc_pres (n n' : Network) (a : ActDiscNet) (v : list BaseType) (t : Time) (i : nat) :
  n -NA- a -NA> n' -> incomingNetNotif v t i n -> 0 < t ->
  incomingNetNotif v t i n'.
Proof.
  intros ST IN POS. destruct IN as [p l li lo ln k EIN INN].
  destruct (link_net_ent_disc_fwd _ _ _ _ _ ST EIN) as [e' [EIN' [EQ | [b S]]]].
  - subst. econstructor; eassumption.
  - destr_ent_inter e' p' l' k' li' lo' ln'.
    econstructor. eassumption.
    eapply stepEnt_disc_pres_notif_pos; eassumption.
Qed.
(**Proof: Analogous to (outgoing_disc_pres).*)

(** If an entity is inPosNet l' i n', and there is some n such that it delays to n' via d,
then i is in inPosNet l i n for some l and the difference between the positions is at most
speedMax*d*)
Lemma inPos_del_bound_bkwd (n n' : Network) (d : Delay) (l' : Position) (i : nat) :
  inPosNet l' i n' -> n -ND- d -ND> n' -> exists l,
  inPosNet l i n /\ dist2d l l' <= speedMax * d.
Proof.
  intros IP ND. destruct IP as [p h k EIN].
  destruct (link_net_ent_del_bkwd _ _ _ _ _ ND EIN) as [e [Y Y0]].
  lets BM : boundedMovement Y0.
  destruct e as [p0 l0 h0 k0]. exists l0. split.
  - econstructor. eassumption.
  - simpl in BM. rewrite Rmult_comm. destruct d as [[dr dp]]. simpl in *. exact BM.
Qed.
(**Proof: Salvaged from old Coq model (pos_bound?).*)

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

(** Any entity within range of a broadcast inputs that broadcast.*)
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

Lemma mState_in_net_unique k k' i n :
  mState_in_net k i n -> mState_in_net k' i n -> k = k'.
Proof.
  intros MS MS'. destruct MS as [p l h E]. destruct MS' as [p' l' h' E'].
  lets EN : entInNetUnique E E'. inversion EN. reflexivity.
Qed.

Lemma inPos_unique : forall (l l' : Position) (i : nat) (n : Network),
  inPosNet l i n -> inPosNet l' i n -> l = l'.
Proof.
  intros l l' i n H H0. destruct H as [p h k E]. destruct H0 as [p0 h0 k0 E0].
  lets EQ : entInNetUnique E E0. inversion EQ. reflexivity.
Qed.
(**Proof: Obvious- inversion and apply entInNetUnique*)

(** An output by entity i from the network n means that the message is now pending
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
  incomingNet v i n -> exists e, incomingEnt v e /\ e @ i .: n.
Proof.
  intro U. invertClear U. exists ([|p, l, {| li := li; lo := lo; ln := ln |}, k|]).
  split. repeat constructor. assumption. assumption.
Qed.

(** Linking theorem.*)
Lemma incoming_ent_net (v : list BaseType) (e : Entity) (i : nat) (n : Network) :
  incomingEnt v e -> e @ i .: n -> incomingNet v i n.
Proof.
  intros U E. destruct U as [p l h k IH]. destruct h as [li lo ln].
  inversion IH; subst. econstructor; eassumption.
Qed.
(**Proof: Follows directly from the definition*)

End NetworkLanguage.

(** A section's notations and tactics end with it. So that later files can use them, the
notations are declared again here, and the tactics are declared here.*)
Notation "e @ i .: n" := (entInNet e i n).
Notation "e .! i .: n" := (safeSing e i n) (at level 50, left associativity).
Notation "b /! i" := (anOut b i) (at level 30).
Notation "b /?" := (anIn b) (at level 30).
Notation "b /:" := (anIg b) (at level 30).
Notation "b /?:" := (anAcc b) (at level 30).
Notation "n1 -NA- a -NA> n2" := (stepDiscNet n1 a n2).
Notation "n1 -ND- d -ND> n2" := (stepTimedNet n1 d n2).
Notation "[\]" := emptyNet.

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

Ltac link_netentdelbkwd_tac e U :=
  match goal with
  | [ H : ?n -ND- ?d -ND> ?n', H0 : ?e' @ ?i .: ?n' |- _] =>
    let H1 := fresh in lets H1 : link_net_ent_del_bkwd H H0;
    let H2 := fresh in destruct H1 as [e H2];
    let U1 := fresh U in let U2 := fresh U in
    decompAnd2 H2 U1 U2
  end.

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

Ltac inposdp :=
  match goal with
  [ w : ?n -NA- _ -NA> ?n', H : inPosNet ?l ?i ?n' |- inPosNet ?l ?i ?n] =>
  eapply inPos_pres_disc; [apply w | assumption]
  end.
