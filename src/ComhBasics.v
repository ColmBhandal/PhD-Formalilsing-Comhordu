(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** Various constants relating to the comhordu model are assumed here. Also some basic notions
are defined here such as the notion of a network of entities.*)

Require Import ComhCoq.Extras.LibTactics.
Require Import Fourier_util.

(*********Imports********)
Require Export List.
(**Notations stolen from tutorial.*)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "e _: n" := (In e n) (at level 60).
Require Export Logic.Decidable.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ListSet.


(*********Basic Stuff********)

Definition toNonneg (r : posreal) : nonnegreal :=
  let h := (Rlt_le 0 r (cond_pos r)) in
  mknonnegreal r h.

(** A time value is a non negative real number.*)
Record Time := mkTime {time :> nonnegreal}.

Definition zeroTime : Time := mkTime zeroNonneg.

(**Solves the goal 0 <= u where u is some time.*)
Ltac timeNonneg := 
  match goal with
  | [ |- 0 <= (nonneg (time ?t))] => unwrap2_apply2 t
  | [ |- (nonneg (time zeroTime)) <= (nonneg (time ?t))] => simpl;unwrap2_apply2 t
  end.

(** A delay is a positive real number.*)
Record Delay := mkDelay {delay :> posreal}.

(**Solves the goal 0 < u where u is some delay.*)
Ltac delPos :=
  match goal with
  | [ |- 0 < (pos (delay ?d))] => unwrap2_apply2 d
  | [ |- (nonneg (time zeroTime)) < (pos (delay ?d))] => simpl;unwrap2_apply2 d
  end.

(** We can coerce a delay to be a time.*)
Coercion delToTime (d : Delay) : Time :=
  match d with mkDelay d0 =>
    mkTime d0 end.

(** A distance is a non negative real number*)
Record Distance := mkDistance {distance :> nonnegreal}.

Ltac foldDist l l0 H := replace (dist_euc (xCoord l) (yCoord l) (xCoord l0) (yCoord l0)) with
  (nonneg (dist2d l l0)) in H;[ | simpl;ring].

Definition distFun p1 p2 := mkDistance (dist2d p1 p2).

Lemma timeEqNonneg : forall (t1 t2 : Time), (time t1) = (time t2) -> t1 = t2.
  destruct t1, t2. simpl. intros. f_equal. assumption. Qed.

Lemma timeEqR : forall (t1 t2 : Time), (nonneg (time t1)) = (nonneg (time t2)) ->
  t1 = t2. intros. apply timeEqNonneg. apply nonnegRealEqR. assumption. Qed.

Lemma delayEqPos : forall (d1 d2 : Delay), delay d1 = delay d2 -> d1 = d2.
  destruct d1, d2. simpl. intros. f_equal. apply H. Qed.

Lemma delayEqR : forall (d1 d2 : Delay), pos d1 = pos d2 -> d1 = d2.
  intros. apply delayEqPos. apply posRealEqR. assumption. Qed.

Open Scope nat_scope.

Lemma lt_notEq : forall (n m : nat),
  n < m -> n <> m. intros. unfold not; intros.
  rewrite H0 in H. apply lt_irrefl in H. assumption. Qed.

(** Converts a decidable proposition to a boolean.*)
Definition decToBool {P : Prop} (p : {P} + {~P}) : bool :=
  match p with
  | left _ => true
  | right _ => false
  end.
   
(** Converts a decidable relation to a boolean.*)
Definition decToOption {P : Prop} (p : {P} + {~P}) : option P :=
  match p with
  | left P => Some P
  | right _ => None
  end.

Lemma lt_plus_r (m n : nat) :
  0 < n -> m < m + n. intros. apply le_lt_trans with (m := m + 0).
  replace (m + 0) with m. apply le_refl. ring.
  apply plus_le_lt_compat. apply le_refl. assumption. Qed.

Lemma lt_plus_l (m n : nat) :
  0 < n -> m < n + m. intros. rewrite plus_comm. apply lt_plus_r.
  assumption. Qed.

Lemma le_plus_r (m n : nat) :
  m <= m + n. intros. apply le_trans with (m := m + 0).
  replace (m + 0) with m. apply le_refl. ring.
  apply plus_le_compat. apply le_refl. apply le_0_n. Qed.

Lemma le_plus_l (m n : nat) :
  m <= n + m. intros. rewrite plus_comm. apply le_plus_r. Qed.

Open Scope R_scope.

(** inAtList a i l says that a is at position i in the list l.
The first position is position 0.*)
Inductive inAtList {A : Type} (a : A) : nat -> list A -> Prop :=
  | inatlFst (l : list A) :
    inAtList a 0 (a :: l)
  | inatlCons (i : nat) (a' : A) (l : list A) :
    inAtList a i l -> inAtList a (S i) (a' :: l).

Notation "a -@ i -: l" := (inAtList a i l) (at level 50).

(** If an element is in a list according to the definition of inAtList,
then it is in the list according to In.*)
Theorem inAtList_inList (A : Type) (a : A) (l : list A) (i : nat) :
  a -@ i -: l -> a _: l. intros. induction H. constructor. reflexivity.
  simpl. right. assumption. Qed.

(** If a is at i in l and so is a', then a = a'.*)
Theorem inAtListUnique (A : Type) (a a' : A) (i : nat) (l : list A) :
  a -@ i -: l -> a' -@ i -: l -> a = a'. intros. induction H.
  inversion H0. reflexivity. inversion H0. apply IHinAtList. assumption. Qed.

(** There either exists an element at position i or there doesn't.*)
Theorem decInAtList (A : Type) (i : nat) (l : list A) :
  decidable (exists a, a -@ i -: l). unfold decidable.
  intros. generalize dependent i. induction l; intros.
  right. intro. inversion H. inversion H0. destruct i.
  left. exists a. constructor. addHyp (IHl i).
  inversion H; clear H. inversion H0 as [e He]. left.
  exists e. apply inatlCons. assumption. right. intro.
  inversion H as [e He]. clear H. inversion He. apply H0. exists e.
  assumption. Qed.

(**Equality is decidable for times.*)
Lemma eqDecTime : eqDec Time. unfold eqDec. destruct x1, x2.
  generalize (eqDecNonnegReal time0 time1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

(** Equality is decidable on Delays.*)
Lemma eqDecDelay : eqDec Delay. unfold eqDec. destruct x1, x2.
  generalize (eqDecPosReal delay0 delay1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

Lemma eqDecDistance : eqDec Distance. unfold eqDec. destruct x1, x2.
  generalize (eqDecNonnegReal distance0 distance1). intros. inversion H.
  left. f_equal. assumption. right. unfold not; intros. apply H0.
  inversion H1. reflexivity. Qed.

(**Returns t1 - t2, or None if t1 < t2.*)
Definition subtractTime (t1 t2 : Time) : option Time :=
  let r1 := nonneg t1 in let r2 := nonneg t2 in
  match total_order_T r1 r2 with
  | inleft _ => None
  | inright H => Some (mkTime (mknonnegreal (r1 - r2)
    (Rlt_le 0 (r1 - r2) (RltMinusBothSides r1 r2 H))))
  end.

Definition addTime (t1 t2 : Time) : Time :=
  let r1 := nonneg t1 in let r2 := nonneg t2 in
  mkTime (mknonnegreal (r1 + r2) (Rle_zero_plus r1 r2 (cond_nonneg t1) (cond_nonneg t2))).

(** Add two delays together to get a third delay.*)
Definition addDelay (d1 d2 : Delay) : Delay :=
  let r1 := pos d1 in let r2 := pos d2 in
  mkDelay (mkposreal (r1 + r2) (Rlt_zero_plus r1 r2 (cond_pos d1) (cond_pos d2))).

(** Add a delay to a time to get a delay.*)
Definition addDelayTime (t : Time) (d : Delay) : Delay :=
  let r1 := nonneg t in let r2 := pos d in
  mkDelay (mkposreal (r1 + r2) (Rplus_le_lt_0_compat r1 r2 (cond_nonneg t) (cond_pos d))).

Notation "t +dt+ d" := (addDelayTime t d) (at level 45).
Notation "d +d+ d'" := (addDelay d d') (at level 45).

Lemma addDelayComm : forall (d d' : Delay), d +d+ d' = d' +d+ d.
  destruct d, d'. unfold addDelay. repeat f_equal.
  apply posRealEqR. simpl. apply Rplus_comm. Qed.

(**If there is some delays d and d', and they are being
added with the left one as a time, then they can be added as normal.*)
Lemma timeDelAddSwitch : forall (d d' : Delay),
  d +dt+ d' = d +d+ d'. intros. unfold addDelayTime.
  unfold addDelay. f_equal. apply posRealEqR. simpl.
  destruct d. destruct delay0. reflexivity. Qed.

Lemma delTimeAddAssoc : forall (t : Time) (d d' : Delay),
  t +dt+ d +dt+ d' = t +dt+ (d +dt+ d'). intros.
  destruct t, d, d'. destruct time0, delay0, delay1.
  unfold addDelayTime. simpl. repeat f_equal.
  apply posRealEqR. simpl. apply Rplus_assoc. Qed.

Lemma delTimeAddAssoc2 : forall (t : Time) (d d' : Delay),
  (t +dt+ d) +d+ d' = t +dt+ (d +d+ d'). intros.
  repeat rewrite <- timeDelAddSwitch. apply delTimeAddAssoc. Qed.

Lemma timeDelAddZeroL : forall (d : Delay),
  zeroTime +dt+ d = d. unfold zeroTime. destruct d.
  unfold addDelayTime. f_equal. apply posRealEqR.
  simpl. ring. Qed.

(** If a delay d is less than or equal a time t,
then there is some time t' such that t = t' + d.*)
Lemma delLeTimeSum : forall (t : Time) (d : Delay),
  d <= t -> exists t', t = t' +dt+ d. intros.
  assert (exists r, nonneg (time t) = d + r /\ 0 <= r).
  exists (t - d). split. ring. replace 0 with (t - t).
  apply Rplus_le_compat. apply Rle_refl.
  apply Ropp_le_contravar. assumption. ring.
  invertClear H0. invertClear H1.
  exists (mkTime (mknonnegreal x H2)). destruct t, d.
  apply timeEqR. simpl. rewrite Rplus_comm. apply H0.
  Qed.

(** Subtract d2 from d1. Requires a proof that d2 is indeed less than d1 so
that the result is a delay.*)
Definition minusDelay (r1 r2 : R) (p : r2 < r1) : Delay :=
   mkDelay (mkposreal (r1 - r2) (Rgt_minus r1 r2 (Rlt_gt r2 r1 p))).

(** Subtracting and then adding the same delay gives the same result.*)
Lemma minusAddDelay : forall (d1 d2 : Delay) (p : d2 < d1),
  (minusDelay d1 d2 p) +d+ d2 = d1. intros. apply delayEqR. simpl. ring. Qed.

(** Adding a time that has been subtracted gives back the original result.*)
Lemma minusDelayAddTime : forall (d : Delay) (t : Time) (p : t < d),
  d = t +dt+ (minusDelay d t p). intros. apply delayEqR. simpl. ring. Qed.

(**The right summand in a sum of delays is less than the total sum.*)
Lemma addDelayLtR : forall (d1 d2 : Delay),
  d2 < d1 +d+ d2. destruct d1, d2. destruct delay0, delay1.
  simpl. rewrite <- Rplus_comm. cut (pos0 + 0 < pos0 + pos).
  rewrite Rplus_0_r. intros. assumption. apply Rplus_lt_compat_l.
  assumption. Qed.

(** Adding and then subtracting the same quantity leaves the original delay.*)
Lemma addMinusDelay : forall (d1 d2 : Delay),
  exists p, minusDelay (d1 +d+ d2) d2 p = d1.
  intros. exists (addDelayLtR d1 d2). destruct d1, d2.
  destruct delay0, delay1. apply delayEqR. simpl. ring. Qed.

(** Communtativity of times in a sum of three terms.*)
Lemma timeDelAddComm : forall (t1 t2 : Time) (d : Delay),
  t1 +dt+ (t2 +dt+ d) = t2 +dt+ (t1 +dt+ d). intros.
  apply delayEqR. simpl. ring. Qed.

(**Subtract R2 from R1. Requires a proof that R2 is indeed less
than or equal r1 so that the result is a Time.*)
Definition minusTime (r1 r2 : R) (p : r2 <= r1) : Time :=
   mkTime (mknonnegreal (r1 - r2) (Rge_le (r1 - r2) 0
   (Rge_minus r1 r2 (Rle_ge r2 r1 p)))).

(** To show that d = d +d+ d' according to the addDel function, it suffices to show that
d = d + d' i.e. that the real parts and real number addition equates.*)
Lemma addRaddDel : forall (d d' d'' : Delay),
  pos d = d' + d'' -> d = d' +d+ d''. intros.
  apply delayEqR. simpl. apply H. Qed.

(** Every delay has two delays that add up to make it.*)
Theorem addDelayExists : forall (d : Delay),
  exists d1 d2, d = d1 +d+ d2. intros.
  destruct d as [r]. addHyp (addPosRealExists r). invertClear H.
  invertClear H0. exists (mkDelay x). exists (mkDelay x0).
  apply addRaddDel. apply H. Qed.

Lemma RMax_time (t1 t2 : Time) : 0 <= Rmax t1 t2.
  eapply Rle_trans;[ |apply Rmax_l]. timeNonneg. Qed.
  
(*Returns the maximum of two times.*)
Definition timeMax (t1 t2 : Time) : Time :=
  mkTime (mknonnegreal (Rmax t1 t2) (RMax_time t1 t2)).
 
(*The timeMax function is correct.*)
Lemma timeMax_RMax : forall (t1 t2 : Time), nonneg (timeMax t1 t2) = Rmax t1 t2.
  intros. reflexivity. Qed.
Notation "t1 +t+ t2" := (addTime t1 t2) (at level 50).

(** Given time t, splits goal into two subgoals based on whether 0 = t or 0 < t*)
Ltac timezerolteq t U := let H := fresh in assert (0 <= t) as H;[timeNonneg| ];
  apply Rle_lt_or_eq_dec in H; let U1 := fresh U in elim_intro H U1 U1.

Ltac mkdel t Q d' := remember (mkDelay (mkposreal t Q)) as d'.


























(*********Comh Related Stuff********)

(** The time it takes for an entity to be notified of a message delivery area.*)
Axiom adaptNotif : Time.

(** The time between initiating the sending of a message and its actual delivery.*)
Axiom msgLatency : Time.

(**We assume a maximum speed at which entities may travel.*)
Axiom speedMax : nonnegreal.

(** The set of all modes.*)
Axiom Mode : Type.

(** A subset of the modes are fail safe.*)
Axiom failSafe : Mode -> Prop.

(** A mode is either fail safe or it isn't.*)
Axiom fsDecMode : forall (m : Mode), decidable (failSafe m).

(** Equality on modes is decidable.*)
Axiom eqDecMode : eqDec Mode.

(** The mode transition relation, which says whether one mode can transition
to another or not.*)
Axiom modeTransRel : Mode -> Mode -> Prop.
Notation "m1 -mtr-> m2" := (modeTransRel m1 m2) (at level 39).

(** The mode transition relation is assumed to be decidable.*)
Axiom modeTransRelDec : forall (m1 m2 : Mode),
  {m1 -mtr-> m2} + {~m1 -mtr-> m2}.

(** Mode transition relation as a boolean function.*)
Definition modeTransRelBool (m1 m2 : Mode) : bool :=
  decToBool (modeTransRelDec m1 m2).

(** Mode transition relation as an option type*)
Definition modeTransRelOpt (m1 m2 : Mode) : option (m1 -mtr-> m2) :=
  decToOption (modeTransRelDec m1 m2).

(** modeTransTime m1 m2 gives the time it takes to transition from
m1 to m2. Note that this function takes two modes and a proof that one
transitions to the other and then returns the transition time.*)
Axiom modeTransTime : forall (m1 m2 : Mode),
  m1 -mtr-> m2 -> Time.

(** We assume that every mode transitions to some fail safe mode,
and this function simply arbitrarily picks one such fail safe mode.*)
Axiom failSafeSucc : Mode -> Mode.

(** This is the assumption that failSafeSucc m is indeed fail safe for all m.*)
Axiom failSafeSuccFS : forall (m : Mode), failSafe (failSafeSucc m).

(*The fail safe successor is actually a successor.*)
Axiom failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m.

(** trans m is the worst case time it takes for an entity in a mode m
to reach a failsafe mode.*)
Axiom trans : Mode -> Time.

(** An upper bound on trans m over all m: transMax is an upper bound on
the time it takes any entity to reach a failsafe mode.*)
Axiom transMax : Time.

(**A little extra positive time that ensures we wait beyond the boundary*)
Axiom waitSurplus : Delay.

(** The wait time between two modes m1 and m2 is the maximum between two different
values. The first is the mode transition time, denoting the physical time it takes
to transition from one mode to another. The second value ensures that the wait time
is to sufficient to ensure surrounding entities are warned. As such, it incorporates
the term msgLatency to allow the initial message to be delivered, transMax for the
receiving entities to react, adaptNotif for the sender to be notified of the coverage,
and finally some positive waitSurplus to ensure that the message delivery, reaction and
notification have definitely happened in the past- without the surplus it might be possible
for these events to be about to happen this instant but they might not have happened yet.*)
Definition waitTime (m1 m2 : Mode) (p : m1 -mtr-> m2) : Time :=
  timeMax (modeTransTime m1 m2 p)
  (msgLatency +t+ (timeMax adaptNotif transMax) +t+ waitSurplus).

Open Scope R_scope.

(** transMax is an upper bound on trans m for all m.*)
Axiom transMaxBound : forall m : Mode,
  trans m <= transMax.

(** The minimum distance of compatibiltiy function is assumed to exist.
It tells us the minimum distance by which two modes must be separated in
order for them to be compatible. If two entities in these modes are
separated by a distance greater than or equal to this distance,
then they are compatible.*)
Axiom minDistComp : Mode -> Mode -> Distance.

(** The minimum distance of compatibility function is symmetric.*)
Axiom minDistCompSymmetric : forall (m1 m2 : Mode),
  minDistComp m1 m2 = minDistComp m2 m1.

(** For a given mode m, maxMinDistComp m is an upper bound on the set
minDistComp m m' taken over all other modes m'. We do not enforce that this
is the least such upper bound, though this would be the sensible interpretation.*)
Axiom maxMinDistComp : Mode -> Distance.

(** The maxMinDistComp is an upper bound on the minDistComp for all other modes*)
Axiom maxMinDistCompBound : forall m m' : Mode,
  minDistComp m m' <= maxMinDistComp m.

(** The minimum distance of compatibility function returns 0 if either
of its arguments are fail safe. Note we only choose the left argument here,
but the choice is irrelevant since the function is symmetric.*)
Axiom minDistCompFS : forall (m1 m2 : Mode),
  failSafe m1 -> minDistComp m1 m2 = (mkDistance zeroNonneg).

(** period m is the time between successive broadcasts from an entity in mode m.*)
Axiom period : Mode -> Time.

Axiom msgLatency_positive : 0 < msgLatency.

Axiom period_positive : forall m : Mode, 0 < period m.

(** To rule out a trivial system, we assume the maximum speed is above 0.*)
Axiom speedMax_pos: 0 < speedMax.

Lemma speedMax_nonneg : 0 <= speedMax.
  (*Proof: follows from speedMax_pos*)
  apply Rlt_le. apply speedMax_pos. Qed.

Axiom adaptNotif_positive : 0 < adaptNotif.

Axiom modeTransTime_bound : forall (m m' : Mode) (p : m -mtr-> m'),
  modeTransTime m m' p <= trans m.

Ltac timering := apply timeEqR; simpl; ring.

(** The coverage r is sufficient for an entity broadcasting in mode m.*)
Definition sufficient (m : Mode) (r : Distance) : Prop :=
  maxMinDistComp m +
  2 * speedMax * (Rmax adaptNotif transMax + period m + trans m) <= r.

(** The sufficient predicate is decidable.*)
Lemma suffDec : forall (m : Mode) (r : Distance),
  {sufficient m r} + {~sufficient m r}. intros. apply Rle_dec. Qed.

(** A version of the sufficient Prop that gives a bool as a result.*)
Definition suffBool (m : Mode) (r : Distance) : bool :=
  if suffDec m r then true else false.

(** The possibly incompatible distance for modes m and m' is the distance
beneath which an entity in mode m must consider mode m' messages from other entities
as potential threats.*)
Definition possIncDist (m m' : Mode) : R :=
  minDistComp m m' + 2 * speedMax * (Rmax adaptNotif transMax + period m' + trans m').

(** possiblyIncompatible m m' r means that if e and e' in m and m'
respectively are separated by r, then e' should begin to transition to a
fail safe mode if it has not already done so.*)
Definition possiblyIncompatible (m m' : Mode) (r : R) :=
  r < possIncDist m m'.

Lemma possIncDec : forall (m m' : Mode) (r : Distance),
  {possiblyIncompatible m m' r} + {~possiblyIncompatible m m' r}. intros.
  apply Rlt_dec. Qed.

(** A version of the possiblyIncompatible Prop that gives a bool as a result.*)
Definition possIncBool (m m' : Mode) (r : Distance) : bool :=
  if possIncDec m m' r then true else false.


(** If m m' r are possibly incompatible, r' is a sufficient coverage for m, then
r <= r'.*)
Theorem possIncSuff : forall (m m' : Mode) (r r' : Distance),
  possiblyIncompatible m m' r -> sufficient m' r' -> r < r'.
  unfold possiblyIncompatible, sufficient. intros.
  eapply Rlt_le_trans. apply H. eapply Rle_trans; try apply H0.
  apply Rplus_le_compat. rewrite minDistCompSymmetric.
  apply maxMinDistCompBound. apply Rle_refl. Qed.

Open Scope nat_scope.

(********* More Stuff ********)


Open Scope nat_scope.

(**If a property p is true of the number j, and j <= k, then there is some
largest j' between j and k such that p is true at j'.*)
Theorem rightmost : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p j -> j <= k ->
  exists j', j <= j' <= k /\ p j' /\
  forall x : nat, j' < x <= k -> ~ p x. intros.
  induction H0. exists j. split. split; apply le_refl.
  split. assumption. intros. inversion H0. apply False_ind.
  eapply lt_not_le. apply H1. assumption.
  invertClear IHle. addHyp (K (S m)). invertClear H2.
  exists (S m). split. split. constructor. assumption. apply le_refl.
  split. assumption. intros. invertClear H2. apply False_ind.
  eapply lt_not_le. apply H4. assumption. exists x.
  invertClear H1. invertClear H4. split. invertClear H2.
  split. assumption. constructor. assumption. split.
  assumption. intros. invertClear H4. invertClear H7.
  assumption. apply H5; split; assumption. Qed.

Open Scope R_scope.

(** This is the interval in the past during which we show that any entity
in a non fail safe mode m must have sent a message containing mode m.*)
Definition preSentInterval (m : Mode) : Interval :=
  let lower := msgLatency + Rmax adaptNotif transMax in
  let upper := lower + period m + trans m in
  (\lower, upper\].

(** The interval of time in the past during which we can show a
sufficient pre-broadcast takes place, parametrised on the mode m.*)
Definition preDeliveredInterval (m : Mode) : Interval :=
  let lower := Rmax adaptNotif transMax in
  let upper := lower + period m + trans m in
  (\lower, upper\].



(** The upper bound of the pre bc suff interval is positive*)
Lemma preBcSuffUpperPos : forall m : Mode,
  0 <= upper (preDeliveredInterval m). intros. apply Rle_trans with (r2 := adaptNotif).
  destruct adaptNotif. destruct time. apply cond_nonneg.
  replace (nonneg (time adaptNotif)) with
  (nonneg (time adaptNotif) + 0 + 0). 
  unfold preDeliveredInterval. simpl. repeat apply Rplus_le_compat.
  apply Rmax_l. destruct (period m). destruct time. apply cond_nonneg.
  destruct (trans m). destruct time. apply cond_nonneg.
  ring. Qed.

Lemma plusIntervalZero : forall (i : Interval),
  i [+] zeroTime = i. intros. destruct i. unfold zeroTime.
  simpl. f_equal; ring. Qed.

Open Scope nat_scope.

(**The same theorem as rightmost but with negation of P as existential and P as
universal properties.*)
Theorem rightmostNeg : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  ~p j -> j <= k ->
  exists j', j <= j' <= k /\ ~p j' /\
  forall x : nat, j' < x <= k -> p x. intros.
  assert (forall a, ~(~(p a)) -> p a). intros.
  addHyp (K a). invertClear H2. apply H3. apply False_ind.
  apply H1. assumption. assert (forall a, decidable (~ p a)).
  intros. apply dec_not. apply K.
  addHyp (rightmost j k (fun j => ~p j) H2 H H0).
  invertClear H3. rename x into j'. exists j'. invertClear H4.
  invertClear H5. split. assumption. split. assumption. intros.
  apply H1. apply H6. assumption. Qed.   

(**This characterisation of le leaves does the inductive part by
subtracting from the lesser number rather than adding to the larger
one, and makes certain proofs easier.*)
Inductive leAlt : nat -> nat-> Prop :=
  | leaRefl : forall (n : nat), leAlt n n
  | leaSucc : forall (m n : nat), leAlt (S m) n -> leAlt m n.

(**This is the key difference between leAlt and le.*)
Lemma leAlt_S : forall (m n : nat), leAlt m n -> leAlt m (S n).
  intros. induction H. repeat constructor. constructor.
  assumption. Qed. 

(*The alternative characterisation of le coindices with
the standard one.*)
Lemma leAltLe : forall (m n : nat), m <= n <-> leAlt m n.
  intros. split; intros. induction H. constructor.
  apply leAlt_S. assumption. induction H. constructor.
  apply le_S_n. constructor. assumption. Qed.  

(**If a property p is true of the number k, and j <= k,
then there is some smallest j' between j and k such that p is true at j'.*)
Theorem leftmost : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p k -> j <= k ->
  exists j', j <= j' <= k /\ p j' /\
  forall x : nat, j <= x < j' -> ~ p x. intros.
  rewrite leAltLe in H0. induction H0.
  exists n. split. split; apply le_refl.
  split. assumption. intros. inversion H0. apply False_ind.
  eapply lt_not_le. apply H2. assumption. apply IHleAlt in H.
  clear IHleAlt. invertClear H. addHyp (K (m)).
  invertClear H1. invertClear H3. invertClear H.
  exists m. split. split. constructor. rewrite leAltLe.
  constructor. assumption. split. assumption.
  intros. invertClear H. unfold not. intros. eapply lt_not_le.
  apply H6. assumption. exists x. split. invertClear H2. split.
  apply le_S_n. constructor. assumption. assumption.
  split. assumption. intros. invertClear H.
  invertClear H5. rewrite <- H. assumption.
  apply H4. split. apply le_n_S. assumption.
  rewrite H7. assumption. Qed.

(**The same theorem as leftmost but with
negation of P as existential and P as universal properties.*)
Theorem leftmostNeg : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  ~p k -> j <= k ->
  exists j', j <= j' <= k /\ ~p j' /\
  forall x : nat, j <= x < j' -> p x. intros.
  assert (forall a, ~(~(p a)) -> p a). intros.
  addHyp (K a). invertClear H2. apply H3. apply False_ind.
  apply H1. assumption. assert (forall a, decidable (~ p a)).
  intros. apply dec_not. apply K.
  addHyp (leftmost j k (fun j => ~p j) H2 H H0).
  invertClear H3. rename x into j'. exists j'. invertClear H4.
  invertClear H5. split. assumption. split. assumption. intros.
  apply H1. apply H6. assumption. Qed. 

(**If p is true at j and j <= k, then there is some rightmost
j' such that p is true from j to j' and either ~p is true at j'+1 or j' = k.*)
Theorem rightmostCont : forall (j k : nat) (p : nat -> Prop)
  (K : forall i : nat, decidable (p i)),
  p j -> j <= k ->
  exists j' , j <= j' <= k /\ 
  forall m : nat, j <= m <= j' -> p m /\
  (~p (S j') \/ j' = k). intros. induction H0.
  exists j. split. split; constructor. intros. split.
  assert (m = j). invertClear H0.
  apply le_antisym; assumption. rewrite H1. assumption.
  right. reflexivity. invertClear IHle. invertClear H1.
  rename x into j'. invertClear H2.
  apply le_lt_eq_dec in H4. invertClear H4.
  (*Case j' < m*) 
  exists j'. split. split. assumption.
  constructor. ltToLe H2. assumption. intros.
  rename m0 into n. addHyp (H3 n H4). clear H3.
  invertClear H5. split. assumption. invertClear H6.
  left. assumption. apply False_ind. rewrite <- H5 in H2.
  eapply lt_irrefl. apply H2.
  (*Case j' = m*)
  addHyp (K (S m)). invertClear H4.
  (*Case p is true at the last p*)
  exists (S m). split.
  split. constructor. rewrite <- H2. assumption. constructor.
  intros. invertClear H4. apply le_lt_eq_dec in H7.
  invertClear H7. rename m0 into n. rewrite H2 in H3.
  addHyp (H3 n). assert (j <= n <= m). split. assumption.
  apply le_S_n. apply H4. addHyp (H7 H8). clear H7.
  invertClear H9. split. assumption. right. reflexivity.
  split. rewrite H4. assumption. right. reflexivity.
  (*Case p is not true at the last p*)
  exists j'. split. split. assumption. rewrite H2.
  repeat constructor. intros n Q.
  addHyp (H3 n Q). invertClear H4. split. assumption.
  invertClear H7. left. assumption. left.
  rewrite H4. assumption. Qed.

Open Scope R_scope.

(**If u = 0 as a real, then u = zeroTime.*)
Lemma timeZero : forall (u : Time),
  (nonneg (time u)) = 0 -> u = zeroTime. intros.
  unfold zeroTime. destruct u. f_equal. destruct time0.
  unfold zeroNonneg. simpl in H. generalize dependent cond_nonneg.
  rewrite H. intros. f_equal. apply proof_irrelevance. Qed.

(*2*speedMax gets used a lot, as it is the maximum relative speed, so we prove this special
result for it*)
Lemma speedMax_double_nonneg : 0 <= 2*speedMax. replace 0 with (2*0).
  apply Rmult_le_compat_l. apply two_nonneg. apply speedMax_nonneg.
  ring. Qed.

(**All numbers within the preDeliveredInterval are strictly positive.*)
Lemma inPreBcSuffPos : forall (m : Mode) (u : Time),
  u [:] (preDeliveredInterval m) -> 0 < u. intros. inversion H.
  simpl in H0. apply Rle_lt_trans with (r2 := adaptNotif).
  timeNonneg. eapply Rle_lt_trans; try apply H0.
  apply Rmax_l. Qed.



(*****Incl stuff******)

Lemma inclNotEx {A : Type} (l1 l2 : list A) : (forall x y : A, {x = y} + {x <> y}) ->
  ~ incl l1 l2 -> exists a, a _: l1 /\ ~a _: l2. intros. induction l1.
  apply False_ind. apply H. unfold incl. intros. inversion H0.
  addHyp (in_dec X a l2). invertClear H0. assert (~ incl l1 l2).
  unfold not. intro. apply H. unfold incl. intros. inversion H2.
  rewrite <- H3. assumption. apply H0. apply H3. apply IHl1 in H0.
  invertClear H0. exists x. invertClear H2. split. apply in_cons.
  assumption. assumption. exists a. split. constructor. reflexivity.
  assumption. Qed. 

Lemma incl_emp {A : Type} (l : list A) : incl [] l. unfold incl. intros.
  inversion H. Qed.

Lemma incl_emp_eq {A : Type} (l : list A) : incl l [] -> l = []. intros.
  unfold incl in H. destruct l. reflexivity. addHyp (H a).
  cut (a _: []). intros. inversion H1. apply H0. constructor.
  reflexivity. Qed.

Lemma diff_emp {A : Type} (l : list A)
  (p : forall x y : A, {x = y} + {x <> y}) : set_diff p l [] = [] -> l = [].
  intros. destruct l. reflexivity. inversion H. apply set_add_not_empty in H1.
  inversion H1. Qed.

Lemma incl_diff_equiv {A : Type} (l1 l2 : list A)
  (p : forall x y : A, {x = y} + {x <> y}) : incl l1 l2 <-> set_diff p l1 l2 = [].
  split; intros. unfold incl in H. remember (set_diff p l1 l2) as l.
  destruct l. reflexivity. apply False_ind. cut (~a _: l2). intros. apply H0.
  apply H. apply set_diff_elim1 with (Aeq_dec := p) (y := l2). rewrite <- Heql.
  constructor. reflexivity. apply set_diff_elim2 with (Aeq_dec := p) (x := l1).
  rewrite <- Heql. constructor. reflexivity.
  unfold incl. intros. addHyp (in_dec p a l2). invertClear H1. assumption.
  addHyp (set_diff_intro p a l1 l2 H0 H2). rewrite H in H1. inversion H1. Qed.

Lemma decIncl {A : Type} (l1 l2 : list A) :
  (forall x y : A, {x = y} + {x <> y}) -> decidable (incl l1 l2).
  intros. remember (set_diff X l1 l2) as l. destruct l. left.
  rewrite incl_diff_equiv. symmetry. apply Heql.
  right. unfold not. intro. rewrite incl_diff_equiv with (p := X) in H.
  rewrite <- Heql in H. inversion H. Qed.

Lemma inter_incl {A : Type} (x y z : set A)
  (p : forall a b : A, {a = b} + {a <> b}) :
  incl x y -> incl (set_inter p x z) (set_inter p y z). intros.
  unfold incl. intros. addHyp H0. apply set_inter_elim1 in H0.
  apply set_inter_elim2 in H1. apply H in H0. apply set_inter_intro;
  assumption. Qed.  

(*****END : Incl stuff******)


(*****Set stuff******)

Lemma set_inter_nil_cons {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p (x :: l1) l2 = [] -> set_inter p l1 l2 = [].
  intros. remember (set_inter p l1 l2). destruct s. reflexivity.
  assert (x0 _: set_inter p l1 l2). rewrite <- Heqs. constructor.
  reflexivity. apply set_inter_elim in H0. invertClear H0.
  assert (x0 _: (x :: l1)). unfold In. right. apply H1.
  assert (x0 _: []). rewrite <- H. apply set_inter_intro.
  apply H0. assumption. inversion H3. Qed.

Lemma set_inter_nil_in1 {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p l1 l2 = [] -> x _: l1 -> ~x _: l2. intros.
  generalize dependent l2. induction l1; unfold not; intros.
  inversion H0. inversion H0. assert (a _: []). rewrite <- H.
  apply set_inter_intro. rewrite <- H2 in H0. assumption.
  rewrite H2. assumption. inversion H3.
  eapply IHl1. apply H2. eapply set_inter_nil_cons. apply H.
  assumption. Qed.  

Lemma set_inter_nil_in2 {X : Type}
  {p : forall x y : X, {x = y} + {x <> y}} (l1 l2 : list X) (x : X) :
  set_inter p l1 l2 = [] -> x _: l2 -> ~x _: l1. unfold not. intros.
  generalize H0. eapply set_inter_nil_in1. apply H. assumption. Qed.

(*****END : Set stuff******)

(*LOCAL TIDY*)

Lemma sufficient_suffBool m r : sufficient m r ->
  suffBool m r = true. intros. unfold suffBool.
  remember (suffDec m r) as SD. destruct SD. reflexivity.
  false. Qed.

Lemma possInc_possIncBool m m' r :
  possiblyIncompatible m m' (distance r) ->
  possIncBool m m' r = true. intros. unfold possIncBool.
  remember (possIncDec m m' r) as PD. destruct PD. reflexivity.
  false. Qed.

Lemma possIncBool_possInc m m' r :
  possIncBool m m' r = true ->
  possiblyIncompatible m m' (distance r).
  unfold possIncBool. intros. remember (possIncDec m m' r) as PD.
  destruct PD. assumption. inversion H. Qed.

Lemma possIncDist_positive m1 m2 : 0 < possIncDist m1 m2.
  (*Proof: follows from adaptNotif_positive and speedMax_pos.*)
  replace 0 with (0 + 0); [ | ring]. apply Rplus_le_lt_compat.
  apply cond_nonneg. repeat apply Rmult_lt_0_compat.
  Admitted. (**Old proof broken - needs to be reproved. Result is pretty obvious.*)