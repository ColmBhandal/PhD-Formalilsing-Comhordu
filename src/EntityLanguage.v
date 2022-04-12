
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
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.

(***************Messages*********************)


(** A message is a vector of values augmented with coverage and location information.*)
Record Message : Type :=
mkMsg
{
  msgPayload :> list Base;
  msgPos : Position;
  msgCoverage : Distance
}.
Notation "[- v , l , r -]" := (mkMsg v l r) (at level 40).

(** Extract the delivery radius from a broadcast.*)
Definition rangeMsg (m : Message) : Distance :=
   match m with [-v, l, r-] => r end.

(** Return the first mode that occurs in v, or None if there is no such mode.*)
Fixpoint firstMode (v : list Base) : option Mode :=
  match v with
  | [] => None
  | b :: vs => match b with
    | baseMode m => Some m
    | _ => firstMode vs
    end
  end.

(** modeBc b will return the first mode m, if it exists,
within the list of base values in b.*)
Definition modeBc (m : Message) : option Mode :=
  match m with [-v, l, r-] => firstMode v end.

(** Extract the position information from a broadcast. Note that this is the position
of the sending entity at the time of sending rather than delivery. The entity may have
moved between sending and delivery.*)
Definition posBc (m : Message) : Position :=
  match m with [-v, l, r-] => l end.



(*************** Syntax (and some other stuff) *********************)


(** And entity is a quadruple of components: An interface term, a software term,
an MState term and a location.*)
Record Entity : Type := mkEntity
{
  procEnt :> ProcTerm;
  posEnt :> Position;
  interEnt :> Interface;
  mstEnt : ModeState 
}.
Notation "[| p , l , i , k |]" := (mkEntity p l i k) (at level 30).

(** Equality on entities is decidable.*)
Lemma eqDecEnt : eqDec Entity. unfold eqDec.
  destruct x1, x2. addHyp (eqDecModeState mstEnt0 mstEnt1).
  addHyp (eqDecPosition posEnt0 posEnt1).
  addHyp (eqDecInterface interEnt0 interEnt1).
  addHyp (eqDecProcTerm procEnt0 procEnt1). invertClear H2.
  invertClear H. invertClear H0. invertClear H1. left.
  rewrite H2, H, H0, H3. reflexivity.
  right. unfold not. intro. apply H0. inversion H1. reflexivity.
  right. unfold not. intro. apply H. inversion H0. reflexivity.
  right. unfold not. intro. apply H2. inversion H. reflexivity.
  right. unfold not. intro. apply H3. inversion H2. reflexivity.
  Qed.

(** The current mode of an entity is the current mode of the mode state.*)
Coercion currModeEnt (e : Entity) : Mode :=
  match e with [|_, _, _, a|] => a end.

(** The next mode of an entity is the next mode of the mode state.*)
Definition nextModeEnt (e : Entity) : option Mode :=
  match e with [|_, _, _, a|] => nextModeMState a end.

Open Scope R_scope.

(** If the minimum distance of compatibiltiy of the respective modes
of the entities is less than or equal to the separation of the
entities in space, then they are compatible.*)
Definition compatible (e1 e2 : Entity) : Prop :=
  (minDistComp e1 e2) <= (dist e1 e2).
Notation "e1 ~~ e2" := (compatible e1 e2) (left associativity, at level 40).

(** Compatibility is a symmetric relation.*)
Lemma compatibleSymmetric : forall (e1 e2 : Entity), (e1 ~~ e2) <-> (e2 ~~ e1).
  unfold compatible. intros. split; intros; rewrite minDistCompSymmetric in H;
  rewrite distSymmetric in H; assumption. Qed.


(***************Semantics*********************)

(** A discrete action is either the input, output or ignorance of a message, or
it is the silent value tau.*)
Inductive ActDiscEnt : Type :=
  | aeTagOut : Message -> ActDiscEnt
  | aeTagIn : Message -> ActDiscEnt
  | aeTagIg : Message -> ActDiscEnt
  | aeTau : ActDiscEnt.
Notation "b #!" := (aeTagOut b) (at level 30).
Notation "b #?" := (aeTagIn b) (at level 30).
Notation "b #:" := (aeTagIg b) (at level 30).

Reserved Notation "e1 -EA- a ->> e2" (left associativity, at level 50).
Reserved Notation "e1 -ED- a ->> e2" (left associativity, at level 50).

(** The discrete action semantics for entities.*)
Inductive stepDiscEnt : Entity -> ActDiscEnt -> Entity -> Prop :=
  | stepDeProcTau : forall (p p' : ProcTerm) (l : Position) (i : Interface) (k : ModeState),
    p -PA- tauAct -PA> p' -> [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k |]
  | stepDeIOProcInter : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list Base),
    p -PA- chanOutProc ;! v -PA> p' -> i -i- chanOutProc {? v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeIOInterProc : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list Base),
    p -PA- chanInProc ;? v -PA> p' -> i -i- chanInProc {! v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeNotif : forall (p p' : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list Base),
    p -PA- chanAN ;? v -PA> p' -> i -i- chanAN {! v -i> i' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i' , k |]
  | stepDeRdStbl : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState),
    p -PA- chanMStable *? -PA> p' -> k -ms- chanMStable @! -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeCurrWrite : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMCurr *! -PA> p' -> k -ms- chanMCurr @? -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeCurrRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMCurr ;? [baseMode m] -PA> p' -> k -ms- chanMCurr .! m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeNextWrite : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMNext ;! [baseMode m] -PA> p' -> k -ms- chanMNext .? m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDeNextRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    p -PA- chanMNext ;? [baseMode m] -PA> p' -> k -ms- chanMNext .! m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  | stepDePosRead : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k : ModeState),
    p -PA- chanPos ;? [basePosition l] -PA> p' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k |]
  (** If the message sent was too far away, it gets ignored.*)
  | stepDeIgnore : forall (p : ProcTerm) (l l' : Position)
    (i : Interface) (k : ModeState) (v : list Base) (r : Distance),
     r < dist l l' -> 
    [| p , l , i , k |] -EA- [-v, l', r-]#: ->> [| p , l , i , k |]
  (** If the message sent was within range, then it gets input. This can be proven not
  to block by analysing the behaviour of interface components. Therefore, a message
  should always be accepted.*)
  | stepDeIn : forall (p : ProcTerm) (l l' : Position)
    (i i' : Interface) (k : ModeState) (v : list Base) (r : Distance),
    dist l l' <= r -> i -i- chanIOEnv {? v -i> i' ->
    [| p , l , i , k |] -EA- [-v, l', r-]#? ->> [| p , l , i' , k |]
  | stepDeOut : forall (p : ProcTerm) (l : Position)
    (i i' : Interface) (k : ModeState) (v : list Base) (r : Distance),
    i -i- chanIOEnv _! v !_ r -i> i' ->
    [| p , l , i , k |] -EA- [-v, l, r-]#! ->> [| p , l , i' , k |]
  | stepDeTest : forall (p : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState) (m : Mode),
    k -ms- chanMNext .? m -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p , l , i , k' |]
  where "e1 -EA- a ->> e2" := (stepDiscEnt e1 a e2).

(**An entity e is discrete action enabled for the discrete action a iff
there is some entity e' such that e transitions to e' via a.*)
Definition discActEnabledEnt (e : Entity) (a : ActDiscEnt) :=
  exists e', e -EA- a ->> e'.

(** This predicate says that it is impossible for p to synchronise with either i
or k via the discrete action a i.e. if p can do a, then neither i nor k can do its
complement.*)
Definition noSyncNow (a : DiscAct) (p : ProcTerm)
  (i : Interface) (k : ModeState) : Prop :=
  discActEnabled p a ->
  (~discActEnabledInter (a^) i /\ ~discActEnabledMState (a^) k).

(** This predicate says that p i and k cannot synchronise now, nor can they
synchronise after each has respectively performed a delay of d' that is less
than d.*)
Definition noSync (p : ProcTerm) (i : Interface)
  (k : ModeState) (d : Delay) : Prop :=
  forall a : DiscAct, noSyncNow a p i k /\
  (forall (p' : ProcTerm) (i' : Interface) (k' : ModeState) (d' : Delay),
  d' < d -> p -PD- d' -PD> p' -> i -i- d' -i> i' -> k -ms- d' -ms> k' ->
  noSyncNow a p' i' k'). 

(** The timed action semantics for entities. There is only one delay law. The software,
mode state and interface components all must delay by the same amount d for the entire
entity to delay by this amount. After this, there are two interesting premises to the law.
The first deals with a displacement vector delta, saying that its absolute value must be
at most the delay multiplied by the maximum speed. In other words, movement is bounded.
The other premise that is of interest says that the components of the entity must not
be capable of synchronisation at any point during the delay.*)
Inductive stepTimedEnt : Entity -> Delay -> Entity -> Prop :=
  | stepTeDel : forall (d : Delay) (p p' : ProcTerm) (l delta : Position)
    (i i' : Interface) (k k' : ModeState),
    p -PD- d -PD> p' -> i -i- d -i> i' -> k -ms- d -ms> k' ->
    displacement delta <= speedMax * d -> noSync p i k d ->
    [| p , l , i , k |] -ED- d ->> [| p' , addPos l delta, i' , k' |]
  where "e1 -ED- d ->> e2" := (stepTimedEnt e1 d e2).


(*************** Results & Tactics *********************)

(*Destruct an entity and then its interface component*)
Ltac destr_ent_inter e p l k li lo ln := let h := fresh in destruct e as [p l h k];
  destruct h as [li lo ln].

(**If the current mode has changed across a tau transition, then the software process
output on mCurr, and the mode state input on the same channel.*)
Theorem curr_switch_proc (p p' : ProcTerm) (l l' : Position) (h h' : Interface) (k k' : ModeState) :
  [|p, l, h, k|] -EA- aeTau ->> [|p', l', h', k'|] -> currModeMState k <> currModeMState k' ->
  p -PA- chanMCurr *! -PA> p' /\ k -ms- chanMCurr @? -ms> k'.
  intros H H0.
  (*By inversion on the discrete entity transition*)
  (*We first eliminate the cases where the mode state is the preserved.*)
  invertClear H; try (false; apply H0; assumption);
  (*We can then eliminate all cases where the the action is not tau,
  and simultaneously match our goal.*)  
  try (lets K : curr_switch_mState H10 H0; inversion K).
  (*Now we have this case which follows from assumptions.*)
  split;assumption.
  (*Finally we deal with a stray case that wasn't caught in our earlier elimination.*)
  lets K : curr_switch_mState H2 H0. inversion K. Qed.

(** The derivative of an ignore transition is the same as the source.*)
Theorem ignoreEqEnt : forall (e e' : Entity) (m : Message),
  e -EA- m#: ->> e' -> e = e'. intros. invertClear H. reflexivity. Qed.

(** An entity can always either input or ignore a message.*)
Theorem inOrIgEnt : forall (e : Entity) (m : Message),
  discActEnabledEnt e (m#?) \/ discActEnabledEnt e (m#:). intros.
  destruct m as [v l' r]. destruct e as [p l i k].
  addHyp (Rlt_or_le r (dist l l')). invertClear H. right.
  exists ([|p, l, i, k|]). apply stepDeIgnore. assumption. 
  left. addHyp (interfaceInEnabled i v). invertClear H.
  rename x into i'. exists ([|p, l, i', k|]).
  apply stepDeIn; assumption. Qed.

Conjecture dec_compatible : forall (e1 e2 : Entity),
  e1 ~~ e2 \/ ~(e1 ~~e2).
(**Proof: Obvious*)

Conjecture currMode_ent_mState : forall (p : ProcTerm) (l : Position) (h : Interface)
  (k : ModeState) (m : Mode), currModeEnt ([|p, l, h, k|]) = m -> currModeMState k = m.
(**Proof: Obvious from definitions*)

Lemma link_ent_inter_disc p p' l l' h h' k k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  h = h' \/ 
  (k = k' /\
  ((exists v, (h -i- chanOutProc {? v -i> h' /\ p -PA- chanOutProc;! v -PA> p')) \/
  (exists v, (h -i- chanInProc {! v -i> h' /\ p -PA- chanInProc;? v -PA> p')) \/
  (exists v, (h -i- chanAN {! v -i> h' /\ p -PA- chanAN;? v -PA> p')) \/
  (exists v, h -i- chanIOEnv {? v -i> h') \/
  (exists v r, h -i- chanIOEnv _! v !_ r -i> h'))).
  (*Inversion on entity transition and try LHS*)
  introz U. inversion U; subst; try (left; reflexivity); right;
  (split; [ reflexivity | ]).
  (*Now we do the other cases.*)
  left. exists v. split; assumption.
  right. left. exists v. split; assumption.
  right. right. left. exists v. split; assumption.
  do 3 right. left. exists v. assumption.
  do 4 right. exists v r. assumption. Qed.

(*Adds the result stepDisc_ent_inter to the hypotheses and splits it up and tidies it.*)
Ltac link_entinterdisc_tac v r U := 
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -EA- ?a ->> [|?p', ?l', ?h', ?k'|] |- _] =>
    let H1 := fresh in lets H1 : link_ent_inter_disc H;
    let U1 := fresh U in let H0 := fresh in 
    (*Break off first disjunct as U1, leave H0 as chunk*)
    elim_intro H1 U1 H0;[ | 
    let H7 := fresh in let H8 := fresh in
    (*Break conjunction H0 into H7 and H8*)
    decompAnd2 H0 H7 H8; let V := fresh v in
    (*Break H8 up into 5 disjuncts*)
    elimOr5 H8 U;
    [(let H2 := fresh in destruct U1 as [V H2]; 
    andflat U).. | let H2 := fresh in destruct U1 as [V H2]; rename H2 into U1 | 
    let R := fresh r in let H3 := fresh in
    decompEx2 U1 V R H3;rename H3 into U1 ]
    ]
  end.

Lemma link_ent_inter_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  h -i- d -i> h'. intros. inversion H. assumption. Qed.

Ltac link_entinterdel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_inter_del H
  end.

Lemma link_ent_soft_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  p -PD- d -PD> p'. intros. inversion H. assumption. Qed.

Ltac link_entsoftdel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_soft_del H
  end.

Lemma link_ent_mState_del p p' l l' h h' k k' d :
  [|p, l, h, k|] -ED- d ->> [|p', l', h', k'|] ->
  k -ms- d -ms> k'. intros. inversion H. assumption. Qed.

Ltac link_entmstatedel_tac U :=
  match goal with
  | [ H : [|?p, ?l, ?h, ?k|] -ED- ?d ->> [|?p', ?l', ?h', ?k'|] |- _] =>
  let U1 := fresh U in lets U1 : link_ent_mState_del H
  end.

Lemma timeSplit_ent e e'' d d' d'' :
  e -ED- d'' ->> e'' -> d'' = d +d+ d' ->
  exists e', e -ED- d ->> e' /\ e' -ED- d' ->> e''. Admitted. (*6*)
(**Proof: This should follow from time split properties of the underlying components. Also, it would have to be shown that the noSynch predicate would still hold for the intermediate entity component e', with the time parameter changed.*)


(*LOCAL TIDY*)

(** Destructs the next entity it encounters naming its sub-components as fresh instances
of p, l, h, k.*)
Ltac destrEnt p l h k :=
  match goal with
  [ e : Entity |- _ ] =>
  let vp := fresh p in let vl := fresh l in
  let vh := fresh h in let vk := fresh k in
  destruct e as [vp vl vh vk]
  end.

(** Repeatedly destructs all entities according to the names given.*)
Ltac destrEnts p l h k := repeat destrEnt p l h k.

(**Destructs any entities it finds. May have also be searched for as destr_ents.*)
Ltac destrEnts_norm := let p := fresh "p" in let l := fresh "l" in
  let h := fresh "h" in let k := fresh "k" in destrEnts p l h k.

(** From a delay on an entity creates the hypothesis NS (a parameter) that no synchronisation
is possible between any of the components of the entity.*)
Ltac del_noSync_tac NS :=
  match goal with [a : DiscAct, U : [|?p0, _, ?h0, ?k0|] -ED- ?d ->> _ |- _] =>
  assert (noSync p0 h0 k0 d) as NS; [inversion U; assumption | ]
  end.

(** From a hypothesis X of noSynch between various components, creates a weakened version of X
saying that noSyncNow is possible between those components and calls it NS.*)
Ltac noSync_noSyncNow_tac NS := 
  match goal with
  [ a : DiscAct, X : noSync ?p0 ?h0 ?k0 _ |- _] =>
  assert (noSyncNow a p0 h0 k0) as NS; [unfold noSync in X; apply X
  | ] end.

(** From an entity delay creates the hypothesis NS saying that noSyncNow is possible between
the components of the entity, via the first action a matched in the hypotheses.*)
Ltac del_noSyncNow_tac NS :=
  let X := fresh in del_noSync_tac X; noSync_noSyncNow_tac NS;
  clear X.

(**Takes a delay hypothesis and inverts to give that noSyncNow holds for
the components of the entity in question.*)
Ltac noSyncNow_tac := match goal with
  [A : [|?p, _, ?h, ?k|] -ED- ?d ->> _ |- _] =>
  let NS := fresh "NS" in
  assert (forall a, noSyncNow a p h k) as NS;
  [inversion A; match goal with [B : noSync p h k d |- _] =>
  apply B end| ] end.

(*Inverts an entity delay to a process delay*)
  Ltac invertDel_ent_proc := match goal with
  [U1 : [|?p0, _, _, _|] -ED- ?d ->> [|?p, _, _, _|] |- _ ]
  => assert (p0 -PD- d -PD> p) as PD; [inversion U1; assumption | ] end.

(** Creates a hypothesis PD saying that some process delays to another process,
then rewrites TR, an equality identifying the process with a triple of processes,
then creates three hypotheses saying that the sort relations of the three processes
are distinct, called SORT1_2, SORT1_3 and SORT2_3.*)
Ltac del_triple_sort_tac :=
  (try invertDel_ent_proc); match goal with
  [TR : ?p = ?p1 $||$ ?p2 $||$ ?p3, PD : ?p -PD- ?d -PD> ?p' |- _] =>
  rewrite TR in PD; let U := fresh in let x := fresh "SORT1_2" in
  let y := fresh "SORT1_3" in let z := fresh "SORT2_3" in
  (lets U : del_triple_sort PD; decompAnd3 U x y z) end.

(*-LOCAL TIDY*)
