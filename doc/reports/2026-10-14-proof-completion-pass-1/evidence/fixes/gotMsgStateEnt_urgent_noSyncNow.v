(* HELPERS *)
From Stdlib Require Import Lra.

(** Repeated inversion on sort / discrete / timed hypotheses whose process term is
not a variable. *)
Ltac gotMsgStateEnt_urgent_inv :=
  repeat match goal with
  | H : sort _ _ ?t |- _ =>
    tryif is_var t then fail else (inversion H; subst; clear H)
  | H : stepDiscProc ?t _ _ |- _ =>
    tryif is_var t then fail else (inversion H; subst; clear H)
  | H : stepTimedProc ?t _ _ |- _ =>
    tryif is_var t then fail else (inversion H; subst; clear H)
  end.

(** Evaluate the (opaque) variable-equality tests left over by substitution. *)
Ltac gotMsgStateEnt_urgent_vareq :=
  repeat (unfold varEq; simpl;
    match goal with
    | |- context [varEqDec ?x ?y] =>
      let E := fresh "E" in
      destruct (varEqDec x y) as [E|E];
      [ try (inversion E; fail) | try (exfalso; apply E; reflexivity) ]
    end).

(** Prove that a substituted unfolding of gotMsgN is literally gotMsg m l0. *)
Ltac gotMsgStateEnt_urgent_eqtac :=
  unfold gotMsg; simpl; unfold update, varEq, resetSub; simpl;
  gotMsgStateEnt_urgent_vareq; reflexivity.

(** The empty interface. *)
Definition gotMsgStateEnt_urgent_I : Interface :=
  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []).

(*** gotMsg m l0 only ever inputs on chanPos and only delays to itself. ***)

Lemma gotMsgStateEnt_urgent_G_step (m : Mode) (l0 : Position) a q :
  gotMsg m l0 -PA- a -PA> q -> exists v, a = chanPos ;? v.
Proof. intro S. unfold gotMsg in S. inversion S; subst. eauto. Qed.

Lemma gotMsgStateEnt_urgent_G_sort (m : Mode) (l0 : Position) a d :
  sort a d (gotMsg m l0) -> exists v, a = chanPos ;? v.
Proof. intro S. unfold gotMsg in S. inversion S; subst. eauto. Qed.

Lemma gotMsgStateEnt_urgent_G_del (m : Mode) (l0 : Position) d q :
  gotMsg m l0 -PD- d -PD> q -> q = gotMsg m l0.
Proof. intro S. unfold gotMsg in *. inversion S; subst. reflexivity. Qed.

(*** The listener derivative of listening after reading [m, l0] on chanInProc. ***)

Definition gotMsgStateEnt_urgent_X (m : Mode) (l0 : Position) : ProcTerm :=
  subProcTerm (listsToSub [vM'', vL'] (listBaselistExp [baseMode m, basePosition l0]))
    (gotMsgN $([eVar vM'', eVar vL'])$).

Lemma gotMsgStateEnt_urgent_X_reach (m : Mode) (l0 : Position) :
  listening -PA- chanInProc ;? [baseMode m, basePosition l0] -PA> gotMsgStateEnt_urgent_X m l0.
Proof.
  unfold listening. apply stepDpChoiceL. apply stepDpChoiceL. apply stepDpChoiceR.
  apply stepDpIn. reflexivity.
Qed.

Lemma gotMsgStateEnt_urgent_X_step (m : Mode) (l0 : Position) a q :
  gotMsgStateEnt_urgent_X m l0 -PA- a -PA> q <-> gotMsg m l0 -PA- a -PA> q.
Proof.
  split; intro S.
  - unfold gotMsgStateEnt_urgent_X in S. simpl in S. inversion S; subst.
    simpl in *. match goal with H : (_, _) = (_, _) |- _ => inversion H; subst end.
    match goal with H : stepDiscProc ?t _ _ |- _ =>
      assert (EQ : t = gotMsg m l0) by gotMsgStateEnt_urgent_eqtac; rewrite EQ in H; exact H end.
  - unfold gotMsgStateEnt_urgent_X. simpl. eapply stepDpApp; [reflexivity | ].
    match goal with |- stepDiscProc ?t _ _ =>
      assert (EQ : t = gotMsg m l0) by gotMsgStateEnt_urgent_eqtac; rewrite EQ; exact S end.
Qed.

Lemma gotMsgStateEnt_urgent_X_sort (m : Mode) (l0 : Position) a d :
  sort a d (gotMsgStateEnt_urgent_X m l0) -> sort a d (gotMsg m l0).
Proof.
  intro S. unfold gotMsgStateEnt_urgent_X in S. simpl in S. inversion S; subst.
  simpl in *. match goal with H : (_, _) = (_, _) |- _ => inversion H; subst end.
  match goal with H : sort _ _ ?t |- _ =>
    assert (EQ : t = gotMsg m l0) by gotMsgStateEnt_urgent_eqtac; rewrite EQ in H; exact H end.
Qed.

Lemma gotMsgStateEnt_urgent_X_del (m : Mode) (l0 : Position) d q :
  gotMsgStateEnt_urgent_X m l0 -PD- d -PD> q <-> gotMsg m l0 -PD- d -PD> q.
Proof.
  split; intro S.
  - unfold gotMsgStateEnt_urgent_X in S. simpl in S. inversion S; subst.
    simpl in *. match goal with H : (_, _) = (_, _) |- _ => inversion H; subst end.
    match goal with H : stepTimedProc ?t _ _ |- _ =>
      assert (EQ : t = gotMsg m l0) by gotMsgStateEnt_urgent_eqtac; rewrite EQ in H; exact H end.
  - unfold gotMsgStateEnt_urgent_X. simpl. eapply stepTpApp; [reflexivity | ].
    match goal with |- stepTimedProc ?t _ _ =>
      assert (EQ : t = gotMsg m l0) by gotMsgStateEnt_urgent_eqtac; rewrite EQ; exact S end.
Qed.

Lemma gotMsgStateEnt_urgent_X_bisim (m : Mode) (l0 : Position) :
  ProcEquiv.bisimulation (gotMsgStateEnt_urgent_X m l0) (gotMsg m l0).
Proof.
  constructor.
  - intros a p' ST. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion ST; subst.
    + apply stepPDisc. apply gotMsgStateEnt_urgent_X_step. assumption.
    + apply stepPTimed. apply gotMsgStateEnt_urgent_X_del. assumption.
  - intros a q' ST. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion ST; subst.
    + apply stepPDisc. apply gotMsgStateEnt_urgent_X_step. assumption.
    + apply stepPTimed. apply gotMsgStateEnt_urgent_X_del. assumption.
Qed.

(*** Entity-level facts, generic in the listener term Y. ***)

(** Every discrete action of sleeping || dormant || Y (Y only inputs on chanPos) is
an input on a channel that neither an interface nor a stable mode state outputs on. *)
Lemma gotMsgStateEnt_urgent_nsn (Y : ProcTerm) (k0 : Mode) (i : Interface) a :
  (forall a q, Y -PA- a -PA> q -> exists v, a = chanPos ;? v) ->
  noSyncNow a (sleeping $||$ dormant $||$ Y) i (sing k0).
Proof.
  intros HY [q ST]. unfold sleeping, dormant in ST.
  gotMsgStateEnt_urgent_inv.
  all: try match goal with H : stepDiscProc ?t _ _ |- _ =>
    is_var t; apply HY in H; destruct H as [? EQ]; inversion EQ; subst end.
  all: simpl; split; intro DI; inversion DI; subst;
    match goal with
    | H : _ -i- _ -i> _ |- _ => inversion H
    | H : _ -ms- _ -ms> _ |- _ => inversion H
    end.
Qed.

Lemma gotMsgStateEnt_urgent_pdel (Y Y' : ProcTerm) (d : Delay) :
  (forall a d, sort a d Y -> exists v, a = chanPos ;? v) -> Y -PD- d -PD> Y' ->
  (sleeping $||$ dormant $||$ Y) -PD- d -PD> (sleeping $||$ dormant $||$ Y').
Proof.
  intros HY DY. unfold sleeping, dormant.
  apply stepTpPar; [repeat constructor | apply stepTpPar; [repeat constructor | exact DY | ] | ];
  intros a S1 S2;
  (repeat match goal with H : sort ?x _ ?t |- _ =>
     is_var x; tryif is_var t then fail else (inversion H; subst; clear H) end);
  simpl in S2; gotMsgStateEnt_urgent_inv;
  match goal with H : sort _ _ ?t |- _ =>
    is_var t; apply HY in H; destruct H as [? EQ]; inversion EQ end.
Qed.

Lemma gotMsgStateEnt_urgent_del_shape (Y : ProcTerm) (d : Delay) p' :
  (sleeping $||$ dormant $||$ Y) -PD- d -PD> p' ->
  exists Y', Y -PD- d -PD> Y' /\ p' = (sleeping $||$ dormant $||$ Y').
Proof.
  intro DL. unfold sleeping, dormant in DL. gotMsgStateEnt_urgent_inv.
  eexists. split; [eassumption | reflexivity].
Qed.

(** Generic witness: sleeping || dormant || Y, with Y behaving like gotMsg m l0,
empty interface and stable mode state, is in the gotMsg state and can delay. *)
Lemma gotMsgStateEnt_urgent_cex_gen (Y : ProcTerm) (m k0 : Mode) (l l0 : Position)
  (d : Delay) :
  ProcEquiv.bisimulation Y (gotMsg m l0) ->
  (forall a q, Y -PA- a -PA> q -> exists v, a = chanPos ;? v) ->
  (forall a d, sort a d Y -> exists v, a = chanPos ;? v) ->
  (forall d Y', Y -PD- d -PD> Y' -> Y' = gotMsg m l0) ->
  Y -PD- d -PD> gotMsg m l0 ->
  gotMsgStateEnt m l0 ([| sleeping $||$ dormant $||$ Y, l, gotMsgStateEnt_urgent_I, sing k0 |]) /\
  [| sleeping $||$ dormant $||$ Y, l, gotMsgStateEnt_urgent_I, sing k0 |] -ED- d ->>
  [| sleeping $||$ dormant $||$ gotMsg m l0, l +p+ origin, gotMsgStateEnt_urgent_I, sing k0 |].
Proof.
  intros BI HS HSo HD DY. split.
  - constructor. constructor. unfold gotMsgState. exact BI.
  - apply stepTeDel.
    + apply gotMsgStateEnt_urgent_pdel; assumption.
    + unfold gotMsgStateEnt_urgent_I. apply stepIntDel.
      * apply stepIlDel.
      * apply stepOlLift. apply stepTlDelEmp.
      * apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement, dist2d, origin, dist_euc. simpl.
      replace (Rsqr (0 - 0) + Rsqr (0 - 0))%R with 0%R by (unfold Rsqr; ring).
      rewrite sqrt_0. apply Rmult_le_pos. apply speedMax_nonneg.
      destruct d as [[r rp]]. simpl. lra.
    + intro a. split.
      * apply gotMsgStateEnt_urgent_nsn. assumption.
      * intros p' i' k' d' LT DP DI DK.
        apply gotMsgStateEnt_urgent_del_shape in DP. destruct DP as [Y' [DY' EQ]].
        apply HD in DY'. subst. inversion DK; subst.
        apply gotMsgStateEnt_urgent_nsn. apply gotMsgStateEnt_urgent_G_step.
Qed.

(** The target is false for EVERY candidate definition R of reachableEnt that
contains the initial entities (initialEnt) and is closed under discrete entity
transitions: from the initial entity <procProtocol, origin, I1, failSafeSucc m0>
whose interface holds one incoming message, a single tau step (the listener
reads the message on chanInProc) reaches a gotMsg entity that can delay. *)
Lemma gotMsgStateEnt_urgent_false (R : Entity -> Prop) (m0 : Mode) :
  (forall e, initialEnt e -> R e) ->
  (forall e e' a, R e -> e -EA- a ->> e' -> R e') ->
  ~ (forall (e e' : Entity) (d : Delay) m l,
       R e -> gotMsgStateEnt m l e -> e -ED- d ->> e' -> False).
Proof.
  intros INIT CL H.
  assert (R0 : R ([| procProtocol, origin,
    mkInterface (mkInputList [ <( [baseMode m0, basePosition origin], zeroTime )> ])
      (mkOutputList []) (mkNotifList []), sing (failSafeSucc m0) |])).
  { apply INIT. constructor. constructor. apply failSafeSuccFS. }
  assert (R1 : R ([| sleeping $||$ dormant $||$ gotMsgStateEnt_urgent_X m0 origin, origin,
    gotMsgStateEnt_urgent_I, sing (failSafeSucc m0) |])).
  { eapply CL. exact R0. eapply stepDeIOInterProc.
    - unfold procProtocol. apply stepDpParR. apply stepDpParR.
      apply gotMsgStateEnt_urgent_X_reach.
    - unfold gotMsgStateEnt_urgent_I. apply stepIntFwdIn. apply stepIlLift.
      apply stepTlFwdHd. }
  destruct (gotMsgStateEnt_urgent_cex_gen (gotMsgStateEnt_urgent_X m0 origin) m0
    (failSafeSucc m0) origin origin (mkDelay (mkposreal 1 Rlt_0_1))) as [GS DL].
  - apply gotMsgStateEnt_urgent_X_bisim.
  - intros a q S. apply gotMsgStateEnt_urgent_X_step in S.
    eapply gotMsgStateEnt_urgent_G_step. exact S.
  - intros a d S. apply gotMsgStateEnt_urgent_X_sort in S.
    eapply gotMsgStateEnt_urgent_G_sort. exact S.
  - intros d Y' S. apply gotMsgStateEnt_urgent_X_del in S.
    eapply gotMsgStateEnt_urgent_G_del. exact S.
  - apply gotMsgStateEnt_urgent_X_del. constructor.
  - eapply H; eassumption.
Qed.
Print Assumptions gotMsgStateEnt_urgent_false.

(*** Validation of the suggested fix (thesis Definition 4.22, noComm, clause
     "forall l, ~ P --chanPos<l>?-->"). ***)

(** A gotMsg process can read any position on chanPos. *)
Lemma gotMsgStateEnt_urgent_aux1 (p : ProcTerm) (m : Mode) (l l0 : Position) :
  gotMsgState m l p -> discActEnabled p (chanPos ;? [basePosition l0]).
  activation_tac. Qed.

Lemma gotMsgStateEnt_urgent_fix_core (p : ProcTerm) (l0 : Position) (h : Interface)
  (k : ModeState) m l (l' : Position) :
  gotMsgStateEnt m l ([| p, l0, h, k |]) -> discActEnabled p (chanPos ;? [basePosition l']).
Proof.
  intro GS. inversion GS; subst.
  match goal with H : gotMsgStateProt _ _ _ |- _ => inversion H; subst end.
  apply parTriple_dae_intro3. eapply gotMsgStateEnt_urgent_aux1. eassumption.
Qed.

(** Fix A (thesis-faithful): noSyncNow additionally forbids enabled position reads. *)
Definition gotMsgStateEnt_urgent_noSyncNowA (a : DiscAct) (p : ProcTerm)
  (i : Interface) (k : ModeState) : Prop :=
  discActEnabled p a ->
  ((~discActEnabledInter (complement a) i /\ ~discActEnabledMState (complement a) k) /\
  (forall l : Position, a <> chanPos ;? [basePosition l]))%type.

Definition gotMsgStateEnt_urgent_noSyncA (p : ProcTerm) (i : Interface)
  (k : ModeState) (d : Delay) : Prop :=
  forall a : DiscAct, gotMsgStateEnt_urgent_noSyncNowA a p i k /\
  (forall (p' : ProcTerm) (i' : Interface) (k' : ModeState) (d' : Delay),
  d' < d -> p -PD- d' -PD> p' -> i -i- d' -i> i' -> k -ms- d' -ms> k' ->
  gotMsgStateEnt_urgent_noSyncNowA a p' i' k').

Inductive gotMsgStateEnt_urgent_delA : Entity -> Delay -> Entity -> Prop :=
  | gotMsgStateEnt_urgent_delA_c : forall (d : Delay) (p p' : ProcTerm) (l delta : Position)
    (i i' : Interface) (k k' : ModeState),
    p -PD- d -PD> p' -> i -i- d -i> i' -> k -ms- d -ms> k' ->
    displacement delta <= speedMax * d -> gotMsgStateEnt_urgent_noSyncA p i k d ->
    gotMsgStateEnt_urgent_delA ([| p , l , i , k |]) d ([| p' , addPos l delta, i' , k' |]).

(** Under fix A the target holds, even without reachableEnt. *)
Lemma gotMsgStateEnt_urgent_fixedA (e e' : Entity) (d : Delay) m l :
  gotMsgStateEnt m l e -> gotMsgStateEnt_urgent_delA e d e' -> False.
Proof.
  intros GS DL. inversion DL; subst.
  match goal with NS : gotMsgStateEnt_urgent_noSyncA _ _ _ _ |- _ =>
    destruct (NS (chanPos ;? [basePosition l])) as [NOW _] end.
  destruct NOW as [_ NP].
  - eapply gotMsgStateEnt_urgent_fix_core. eassumption.
  - apply (NP l). reflexivity.
Qed.
Print Assumptions gotMsgStateEnt_urgent_fixedA.
(* PROOF *)
Proof.
Admitted.
