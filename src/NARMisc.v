(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

From Stdlib Require Import Program.Equality.
Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs. 
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults. 
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.ProtAuxResults.

(* begin helpers for state_disj_paused_notifAbort *)
(* Given D : discActEnabled q a, where q is (bisimilar-free) concrete protocol
   state term, unfold q and invert every transition, closing the goal when q
   cannot perform a. *)
Ltac state_disj_paused_notifAbort_dae_contra D :=
  let q := fresh "q" in let TR := fresh "TR" in
  destruct D as [q TR];
  unfold rangeBad, currOK, abortOvlp, paused, tfsCurr, tfsStart, tfsBc,
    switchListen, switchBc, switchCurr, ovReady, ovWait, init in TR;
  repeat (match goal with [T : stepDiscProc _ _ _ |- _] =>
    inversion T; clear T; subst end).

(* Given RS : X p (with X p unfolding to p ~p~ q) and PU : discActEnabled p a,
   derive a contradiction when q cannot perform a. *)
Ltac state_disj_paused_notifAbort_bisim_contra RS PU :=
  let D := fresh "D" in
  lets D : bisim_dae RS PU; state_disj_paused_notifAbort_dae_contra D.
(* end helpers *)

Lemma state_disj_paused_notifAbort i n :
  pausedStateNet i n -> notifAbortPathNet i n -> False.
Proof.
  intros U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst.
  lets PU : paused_unpause_in PS. clear PS.
  inversion V1; subst;
  first [ match goal with [X : rangeBadStateProt _ _ |- _] => inversion X; subst end
        | match goal with [X : currOKStateProt _ _ |- _] => inversion X; subst end
        | match goal with [X : abortOvlpStateProt _ |- _] => inversion X; subst end ];
  match goal with [RS : _ p3 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_start : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsStartStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_bc : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> tfsBcStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

Lemma state_disj_tfsCurr_switchListen : forall (i : nat) (n : Network),
  tfsCurrStateNet i n -> switchListenStateNet i n -> False.
Proof.
  intros i n U V. inversion U as [e U1 U2]. inversion V as [e' V1 V2].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP.
  lets PU : tfsCurr_abort_in PS. clear PS.
  inversion V1; subst.
  match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end.
  match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end.
Qed.

(*The following string of results should be provable by lifting inter-component
relationships. Except the one with nextSince, not so sure there.*)
Lemma init_nextMode_net m i n :
  initStateNet m i n -> nextModeNet m i n. Admitted. (*4*)
(*+*)
Lemma ovWait_ovReady_nextMode_net i n (p : reachableNet n) :
  (forall m t x y, ovWaitStateNet m t x y i n ->
   nextModeNet m i n) /\
  (forall m t l, ovReadyStateNet m t l i n -> nextModeNet m i n).
Proof.
  split; intros.
  - eapply ComhCoq.NetAuxBasics.ovWaitState_nextMode_net; eassumption.
  - eapply ComhCoq.NetAuxBasics.ovWait_ovReady_nextMode_net
      with (x := zeroTime) (y := zeroTime); [exact p | right; eassumption].
Qed.
(*+*)
Lemma switchBc_nextMode_net m i n :
  switchBcStateNet m i n -> nextModeNet m i n. Admitted. (*4*)
(*+*)
Lemma switchCurr_nextSince_nextMode_net m t i n p :
  nextSince m t i n p ->
  switchCurrStateNet i n -> nextModeNet m i n. Admitted. (*4*)

(* begin helpers for nextSince_switchBc_modeEq *)
(** Given D : discActEnabled q a, where q is a concrete protocol state term,
unfold q and invert every transition, closing the goal when q cannot do a. *)
Ltac nextSince_switchBc_modeEq_dae_contra D :=
  let q := fresh "q" in let TR := fresh "TR" in
  destruct D as [q TR];
  unfold rangeBad, currOK, abortOvlp, paused, tfsCurr, tfsStart, tfsBc,
    switchListen, switchBc, switchCurr, ovReady, ovWait, init in TR;
  repeat (match goal with [T : stepDiscProc _ _ _ |- _] =>
    inversion T; clear T; subst end).

(** Given RS : X p (unfolding to p ~p~ q) and PU : discActEnabled p a,
derive a contradiction when q cannot perform a. *)
Ltac nextSince_switchBc_modeEq_bisim_contra RS PU :=
  let D := fresh "D" in
  lets D : bisim_dae RS PU; nextSince_switchBc_modeEq_dae_contra D.

(** Two next-mode facts about the same entity coincide. *)
Lemma nextSince_switchBc_modeEq_uniq m m' i n :
  nextModeNet m i n -> nextModeNet m' i n -> m = m'.
Proof.
  intros NM NM'. apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM'. destruct NM' as [e' [EIN' NME']].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  destruct e as [p l h k].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME'.
  rewrite NME in NME'. inversion NME'. reflexivity.
Qed.

(** Across a discrete step whose target is neither switchListen nor tfsBc,
the mode state is unchanged, so next modes before and after coincide. *)
Lemma nextSince_switchBc_modeEq_mst m m0 i n n' a :
  reachableNet n -> n -NA- a -NA> n' -> nextModeNet m i n ->
  nextModeNet m0 i n' -> ~ switchListenStateNet i n' ->
  ~ tfsBcStateNet i n' -> m = m0.
Proof.
  intros RN W NM NM0 NSL NTB.
  apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM0. destruct NM0 as [e0 [EIN0 NME0]].
  destruct e as [p l h k]. destruct e0 as [p0 l0 h0 k0].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME0.
  destruct (eqDecModeState k k0) as [EQ | NEQ].
  - subst. rewrite NME in NME0. inversion NME0. reflexivity.
  - exfalso.
    assert (mState_in_net k i n) as MS by (econstructor; eassumption).
    assert (mState_in_net k0 i n') as MS0 by (econstructor; eassumption).
    lets MSS : mState_switch_states RN NEQ W MS MS0.
    destruct MSS as [[_ TB] | [_ SL]]; [apply NTB | apply NSL]; assumption.
Qed.

(** A nextSince state is neither switchListen nor tfsBc. *)
Lemma nextSince_switchBc_modeEq_nss_not i n :
  nextSinceStateNet i n -> ~ switchListenStateNet i n /\ ~ tfsBcStateNet i n.
Proof.
  intro U. inversion U as [e U1 U2]. inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP U1 U.
  split; intro V; inversion V as [e' V1 V2];
  (assert (e' = [|p1 $||$ p2 $||$ p3, l, h, k|]) as EQ
    by (eapply entInNetUnique; eassumption)); subst e';
  inversion V1; subst;
  (match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end);
  (match goal with [RS : _ p2 |- _] =>
    first [lets PU : switchListen_unpause_out RS | lets PU : tfsBc_trans_out RS];
    clear RS end);
  inversion PS; clear PS; subst;
  (match goal with [RS : _ p2 |- _] =>
    nextSince_switchBc_modeEq_bisim_contra RS PU end).
Qed.

(** nextSince m implies that the next mode is m, by induction on nextSince,
comparing mode states across each discrete step. *)
Lemma nextSince_switchBc_modeEq_next m t i n p :
  nextSince m t i n p -> nextModeNet m i n.
Proof.
  intro NS. induction NS as [a i0 n0 n0' p0 w l t0 t0' x y PND OR OW
    | a t0 i0 n0 n0' p0 w NS IH NSS | d t0 i0 n0 n0' p0 w NS IH].
  - eapply ovWaitState_nextMode_net; [ | eassumption].
    eapply reachNetDisc; eassumption.
  - assert (reachableNet n0') as RN' by (eapply reachNetDisc; eassumption).
    lets NOT : nextSince_switchBc_modeEq_nss_not NSS. destruct NOT as [NSL NTB].
    lets NSN : nexSinceStateNet_cases NSS.
    destruct NSN as [OW | [OR | [SB | SC]]].
    + destruct OW as [m0 [t1 [x1 [y1 OW]]]].
      lets NM0 : ovWaitState_nextMode_net RN' OW.
      assert (m = m0) as EQ
        by (eapply nextSince_switchBc_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct OR as [m0 [t1 [l1 OR]]].
      assert (nextModeNet m0 i0 n0') as NM0.
      { eapply ComhCoq.NetAuxBasics.ovWait_ovReady_nextMode_net
          with (x := zeroTime) (y := zeroTime); [exact RN' | right; eassumption]. }
      assert (m = m0) as EQ
        by (eapply nextSince_switchBc_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct SB as [m0 SB].
      assert (nextModeNet m0 i0 n0') as NM0
        by (eapply switchBc_nextMode_net; eassumption).
      assert (m = m0) as EQ
        by (eapply nextSince_switchBc_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + eapply switchCurr_nextSince_nextMode_net; [ | eassumption].
      exact (nextSinceDisc _ _ _ _ _ _ _ w NS NSS).
  - eapply nextModeNet_del_pres; eassumption.
Qed.
(* end helpers *)

Lemma nextSince_switchBc_modeEq m m' t i n p :
  nextSince m t i n p -> switchBcStateNet m' i n -> m = m'.
Proof.
  intros NS SB.
  lets NM : nextSince_switchBc_modeEq_next NS.
  lets NM' : switchBc_nextMode_net SB.
  eapply nextSince_switchBc_modeEq_uniq; eassumption.
Qed.

(* begin helpers for nextSince_ovWait_modeEq *)
(** Two next-mode facts about the same entity coincide. *)
Lemma nextSince_ovWait_modeEq_uniq m m' i n :
  nextModeNet m i n -> nextModeNet m' i n -> m = m'.
Proof.
  intros NM NM'. apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM'. destruct NM' as [e' [EIN' NME']].
  assert (e' = e) as EQ by (eapply entInNetUnique; eassumption). subst e'.
  destruct e as [p l h k].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME'.
  rewrite NME in NME'. inversion NME'. reflexivity.
Qed.

(** Across a discrete step whose target is neither switchListen nor tfsBc,
the mode state is unchanged, so next modes before and after coincide. *)
Lemma nextSince_ovWait_modeEq_mst m m0 i n n' a :
  reachableNet n -> n -NA- a -NA> n' -> nextModeNet m i n ->
  nextModeNet m0 i n' -> ~ switchListenStateNet i n' ->
  ~ tfsBcStateNet i n' -> m = m0.
Proof.
  intros RN W NM NM0 NSL NTB.
  apply nextMode_ent_ex in NM. destruct NM as [e [EIN NME]].
  apply nextMode_ent_ex in NM0. destruct NM0 as [e0 [EIN0 NME0]].
  destruct e as [p l h k]. destruct e0 as [p0 l0 h0 k0].
  apply nextMode_ent_mState in NME. apply nextMode_ent_mState in NME0.
  destruct (eqDecModeState k k0) as [EQ | NEQ].
  - subst. rewrite NME in NME0. inversion NME0. reflexivity.
  - exfalso.
    assert (mState_in_net k i n) as MS by (econstructor; eassumption).
    assert (mState_in_net k0 i n') as MS0 by (econstructor; eassumption).
    lets MSS : mState_switch_states RN NEQ W MS MS0.
    destruct MSS as [[_ TB] | [_ SL]]; [apply NTB | apply NSL]; assumption.
Qed.

(** A nextSince state is neither switchListen nor tfsBc. *)
Lemma nextSince_ovWait_modeEq_nss_not i n :
  nextSinceStateNet i n -> ~ switchListenStateNet i n /\ ~ tfsBcStateNet i n.
Proof.
  intro U. inversion U as [e U1 U2]. inversion U1 as [p l h k PP]; subst.
  inversion PP as [p1 p2 p3 PS]; subst. clear PP U1 U.
  split; intro V; inversion V as [e' V1 V2];
  (assert (e' = [|p1 $||$ p2 $||$ p3, l, h, k|]) as EQ
    by (eapply entInNetUnique; eassumption)); subst e';
  inversion V1; subst;
  (match goal with [X : _ (p1 $||$ p2 $||$ p3) |- _] => inversion X; subst end);
  (match goal with [RS : _ p2 |- _] =>
    first [lets PU : switchListen_unpause_out RS | lets PU : tfsBc_trans_out RS];
    clear RS end);
  inversion PS; clear PS; subst;
  (match goal with [RS : _ p2 |- _] =>
    state_disj_paused_notifAbort_bisim_contra RS PU end).
Qed.

(** nextSince m implies that the next mode is m. Proved directly by induction
on nextSince, comparing mode states across each discrete step. *)
Lemma nextSince_ovWait_modeEq_next m t i n p :
  nextSince m t i n p -> nextModeNet m i n.
Proof.
  intro NS. induction NS as [a i0 n0 n0' p0 w l t0 t0' x y PND OR OW
    | a t0 i0 n0 n0' p0 w NS IH NSS | d t0 i0 n0 n0' p0 w NS IH].
  - eapply ovWaitState_nextMode_net; [ | eassumption].
    eapply reachNetDisc; eassumption.
  - assert (reachableNet n0') as RN' by (eapply reachNetDisc; eassumption).
    lets NOT : nextSince_ovWait_modeEq_nss_not NSS. destruct NOT as [NSL NTB].
    lets NSN : nexSinceStateNet_cases NSS.
    destruct NSN as [OW | [OR | [SB | SC]]].
    + destruct OW as [m0 [t1 [x1 [y1 OW]]]].
      lets NM0 : ovWaitState_nextMode_net RN' OW.
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct OR as [m0 [t1 [l1 OR]]].
      assert (nextModeNet m0 i0 n0') as NM0.
      { eapply ComhCoq.NetAuxBasics.ovWait_ovReady_nextMode_net
          with (x := zeroTime) (y := zeroTime); [exact RN' | right; eassumption]. }
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + destruct SB as [m0 SB].
      assert (nextModeNet m0 i0 n0') as NM0
        by (eapply switchBc_nextMode_net; eassumption).
      assert (m = m0) as EQ
        by (eapply nextSince_ovWait_modeEq_mst with (n := n0); eassumption).
      subst. assumption.
    + eapply switchCurr_nextSince_nextMode_net; [ | eassumption].
      exact (nextSinceDisc _ _ _ _ _ _ _ w NS NSS).
  - eapply nextModeNet_del_pres; eassumption.
Qed.
(* end helpers *)

Lemma nextSince_ovWait_modeEq m m' t t' x y i n p :
  nextSince m t i n p -> ovWaitStateNet m' t' x y i n -> m = m'.
Proof.
  intros NS OW.
  lets NM : nextSince_ovWait_modeEq_next NS.
  lets NM' : ovWaitState_nextMode_net p OW.
  eapply nextSince_ovWait_modeEq_uniq; eassumption.
Qed.
(*+PROBABLY NEED TO PROVE THESE TOGETHER FROM A MASTER "MUTUAL" RESULT+*)
(* begin helpers for nextSince_ovReaddy_modeEq *)
(** Two overlap-component state predicates holding for the same entity in the
same network reduce to both holding of the same overlap process.*)
Lemma nextSince_ovReaddy_modeEq_lift (X Y : ProcTerm -> Prop) i n :
  liftEntNet (liftProcEnt (liftOverlap X)) i n ->
  liftEntNet (liftProcEnt (liftOverlap Y)) i n ->
  (forall p, X p -> Y p -> False) -> False.
Proof.
  intros H1 H2 HXY.
  inversion H1 as [e1 E1 I1]; inversion H2 as [e2 E2 I2].
  assert (e1 = e2) as EQ by (eapply entInNetUnique; eassumption). subst e2.
  inversion E1 as [p l h k P1 EQ1]; subst.
  inversion E2 as [p' l' h' k' P2 EQ2]; subst.
  inversion P1 as [a b c X1 EQ3]; subst.
  inversion P2 as [a' b' c' Y1 EQ4]; subst.
  eapply HXY; eassumption.
Qed.

(** Given D : discActEnabled B a, with B a concrete overlap process body that
cannot perform a, closes the goal by exhaustive inversion.*)
Ltac nextSince_ovReaddy_modeEq_inv D :=
  let p' := fresh "p'" in let T := fresh "T" in
  destruct D as [p' T];
  cbv [ovWait ovReady tfsStart tfsNext tfsCurr tfsBc tfsListen switchCurr
    switchBc switchListen dormant init ovAbort] in T;
  repeat match goal with
  | T0 : _ -PA- _ -PA> _ |- _ => inversion T0; subst; clear T0
  end.

Lemma nextSince_ovReaddy_modeEq_ovReady_out m t l p :
  ovReadyState m t l p ->
  discActEnabled p (chanOutProc ;! [baseMode m, basePosition l]).
Proof. activation_tac. Qed.

Lemma nextSince_ovReaddy_modeEq_wr m t x y m' t' l i n :
  ovWaitStateNet m t x y i n -> ovReadyStateNet m' t' l i n -> False.
Proof.
  intros W R.
  apply (nextSince_ovReaddy_modeEq_lift (ovReadyState m' t' l)
    (ovWaitState m t x y) i n R W).
  intros p HR HW.
  lets D : nextSince_ovReaddy_modeEq_ovReady_out HR.
  eapply bisim_dae in D; [ | exact HW].
  nextSince_ovReaddy_modeEq_inv D.
Qed.
(* end helpers *)

Lemma nextSince_ovReaddy_modeEq m m' t t' l i n p :
  nextSince m t i n p -> ovReadyStateNet m' t' l i n -> m = m'.
Proof.
  intros NS. revert t' l. induction NS; intros t0 l0 OR.
  - exfalso. eapply nextSince_ovReaddy_modeEq_wr; eassumption.
  - match goal with W : _ -NA- _ -NA> _ |- _ =>
      lets PR : ovReady_prev_net OR W end.
    destruct PR as [OR' | [x0 [y0 OW]]].
    + eapply IHNS; eassumption.
    + eapply nextSince_ovWait_modeEq; eassumption.
  - eapply IHNS. eapply ovReady_del_pres_bkwd_net; eassumption.
Qed.

(*If an entity is tfs m, then it is in some tfsState.*)
Theorem tfs_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : tfs m t i n p -> tfsStateNet i n .
  intros.
  (*Induction on tfs.*)
  induction H.
  (*Base case can be shown by tfsStateNet constructor.*)
  invertClear H. econstructor;[ |apply H2]. invertClear H1.
  constructor. invertClear H. repeat constructor.
  (*assumption.
  (*Discrete inductive case follows from definition of tfs.*)
  assumption.
  (*Delay constructor follows from standard result (...del_pres_tfsState...) that
  delay preserves the tfsState predicate.*)
  erewrite <- tfsState_del_pres_net. apply IHtfs. apply w. Qed.*)
  Admitted. (*R*)

(*The tfs relation is at zero time when in the state tfsStart.*)
Lemma tfsStart_tfs_zero : forall (n : Network) (t : Time)
  (i : nat) (m : Mode) (p : reachableNet n),
  tfs m t i n p -> tfsStartStateNet i n -> t = zeroTime.
(*Proof: Similar to tfsNext_tfs_zero except can eliminate the backtrack
case because it implies the previous state is not tfs.*)
  intros. induction p. initNet_contra H0.
(*Discrete inductive case.*)
  dependent destruction H. reflexivity. 
  (*
  lets TPN : tfsStart_prev_net H1 s. elim_intro TPN TS OW.
  apply IHp; assumption. decompEx4 OW m' t' x y OW.
  apply tfs_rel_state in H. apply tfsState_elim_net in H.
  elimOr5 H TFS; try state_pred_elim_net OW TFS. invertClearAs2 TFS m'' TFS'.
  state_pred_elim_net OW TFS'.
(*Timed case: Follows from delay preservation of tfsStart and contraction
because tfsStart is urgent.*)
  lets DPT : del_pres_bkwd_tfsStart s H0.
  lets TU : tfsStart_urgent_net DPT s. inversion TU. Qed.*)
  Admitted. (*R*)

(*The tfs relation is at zero time when in the state tfsNext.*)
Lemma tfsNext_tfs_zero : forall (n : Network) (t : Time)
  (i : nat) (m : Mode) (p : reachableNet n),
  tfs m t i n p -> tfsNextStateNet m i n -> t = zeroTime.
  intros. induction p. initNet_contra H0.
  (*
  assert (tfs m t i n p) as TFP. dependent destruction H.
  state_pred_elim_net H H1. assumption.
  lets TPN : tfsNext_prev_net H0 s. elim_intro TPN TN TS.
  apply IHp; assumption.
  eapply tfsStart_tfs_zero. apply TFP. assumption.
(*Timed case: Follows delay preservation of tfsNext and contraction
because tfsNext is urgent.*)
  lets DPT : del_pres_bkwd_tfsNext s H0.
  lets TU : tfsNext_urgent_net DPT s. inversion TU. Qed.*)
  Admitted. (*R*)
  
Lemma currModeNet_switch_states n n' a m m' i :
  reachableNet n -> n -NA- a -NA> n' -> currModeNet m i n ->
  currModeNet m' i n' -> m <> m' ->
  (switchCurrStateNet i n /\ switchListenStateNet i n') \/
  (tfsCurrStateNet i n /\ tfsBcStateNet i n').
Proof.
  intros RN W CM CM' NEQ.
  apply currMode_ent_ex in CM. apply currMode_ent_ex in CM'.
  destruct CM as [e [EIN CE]]. destruct CM' as [e' [EIN' CE']].
  destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  assert (k <> k') as KNE.
  { intro EQ. subst k'. apply NEQ. rewrite <- CE, <- CE'. reflexivity. }
  destruct (mState_switch_states n n' i a k k' RN KNE W
    (minet k i n p l h EIN) (minet k' i n' p' l' h' EIN')) as [[A B] | [A B]].
  - right; split; assumption.
  - left; split; assumption.
Qed.
(*Proof: First of all use a tactic to generate the entities and the entity level
predicates, then do brute force elimination on these using a tactic leaving only
the desirable cases. Finally map the entity level results back up to the network
level using a tactic- netState_auto_tac or some variant?*)

(*tfs and tfsNext state simultaneously mean the mode parameters coincide*)
Lemma tfsNext_tfs_mode_eq : forall (n : Network) (t : Time)
  (i : nat) (m1 m2 : Mode) (p : reachableNet n),
  tfs m1 t i n p -> tfsNextStateNet m2 i n -> m1 = m2. 
(**Proof: Induction on tfs. BaseType case fails by state pred elim with tfsNext. Discrete inductive
case can use back-tracking to show that the previous state was either tfsStart or tfsNext. In the former
case, we use an auxiliary theorem (...write it...) like this one except instead of tfsNextStateNet m2 i n we
have tfsStartStateNet i n  and currModeNet m2. In the latter case, as in the delay inductive case (due to delay pres),
we can just apply I.H. For the discrete case, a result currModeNet_switch_states will do (the possible states contradict
the one given) to give the mode equality for this state. In the timed case, a delay preservation result
on currModeNet suffices*)
  Admitted. (*3*)

(* If the nextSince relation holds for some m t then the entity in question
is in a nextSinceState.*)
Theorem nextSince_rel_state (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : nextSince m t i n p -> nextSinceStateNet i n. 
  (*Induction on nextSince.*)
  intro U. induction U.
  (*The base case follows because ovWaitStateNet m t' x y i n' is a nextSinceStateNet.*)
  netprottrip H1 U q l0 h k.
  dofirst4 econstructor. apply U0. apply U.
  (*The discrete inductive case follows immediately from the definition of nextSince.*)
  assumption.
  (*The delay case follows by applying I.H. to the previous state to get nextSinceStateNet i n*)
  netprottrip IHU U q l h k.
  (*Then we show that delay preserves this state predicate
  (...del_pres_nextSinceState...).*)
  lets DX : net_del_elim U0 w. decompEx6 DX q' q0' q1' l' h' k' DE.
  andflat Q. dofirst3 econstructor. eapply del_pres_nextSinceState.
  apply U1. apply Q0. apply Q. Qed.

Lemma nextSince_next : forall (m : Mode) (t : Time) (i : nat)
  (n : Network) (p : reachableNet n),
  nextSince m t i n p -> nextModeNet m i n.
(**Proof: Strtengthen the statement to replace nextSince with nextSinceState.
Then split into the different nextSinceState cases and use an aux lemma for each.*)
  intros. lets NSR : nextSince_rel_state H.
  lets NSC : nexSinceStateNet_cases NSR. 
  lets OON : ovWait_ovReady_nextMode_net i n p. andflat OON.
  elimOr4 NSC NSC; ex_flat.
(*Case 1*)
  eapply OON0. replace m with x. eassumption. symmetry.
  eapply nextSince_ovWait_modeEq; eassumption. 
(*Case 2*)
  eapply OON1. replace m with x. eassumption. symmetry.
  eapply nextSince_ovReaddy_modeEq; eassumption.
(*Case 3*)
  eapply switchBc_nextMode_net. replace m with x. eassumption. symmetry.
  eapply nextSince_switchBc_modeEq; eassumption.
(*Case 4*)
  eapply switchCurr_nextSince_nextMode_net; eassumption.
  Qed.

(*Let's say two entities e1 and e2 are separated by a distance x. If e1 has delivered
message v to radius r t time units ago, and x + 2*Smax*t <= r, then e2 has received v t time
units ago.*)
Theorem delivered_received (n : Network) (v : list BaseType) (t : Time) (r x : Distance)
  (i j : nat) (p : reachableNet n) (l : Position) :
  delivered ([-v, l, r-]) t i n p -> i <> j ->
  distNet i j n x -> x + 2*speedMax*t <= r -> received v t j n p.
  intros. generalize dependent x.
  (*Induction on the proof of delivered.*)
  induction H; intros.
  (*In the base case, we have that n -v_l_r_i!-> n' and t = 0. So our last hypothesis
  becomes x <= r.*)
  simpl in H1. rewrite Rmult_0_r in H2. rewrite Rplus_0_r in H2.
  (*By analysing the transition from n to n', we can see from the semantics
  that this can only happen when all entities within range of entity i input the message,
  and all others ignore.*)
  addHyp (distNet_elim i j n' x H1). decompose [ex] H. clear H. decompose [and] H4.
  clear H4. rename x0 into e1'. rename x1 into e2'.
  addHyp (link_net_ent_disc_bkwd n n' e2' j (([-v, l, r-]) /! i) w H5).
  decompExAnd H3 e2 H4 Q.
  (*By x <= r, our guy is within range. Therefore he inputs.*)
  addHyp (inRange_out_input n n' v l r x i j e2 w H4 H0 H1 H2).
  invertClear H3. invertClear H7.
  (*Therefore, by the base case of received, he receives, with time
  parameter 0, as required.*)
  eapply receivedBase. apply H4. apply H8. apply H3.
  (*In the discrete case of induction, we get that the distance x doesn't change between n and n'*)
  addHyp (disc_pres_distNet_bkwd n n' a i j x w H1).
  (*The goal the follows easily by discrete inductive case of received
  and inductive hypothesis.*)
  constructor. apply (IHdelivered H0 x);assumption.
  (*In the timed case, we have delivered v r t i n p and so we can show
  delivered v r (t + d) i n' p'*)
  remember (reachNetDel n n' d p w) as p'.
  assert (delivered ([-v, l, r-]) (t +dt+ d) i n' p'). rewrite Heqp'. constructor.
  assumption.
  (*Let's call the distance at n' x'. Then we have that dist2d i j n' x' and x' + 2*Smax*(t + d) <= r*)
  rename x into x'.
  (*The latter rearranges to x' + 2*Smax*t + 2*Smax*d <= r.*)
  assert (nonneg (distance x') +
  2 * nonneg speedMax * nonneg (time t) + 2 * nonneg speedMax * pos (delay d)
  <= nonneg (distance r)). rewrite Rmult_assoc in H2. simpl in H2.
  repeat rewrite Rmult_plus_distr_l in H2. rewrite <- Rplus_assoc in H2.
  repeat rewrite <- Rmult_assoc in H2. assumption.
  (*But we can also prove that x <= x' + 2*Smax*d, where dist2d i i' n x.*)
  addHyp (del_link_distNet_bkwd n n' d i j x' w H1). invertClear H5.
  invertClear H6.
  (*Strategically adding 2*Smax*t to each side of the inequality we get
  x + 2*Smax*t <= x' + 2*Smax*t + 2*Smax*d*)
  apply (Rplus_le_compat_r (2*speedMax*t)) in H7.
  (*Now, from a previous result, this is in turn <= r. So x + 2*Smax*t <= r.*)
  assert (x + 2 * speedMax * t <= r). eapply Rle_trans. apply H7.
  eapply Rle_trans;[ |apply H2]. apply Req_le. simpl. ring.
  (*So we have enough information now to show from the I.H. that received v t j n p.*)
  assert (received v t j n p). apply (IHdelivered H0 x); assumption.
  (*And so by the delay constructor of received, we get received v (t + d) i' n p'.*)
  rewrite Heqp'. constructor. assumption.
  (*Note: The intuition here is that e1 and e2 could have been separated by at most
  x + 2*Smax*t t time units ago, due to the separation being x now, the maximum
  relative speed being 2*Smax and the time since the message delivery being t.*) 
  Qed. 

(*The currSince relation for mode m implies that the current mode we are now in is m.*)
Theorem currSince_curr (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : currSince m t i n p -> currModeNet m i n.
  intros.
  (*Induction on currSince.*)
  induction H.
  (*Base case follows from previous results.*)
  eapply switch_states_mState; try apply w; try assumption. eapply nextSince_next. 
  apply H.
  (*The discrete inductive case is straightforward: the definition of currSince includes in
  it that the currMode is m, so the goal follows immediately.*)
  assumption.
  (*Delay doesn't change the mode state, so I.H. will do.*)
  erewrite <- currModeNet_del_pres. apply IHcurrSince. apply w. 
  Qed.

(*If an entity is tfs t in the state tfsCurrState, then there is some t' such that
the mode transition guard for that entity is t' and the sum of t and t' is at most
trans m.*)
Theorem tfs_transGuard (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : 
  tfsCurrStateNet i n -> tfs m t i n p ->
  exists t', transGuard t' i n /\ t + t' <= trans m.
  intros.
  (**Proof: Induction on tfs.*)
  induction H0.
  (*The base case fails because the state is wrong.*)
  (*First we show that there is a mode state at i in n.*)
  apply False_ind. eapply state_disj_tfsCurr_start. apply H. assumption.
  (*In the discrete inductive case, we check whether or not the previous case was
  tfsCurrStateNet.*)
  addHyp (tfsCurrNet_dec i n). invertClear H2.
  (*If it was we can apply the IH.*)
  apply IHtfs in H3. invertClear H3. rename x into t'. invertClear H2.
  (*Now we can use t' as our witness because the mode state shouldn't have changed.*)
  exists t'. split;[ |assumption].
  addHyp (transGuard_elim t' i n H3). decompose [ex] H2. rename x into m1.
  rename x0 into m2.
  (*Then we show that there must be a mode state at i in n'*)
  remember (<| m1, m2, t' |>) as k. addHyp (mState_disc_pres n n' i a k w H6).
  invertClear H5. rename x into k'.
  (*Now, either the mode states are equal or they are not.*)
  addHyp (eqDecModeState k k'). invertClear H5.
  (*If they are equal, then the tranGuard property immediately follows.*)
  eapply transGuard_intro. rewrite <- H8 in H7. rewrite Heqk in H7. apply H7.
  (*Otherwise, the mode states are not equal. So the software component must have
  been in one of two states at n', because this is the only way that the mode state
  can change. However, the cases don't match, so this case is written off with
  contradiction.*)
  apply False_ind. lets H5 : mState_switch_states p H8 w H6 H7.
  invertClear H5; invertClear H9. eapply state_disj_tfsCurr_bc. apply H.
  assumption. eapply state_disj_tfsCurr_switchListen. apply H. assumption.
  (*So now we must deal with the case where the previous state wasn't tfsCurr.
  Here we can show (...PA::tracking...) that it was tfsNext and that the transition
  was an output to the mode state of the next mode.*)
  addHyp (tfsCurrStateNet_bktrk_net n n' i a H w). invertClear H2. contradiction H3.
  decompose [ex] H4. clear H4. rename x into m1. rename x0 into mF.
  decompose [and] H2. clear H2.
  (*Now, by previous knowledge we know that the mode transition time
  is less than or equal trans m.*)
  (*Also, we know from other theorems that tfs is 0 on entering this state.
  So the bound holds.*)
  addHyp (tfsNext_tfs_mode_eq n t i m m1 p H0 H4). rewrite <- H2 in H4.
  addHyp (tfsNext_tfs_zero n t i m p H0 H4). rewrite H5. simpl.
  exists (modeTransTime m1 mF x1). rewrite Rplus_0_l.
  generalize dependent x1. rewrite <- H2. intros. split.  
  eapply transGuard_intro. apply H7. apply modeTransTime_bound.
  (*Now, for the delay inductive case, we know that delay preserves tfsCurr*)
  addHyp (tfsCurrState_del_pres_net n n' d i w). addHyp H. rewrite <- H1 in H2.
  (*So we can apply I.H. to the previous state.*)
  apply IHtfs in H2. invertClear H2. rename x into t'. invertClear H3.
  (*Then we know that the transGuard decreases and the t from
  tfs increases proportionately, and so the sum remains the same.*)
  addHyp (transGuard_del n n' d t' i w H2). invertClear H3.
  remember (minusTime t' d x) as t0. exists t0. split. assumption.
  rewrite Heqt0. eapply Rle_trans;[ |apply H4]. apply Req_le.
  simpl. ring. Qed.

  
(*If an entity is tfs m for a time of t, then this t is bounded from above by trans m.*)
Theorem tfs_bound (n : Network) (m : Mode) (t : Time) (i : nat)
  (p : reachableNet n) : tfs m t i n p -> t <= trans m.
  intros.
  (*Induction on the proof of reachable.*)
  generalize dependent t. induction p; intros.
  (*The base case is easy because the base proof of reachability implies zero time
  which is less than any time.*)
  dependent destruction H. simpl. timeNonneg.
  (*The discrete inductive case is easy: either we have the base case of tfs, in
  which case the previous argument applies, or we just apply the I.H. and observe
  that the time hasn't changed.*)
  dependent destruction H. simpl. timeNonneg.
  apply IHp. assumption. addHyp H. rename H0 into Q.
  remember (reachNetDel n n' d p s) as p'. rewrite Heqp' in H.
  (*The timed case takes a bit more effort. First some preliminaries.*)
  dependent destruction H. simpl. timeNonneg.
  (*Now we apply (tfs_rel_state) and show that the middle software component must delay.*)
  addHyp (tfs_rel_state n m t i p H). invertClear H0. invertClear H1.
  invertClear H0. rewrite <- H4 in H3.
  addHyp (del_net_ent e i n n' d H2 s). rewrite <- H3 in H2.
  invertClear H0. rename x into e'. rewrite <- H3 in H5.
  (*Now do inversion on the tfsStates show that no time can pass for tfsListen, tfsBc,
  tfsNext and tfsStart (...EA::urgency...), contradicting the delay just shown*)
  invertClear H1.
  (*
  (*tfsStart*)
  apply False_ind. eapply tfsStartStateEnt_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*tfsNext*)
  apply False_ind. eapply tfsNext_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. apply H0.
  apply H5.
  (*tfsBc*)
  Focus 2. apply False_ind. eapply tfsBc_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*tfsListen*)
  Focus 2. apply False_ind. eapply tfsListen_urgent. eapply reachable_net_ent.
  apply p. apply H2. repeat constructor. assumption.
  apply H5.
  (*For tfsCurr use a special result (tfs_transGuard), to give us our bound.*)
  assert (tfsCurrStateNet i n). econstructor. constructor. constructor.
  apply H0. apply H2. 
  addHyp (tfsCurrState_del_pres_net n n' d i w). addHyp H1. rewrite H6 in H7.
  clear H6. rename H7 into H6.
  addHyp (tfs_transGuard n' m (t +dt+ d) i p' H6 Q). invertClear H7.
  rename x into t'. invertClear H8. eapply Rle_trans;[ | apply H9].
  apply Rplus_le_weaken_rr. timeNonneg. apply Rle_refl. Qed.*)
  Admitted. (*R*)



(*If v is timed out and outgoing, and the parent network makes a discrete transition,
then in the resultant network, v is either still timed out and outgoing or it has just
been delivered in this instant.*)
Theorem outgoing_timeout_disc (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) (l : Position) :
  outgoing v zeroTime i n ->
  outgoing v zeroTime i n' \/
  exists r, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
  introz U.
  (*Case analysis on the discrete action in question*)
  destruct a.
  (*In the case of output, we further check to see if the message payload output is v.*)
  destruct m as [v' l' r'].
  (*The only case where something is in the output list of an interface and not in the
  output list of the derivative is where the action linking the states is a broadcast
  of the message in question, which gives us delivered with timestamp 0 i.e. the RHS.*)
  (*For a of type tau, input or ignore, we can show that outgoing is preserved
  (...linking theorems + theorems on timed lists...), hence the LHS. *)
  Admitted. (*3*)
(**Proof: In steps above*)

(*AMALGAMATE WITH OTHERS- cull repetitions?*)
(* begin helpers for notifAbortPathNet_urgent *)
Lemma notifAbortPathNet_urgent_rangeBad_in m m0 p :
  rangeBadState m p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
Proof. activation_tac. Qed.

Lemma notifAbortPathNet_urgent_currOK_in m m0 p :
  currOKState m p -> discActEnabled p (chanMNext ;? [baseMode m0]).
Proof. activation_tac. Qed.

(** An entity whose listener is in the rangeBad state can always read the
current mode from its mode state, so it cannot delay. No reachability needed.*)
Lemma notifAbortPathNet_urgent_rangeBad_ent m p l h k e' d :
  rangeBadStateProt m p -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros RB ED. inversion RB as [p1 p2 p3 RB3 EQ]; subst.
  noSyncNow_tac.
  destruct (NS (chanMCurr ;? [baseMode (currModeMState k)])) as [_ DM].
  - apply parTriple_dae_intro3.
    exact (notifAbortPathNet_urgent_rangeBad_in m (currModeMState k) p3 RB3).
  - apply DM. exact (modeState_curr_enabled k).
Qed.

(** An entity whose listener is in the currOK state while its mode state has
a next mode m' can read m' on mNext, so it cannot delay.*)
Lemma notifAbortPathNet_urgent_currOK_ent m m' p l h k e' d :
  currOKStateProt m p -> nextModeMState k = Some m' ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros CO NM ED. inversion CO as [p1 p2 p3 CO3 EQ]; subst.
  noSyncNow_tac.
  destruct (NS (chanMNext ;? [baseMode m'])) as [_ DM].
  - apply parTriple_dae_intro3.
    exact (notifAbortPathNet_urgent_currOK_in m m' p3 CO3).
  - apply DM. destruct k as [m0 | m0 m1 t0]; simpl in NM; inversion NM; subst.
    econstructor. apply stepMsOutNext.
Qed.

Lemma notifAbortPathNet_urgent_ent e e' d :
  reachableEnt e -> notifAbortPathEnt e -> e -ED- d ->> e' -> False.
Proof.
  intros RE NA ED.
  inversion NA as [p l h k m m' RB CM NE NM | p l h k m' CO NM | p l h k AO]; subst.
  - eapply notifAbortPathNet_urgent_rangeBad_ent; eassumption.
  - eapply notifAbortPathNet_urgent_currOK_ent; eassumption.
  - eapply abortOvlpStateEnt_urgent; [exact RE | econstructor; exact AO | exact ED].
Qed.
(* end helpers *)

Lemma notifAbortPathNet_urgent (i : nat) (n n' : Network) (d : Delay) :
  reachableNet n -> notifAbortPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros RN NA W.
  destruct NA as [e NE EIN].
  destruct (del_net_ent e i n n' d EIN W) as [e' ED].
  eapply notifAbortPathNet_urgent_ent;
    [eapply reachable_net_ent; eassumption | exact NE | exact ED].
Qed.
(**Proof: lift from...EA::urgency... #urgent-path*)

Lemma notifBadPathNet_urgent i n n' d :
  notifBadPathNet i n -> n -ND- d -ND> n' -> False. Admitted. (*4*)
(**Proof: Follows from urgency results from all underlying component states.
Urgency holds in each one because there is always a synch possible with the
mode state or the overlap component. #urgent-path*)

Lemma msgBadPathNet_urgent (n n' : Network) (d : Delay) (i : nat) :
  msgBadPathNet i n -> n -ND- d -ND> n' -> False. Admitted. (*4*)
(**Proof: Lift urgency from EA urgency result. #urgent-path*)

(* begin helpers for msgAbort_paused_disj_net *)
Lemma msgAbort_paused_disj_net_unp q :
  pausedState q -> exists q', q -PA- chanUnpause *? -PA> q'.
Proof.
  intro P.
  assert (exists q', paused -PA- chanUnpause *? -PA> q') as [q0 TR].
  { eexists. unfold paused. constructor. reflexivity. }
  apply ComhCoq.ProcEquiv.bisim_symm in P.
  exact (bisim_disc_match _ _ _ _ P TR).
Qed.

Ltac msgAbort_paused_disj_net_inv :=
  repeat (match goal with V : _ -PA- _ -PA> _ |- _ => inversion V; subst; clear V end).
(* end helpers *)

Lemma msgAbort_paused_disj_net (i : nat) (n : Network) :
  msgAbortPathNet i n -> pausedStateNet i n -> False.
Proof.
  intros U V. destruct U as [e E1 E2]. destruct V as [e' E1' E2'].
  assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
  inversion E1' as [p l h k P]; subst.
  inversion P as [p1 p2 p3 P3]; subst.
  destruct (msgAbort_paused_disj_net_unp _ P3) as [q' TQ].
  inversion E1; subst.
  - match goal with H : gotMsgStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotMsgState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotMsg in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : gotRangeStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : gotRangeState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold gotRange in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : currCompStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : currCompState _ _ _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold currComp in TR. msgAbort_paused_disj_net_inv.
  - match goal with H : abortOvlpStateProt _ |- _ => inversion H; subst end.
    match goal with H : abortOvlpState _ |- _ =>
      let X := fresh "X" in lets X : bisim_disc_match H TQ; destruct X as [qq TR] end.
    clear - TR. unfold abortOvlp in TR. msgAbort_paused_disj_net_inv.
Qed.

(** If we are switching from a tfs state to a non tfs state, then we cannot be currSince.*)
Lemma tfsState_not_currSince (m : Mode) (t : Time) (i : nat) (n n' : Network)
  (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
  tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p. Admitted. (*3*)
(**Proof: Well, such a switch would mean we are going from tfsListen to dormant. And we can
show in a separate result that the tfsListen state implies that we're not currSince (which
in turn is because the tfsBc state is not currSince, which again in turn is because it is
preceded by an output on mCurr to switch the mode to some fail safe mode*)

Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  msgBadPathNet i n -> currModeNet m i n ->
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w). Admitted. (*3*)
(**Proof: Decompose msgBadPath. For all cases but one, fwd-tracking gives that either the state is preserved or the next state is also on the bad path, which is the LHS. The only exception is the badOvlp state, in which case the future may be the listening state. In this case though, fwd-tracking gives that the transition was an output on bad. Now, this must be matched in order for a synch to occur, and the only possible match is from the overlap component. There are 3 states in which this listens on bad. We can eliminate tfsListen and tfsCurr because they would imply that the entity is alredy tfs, which contradicts the assumption that it was on the msgBadPath: the definition of msgBadPath dictates that an entity is not tfs. Thus the remaining case is the transition from ovWait to tfsStart, giving the base case for tfs, which is the RHS exactly.*)

(*Needs some inter-component results for its proof*)
(** With a time parameter of 0, the tfs relation is preserved*)
Lemma tfs_zero_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  tfs m zeroTime i n p ->
  tfs m zeroTime i n' (reachNetDisc n n' a p w). Admitted. (*4*)
(**Proof: A state that is tfs with 0 time parameter must be either tfsStart, tfsNext or a guarded tfsCurr. It can be shown
by tracking that the first two cases are either preserved or go to the next case, ending at tfsCurr. This in turn is then delay
guarded, because a next mode has just been written to the mode state and the state can only be left by writing mCurr to the mode
state, which is only possible when this delay expires. But since the time parameter to tfs is 0, time can't pass, and so the entity
remains stuck in this state.*)

Lemma ovWait_nextSince_time (n : Network) (m : Mode) (x y t t1: Time) (i : nat)
  (p : reachableNet n) :
  ovWaitStateNet m t x y i n -> nextSince m t1 i n p -> period m - y <= t1.
(**Proof: Induction on next since. The base case gives that y = period m,
so the LHS of the inequality is 0 and trivially true. For the discrete
inductive case, neither t1 nor y changes, and so the I.H. suffices.
For the timed inductive case, y decreases and t1 increases proportionally.
Hence both sides of the inequality increase by the same amount, which can be
cancelled, and then the I.H. is applicable.*)
  intros OW NS. generalize dependent OW. induction NS; intro OW.
  lets OWT : ovReady_wait_track_net H0 H1 w. andflat EQ.
  invertClearAs2 EQ1 pr EQM. subst. clear EQ.
  (*
  state_pred_elim_net OW H1; unique_exps; my_applys_eq (Rle_refl 0); ring.
  (*Discrete inductive case*)
  lets OWP : ovWait_prev_net OW w. elim_intro OWP OWN ORX.
  apply IHNS; assumption.
  (*Now we case analyse on whether the previous state was ovReady or init.*)
  elim_intro ORX ORS IS.
  (*In the case of ovReady, we use ovReady_wait_track_net.*)
  invertClearAs2 ORS l OR.
  lets OWT : ovReady_wait_track_net OR OW w. andflat EQ. subst.
  Rminus_refl_simpl. timeNonneg.
  (*In the case of init, we show a contradiction with nextSince.*)
  apply nextSince_rel_state in NS. apply nexSinceStateNet_cases in NS.
  or_flat; ex_flat; [ | rename H0 into H1 |
  rename H0 into H1 | rename OR0 into H1];
  (state_pred_elim H1 IS; entnetuniq2 EN n; subst;
  state_pred_elim H3 H0; state_pred_elim H5 H7;
  state_pred_elim H11 H8).
  (*Delay inductive case*)
  assert (ovWaitStateNet m t x y i n) as ODP. eapply ovWait_del_pres_net.
  apply w. assumption. eapply Rle_trans. apply IHNS. assumption.
  simpl. Rplus_le_tac. apply Rlt_le. delPos. Qed.*)
  Admitted. (*R*)

(*The mode parameter of ovWait is the same as that of the nextSince relation if both hold.*)
Lemma nextSince_ovWait_modes_eq (n : Network) (m1 m2 : Mode) (t t1 x y : Time)
  (i : nat) (p : reachableNet n) :
  ovWaitStateNet m1 t x y i n -> nextSince m2 t1 i n p -> m1 = m2.
Proof.
  intros OW NS. symmetry. eapply nextSince_ovWait_modeEq; eassumption.
Qed.
(**Proof: Generalise the statement to include a similar statement about ovReadyState, then proceed by induction on nextSince. Back tracking
shows that ovReadySate and ovWaitState are predecessors to each other and so the I.H. carries forward. The base case follows directly from the
definition of nextSince.*)

Lemma bcWait_bktrk_net (n n' : Network) (m : Mode) (x : Time)
  (i : nat) (a : ActDiscNet) (p : reachableNet n) :
  bcWaitStateNet m x i n' -> n -NA- a -NA> n' ->
  bcWaitStateNet m x i n \/ (sleepingStateNet i n /\ x = zeroTime) \/
  (exists l, bcReadyStateNet m l i n /\ x = period m /\
  sent [baseMode m, basePosition l] zeroTime i n p). Admitted. (*4*)
(**Proof: Lift back tracking result.*)

Lemma msgAbortPathNet_urgent i n n' d :
  reachableNet n -> msgAbortPathNet i n -> n -ND- d -ND> n' -> False.
  intros. inversion H. link_netentdelfwd_tac e' LD.
  assert (reachableEnt e) as RE. eapply reachable_net_ent; eassumption.
  eapply msgAbortPathEnt_urgent; eassumption. Qed.
(**Proof: Synchronisation is always possible for the msgAbortPath states between the
listener component and either the position, the mode state or the overlap component.
Hence a delay would violate the noSynch property, and so cannot exist.*)

(*LOCAL TIDY*)

(** The notifBadPathNet relation can be broken down into the following cases.*)
Lemma notifBadPathNet_cases m i n :
  notifBadPathNet i n -> currModeNet m i n ->
  rangeBadStateNet m i n \/
  badOvlpStateNet i n.
  (*Proof: Similar to nexSinceStateNet_cases.*)
  intros. rename H0 into CMN. inversion H.
  inversion H0.
  apply currMode_ent_ex in CMN. ex_flat. and_flat.
  subst. entnetuniq2 EN n. subst. 
  left. eexists;[ | apply H1]. simpl.
  econstructor. assumption.
  subst. right. econstructor;[ | apply H1]. subst.
  constructor. assumption. Qed.

Lemma rangeBad_notifBad_net m i n :
  rangeBadStateNet m i n -> notifBadPathNet i n.
  Admitted. (*#notifBadNetLift #complexNetLift*)

Lemma badOvlp_notifBad_net i n :
  badOvlpStateNet i n -> notifBadPathNet i n.
Proof.
  intro H. destruct H as [e H1 H2]. destruct H1 as [p l h k H3].
  econstructor; [ | apply H2]. apply nbpBad. exact H3.
Qed.

Lemma ovReady_nextSince_state m t l i n :
  ovReadyStateNet m t l i n -> nextSinceStateNet i n.
Proof.
  intro H. destruct H as [e H1 H2]. destruct H1 as [p l' h k H3].
  inversion H3; subst.
  econstructor; [ | apply H2]. constructor. constructor.
  eapply nexsOvrSt. eassumption.
Qed.

(*-LOCAL TIDY*)