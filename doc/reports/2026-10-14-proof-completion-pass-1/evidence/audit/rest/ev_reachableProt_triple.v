(* HELPERS *)
(* Counterexample: procProtocol inputs on chanBad (the dormant branch
   [chanBad? tfsStartN]) and the overlap component becomes tfsStartN, which is
   neither dormantState nor ovWaitState, so the result is not a protocolState. *)
Ltac reachableProt_triple_kill :=
  repeat match goal with
  | H : false = true |- _ => discriminate H
  | H : context [varEqDec ?x ?y] |- _ => destruct (varEqDec x y); simpl in H
  | H : context [varEq ?x ?y] |- _ => destruct (varEq x y); simpl in H
  | H : context [update] |- _ => unfold update in H; simpl in H
  | H : evalBoolExpFunTot _ = true |- _ => unfold evalBoolExpFunTot in H; simpl in H
  | H : stepProc _ _ _ |- _ => inversion H; subst; clear H
  | H : def _ = (_, _) |- _ => simpl in H; inversion H; subst; clear H
  | H : stepDiscProc (liftNameProc _) _ _ |- _ => unfold liftNameProc in H
  | H : stepDiscProc (app _ _) _ _ |- _ => inversion H; subst; clear H
  | H : stepDiscProc (subProcTerm _ _) _ _ |- _ => progress (simpl in H)
  | H : stepDiscProc (inPrefix _ _ _) _ _ |- _ => inversion H; subst; clear H
  | H : stepDiscProc (outPrefix _ _ _) _ _ |- _ => inversion H; subst; clear H
  | H : stepDiscProc (sum _ _) _ _ |- _ => inversion H; subst; clear H
  | H : stepDiscProc (ifThen _ _) _ _ |- _ => inversion H; subst; clear H
  end.

Lemma reachableProt_triple_cex_step :
  procProtocol -PA- chanBad ;? [] -PA> (sleeping $||$ tfsStartN $||$ listening).
Proof.
  unfold procProtocol. apply stepDpParR. apply stepDpParL. unfold dormant.
  apply stepDpChoiceR.
  change (liftNameProc tfsStartN) with
    (subProcTerm (listsToSub [] (listBaselistExp [])) tfsStartN).
  apply stepDpIn. reflexivity.
Qed.

Lemma reachableProt_triple_cex_not_ovlp : ~ overlapState tfsStartN.
Proof.
  intro H. destruct H as [D | m t x y W].
  - unfold dormantState in D. destruct D as [_ B].
    assert (S0 : exists q', dormant -P- chanAbort ;? [] -P> q').
    { eexists. apply stepPDisc. unfold dormant. apply stepDpChoiceL.
      apply stepDpChoiceR. apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold ovWaitState in W. destruct W as [_ B].
    assert (S0 : exists q', ovWait m t x y -P- chanAbort ;? [] -P> q').
    { eexists. apply stepPDisc. unfold ovWait. apply stepDpChoiceL.
      apply stepDpChoiceL. apply stepDpChoiceL. apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
Qed.

Lemma reachableProt_triple_cex :
  reachableProt (sleeping $||$ tfsStartN $||$ listening) /\
  ~ protocolState (sleeping $||$ tfsStartN $||$ listening).
Proof.
  split.
  - eapply reachprDisc. apply reachprBase. apply reachableProt_triple_cex_step.
  - intro H. inversion H; subst. apply reachableProt_triple_cex_not_ovlp. assumption.
Qed.

Lemma reachableProt_triple_false :
  ~ (forall p, reachableProt p -> protocolState p).
Proof.
  intro H. destruct reachableProt_triple_cex as [R N]. apply N, H, R.
Qed.

(* Second, independent gap: the listener can input on chanPause and become
   pausedN, which is not covered by listenerState either. *)
Lemma reachableProt_triple_cex2_step :
  procProtocol -PA- chanPause ;? [] -PA> (sleeping $||$ dormant $||$ pausedN).
Proof.
  unfold procProtocol. apply stepDpParR. apply stepDpParR. unfold listening.
  apply stepDpChoiceL. apply stepDpChoiceR.
  change (liftNameProc pausedN) with
    (subProcTerm (listsToSub [] (listBaselistExp [])) pausedN).
  apply stepDpIn. reflexivity.
Qed.

Lemma reachableProt_triple_cex2_not_list : ~ listenerState pausedN.
Proof.
  intro H. destruct H as [L | m R | m C | A | Bd | m r C].
  - unfold listeningState in L. destruct L as [_ B].
    assert (S0 : exists q', listening -P- chanPause ;? [] -P> q').
    { eexists. apply stepPDisc. unfold listening. apply stepDpChoiceL.
      apply stepDpChoiceR. apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold rangeBadState in R. destruct R as [_ B].
    assert (S0 : exists q', rangeBad m -P- chanMCurr ;? [baseMode m] -P> q').
    { eexists. apply stepPDisc. unfold rangeBad. apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold currOKState in C. destruct C as [_ B].
    assert (S0 : exists q', currOK m -P- chanMStable ;? [] -P> q').
    { eexists. apply stepPDisc. unfold currOK. apply stepDpChoiceL.
      apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold abortOvlpState in A. destruct A as [_ B].
    assert (S0 : exists q', abortOvlp -P- chanAbort ;! [] -P> q').
    { eexists. apply stepPDisc. unfold abortOvlp. apply stepDpOut. constructor. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold badOvlpState in Bd. destruct Bd as [_ B].
    assert (S0 : exists q', badOvlp -P- chanBad ;! [] -P> q').
    { eexists. apply stepPDisc. unfold badOvlp. apply stepDpOut. constructor. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
  - unfold currCompState in C. destruct C as [_ B].
    assert (S0 : exists q', currComp m r -P- chanMStable ;? [] -P> q').
    { eexists. apply stepPDisc. unfold currComp. apply stepDpChoiceL.
      apply stepDpIn. reflexivity. }
    destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
    reachableProt_triple_kill.
Qed.

Lemma reachableProt_triple_cex2 :
  reachableProt (sleeping $||$ dormant $||$ pausedN) /\
  ~ protocolState (sleeping $||$ dormant $||$ pausedN).
Proof.
  split.
  - eapply reachprDisc. apply reachprBase. apply reachableProt_triple_cex2_step.
  - intro H. inversion H; subst. apply reachableProt_triple_cex2_not_list. assumption.
Qed.
(* Third, typing gap: process-level inputs are unconstrained, so an ill-typed
   value (a Time where a Mode/Distance is expected) can be input on chanAN.  The
   listener then reaches a checkRange whose two guards both evaluate to false:
   a state with NO discrete transitions.  Every named listener state has an
   enabled discrete action, so no completion of listenerState by named states
   with Mode/Distance/Position parameters can cover it. *)
Definition reachableProt_triple_stuck : ProcTerm :=
  subProcTerm (listsToSub (vR :: vM'' :: nil)
    (listBaselistExp (baseTime zeroTime :: baseTime zeroTime :: nil)))
    (checkRangeN $(eVar vM'' :: eVar vR :: nil)$).

Lemma reachableProt_triple_cex3_step :
  procProtocol -PA- chanAN ;? (baseTime zeroTime :: baseTime zeroTime :: nil) -PA>
  (sleeping $||$ dormant $||$ reachableProt_triple_stuck).
Proof.
  unfold procProtocol, reachableProt_triple_stuck. apply stepDpParR. apply stepDpParR.
  unfold listening. apply stepDpChoiceL. apply stepDpChoiceL. apply stepDpChoiceL.
  apply stepDpIn. reflexivity.
Qed.

Lemma reachableProt_triple_stuck_dead a q :
  ~ (reachableProt_triple_stuck -PA- a -PA> q).
Proof.
  intro H. unfold reachableProt_triple_stuck in H. reachableProt_triple_kill.
Qed.

Lemma reachableProt_triple_cex3 :
  reachableProt (sleeping $||$ dormant $||$ reachableProt_triple_stuck) /\
  ~ protocolState (sleeping $||$ dormant $||$ reachableProt_triple_stuck).
Proof.
  split.
  - eapply reachprDisc. apply reachprBase. apply reachableProt_triple_cex3_step.
  - intro H. inversion H; subst.
    match goal with H : listenerState _ |- _ => rename H into HL end.
    destruct HL as [L | m R | m C | A | Bd | m r C].
    + destruct L as [_ B].
      assert (S0 : exists q', listening -P- chanPause ;? [] -P> q').
      { eexists. apply stepPDisc. unfold listening. apply stepDpChoiceL.
        apply stepDpChoiceR. apply stepDpIn. reflexivity. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
    + destruct R as [_ B].
      assert (S0 : exists q', rangeBad m -P- chanMCurr ;? [baseMode m] -P> q').
      { eexists. apply stepPDisc. unfold rangeBad. apply stepDpIn. reflexivity. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
    + destruct C as [_ B].
      assert (S0 : exists q', currOK m -P- chanMStable ;? [] -P> q').
      { eexists. apply stepPDisc. unfold currOK. apply stepDpChoiceL.
        apply stepDpIn. reflexivity. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
    + destruct A as [_ B].
      assert (S0 : exists q', abortOvlp -P- chanAbort ;! [] -P> q').
      { eexists. apply stepPDisc. unfold abortOvlp. apply stepDpOut. constructor. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
    + destruct Bd as [_ B].
      assert (S0 : exists q', badOvlp -P- chanBad ;! [] -P> q').
      { eexists. apply stepPDisc. unfold badOvlp. apply stepDpOut. constructor. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
    + destruct C as [_ B].
      assert (S0 : exists q', currComp m r -P- chanMStable ;? [] -P> q').
      { eexists. apply stepPDisc. unfold currComp. apply stepDpChoiceL.
        apply stepDpIn. reflexivity. }
      destruct S0 as [q' S0]. apply B in S0. destruct S0 as [q [S _]].
      inversion S; subst. eapply reachableProt_triple_stuck_dead; eassumption.
Qed.

(* Suggested fix, validated: component predicates as closure of the initial
   component under the component-level semantics. *)
Inductive reachableProt_triple_compReach (p0 : ProcTerm) : ProcTerm -> Prop :=
  | rptcr_base : reachableProt_triple_compReach p0 p0
  | rptcr_disc p p' a : reachableProt_triple_compReach p0 p ->
      p -PA- a -PA> p' -> reachableProt_triple_compReach p0 p'
  | rptcr_del p p' d : reachableProt_triple_compReach p0 p ->
      p -PD- d -PD> p' -> reachableProt_triple_compReach p0 p'.

Lemma reachableProt_triple_fix p : reachableProt p ->
  exists p1 p2 p3, p = p1 $||$ p2 $||$ p3 /\
    reachableProt_triple_compReach sleeping p1 /\
    reachableProt_triple_compReach dormant p2 /\
    reachableProt_triple_compReach listening p3.
Proof.
  induction 1 as [ | p p' a R IH S | p p' d R IH S].
  - exists sleeping. exists dormant. exists listening. repeat split; constructor.
  - destruct IH as (p1 & p2 & p3 & E & C1 & C2 & C3). subst p.
    inversion S; subst;
    repeat match goal with
      | H : p2 $||$ p3 -PA- _ -PA> _ |- _ => inversion H; subst; clear H
    end;
    do 3 eexists; (split; [reflexivity | ]);
    repeat split; first [eassumption | eapply rptcr_disc; eassumption].
  - destruct IH as (p1 & p2 & p3 & E & C1 & C2 & C3). subst p.
    inversion S; subst.
    match goal with H : p2 $||$ p3 -PD- _ -PD> _ |- _ => inversion H; subst end.
    do 3 eexists; split; [reflexivity | ].
    repeat split; eapply rptcr_del; eassumption.
Qed.

(* PROOF *)
Proof.
Admitted.
