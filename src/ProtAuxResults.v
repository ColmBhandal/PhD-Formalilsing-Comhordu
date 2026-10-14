(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import ComhCoq.Extras.LibTactics.

(***************************** Specialised Imports *****************************)

Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProcEquiv.

(****************** (TIDY?) General Stuff ******************)

Ltac invert_def := match goal with [ U : def _ = (_, _) |- _] =>
  invertClear U; subst end.

Ltac invert_trans := match goal with [P : _ -PA- _ -PA> _ |- _]
  => invertClear P; subst end.

Lemma subProc_id_eq p : subProcTerm idSubst p = p.
  induction p; try simpl; try rewrite resetPreservesId;
  try rewrite idSubBoolExp;
  try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
  try rewrite idSubList; try rewrite idSubExp; try reflexivity.
  Qed.

Ltac clean_proc_trans := match goal with [U : _ -PA- _ -PA> _ |- _] =>
  clean_proc_hyp U end.

(** Given some application process in the context, this tactic performs inversion and
some cleanup on this until it is in the form of a process body as the source.*)
Ltac invert_app_trans := match goal with
  | [U : _ $( _ )$ -PA- _ -PA> _ |- _] => invertClear U; invert_def; clean_proc_trans
  | [U : liftNameProc _ -PA- _ -PA> _ |- _] => invertClear U; invert_def; clean_proc_trans
  end. 

Lemma dae_outPfx c l v p :
  evalExpLists l v -> discActEnabled (c $<l>$! p) (c;! v). intro X.
  econstructor. constructor. assumption. Qed.

Lemma dae_inPfx c l v p :
  length l = length v -> discActEnabled (c $<l>$? p) (c;? v).
  intro W. econstructor. constructor. symmetry. assumption. Qed.

Ltac update_eval := match goal with [H : ?e |_| ?m |- update _ ?x ?e ?x |_| ?m]
  => rewrite updateAppEq; apply H end.

(*Converts a hypothesis of an action for p1 or p2, into a hypothesis
of the same action by p1 + p2*)
Ltac lift_act_sum p1 p2 :=
  match goal with
  | [V : p1 -PA- ?a -PA> ?p' |- _] => apply (stepDpChoiceL p1 p2) in V
  | [V : p2 -PA- ?a -PA> ?p' |- _] => apply (stepDpChoiceR p1 p2) in V
  end.

(*Generates a trivial list of base values of the specified length. The list
just consists of a string of zeros (times).*)
Fixpoint genBaseList (n : nat) : list BaseType :=
  match n with
  | 0 => []
  | S n' => (baseTime zeroTime) :: (genBaseList n')
  end.

(*Converts a hypothesis of an action for p into one for b $> p, given that
evalBoolExp b true is a hypothesis.*)
Ltac lift_act_then b p := match goal with 
  [V1 : p -PA- ?a -PA> ?p', V2 : evalBoolExpFunTot b = true |- _] =>
  let V := fresh in rename V1 into V;
  lets V1 : stepDpThen V V2; clear V end.

(*An alternative characterisation of the discrete transition rule for application processes,
where the equality as a hypothesis is removed.*)
Lemma stepDpApp_alt : forall (n : Name) (l2 : list Exp) (p' : ProcTerm) (a : DiscAct),
  stepDiscProc (subProcTerm (listsToSub (fst (def n)) l2) (snd (def n))) a p' ->
  stepDiscProc (app n l2) a p'. intros. remember (def n). destruct p. eapply stepDpApp.
  rewrite <- Heqp. reflexivity. apply H. Qed.

(*Converts a hypothesis of an action on the body of n applied to x to a
hypothesis on the application process (n x)*)
Ltac lift_act_app h l2 :=
  match goal with
  | [V : (subProcTerm (listsToSub (fst (def h)) l2) (snd (def h))) -PA- _ -PA> _ |- _] =>
    apply stepDpApp_alt in V
  end.

Lemma genBaseList_length A (l : list A) :
  length (genBaseList (length l)) = length l. induction l.
  reflexivity. simpl. f_equal. assumption. Qed.

(*Generate all the discrete actions for some process p as hypotheses. Might leave some
boolean equalities over as contradictions to prove. Note: a posssilbe side-effect
of using this tactic is that any hypothesised actions on sub-terms of p will probably
be converted to actions on p. E.g. if we have H : p1 -a-> p' and then we do
gen_disc_acts (p1 + p2), we'll end up with H : p1 + p2 -a-> p'. Also this tactic hasn't
been written to work with parallel constructs, though this functionality could easily
be added.*)
Ltac gen_disc_acts p := 
  match p with
  | ?c $< ?l >$? ?p' => let V := fresh in
    assert (p -PA- c ;? genBaseList (length l) -PA>
    subProcTerm (listsToSub l (listBaselistExp (genBaseList (length l)))) p');
    [constructor; reflexivity | ]; remove_resets_hyp V; remove_updates_hyp V
  | ?c $< ?l >$! ?p' =>
    let EEL := fresh in let EELEQ := fresh in
    remember (evalExpListsFun l) as EEL eqn:EELEQ;
    destruct EEL; try solve [inversion EELEQ];
    match type of EELEQ with
    | Some ?l' = _ =>
      symmetry in EELEQ; assert (p -PA- c ;! l' -PA> p');
      [apply evalExpListsFunRel in EELEQ; econstructor;
      eassumption | ]; inversion EELEQ; subst
    | _ => idtac
    end; clear EELEQ
  | ?b $> ?p' =>
    let EEL := fresh in let EELEQ := fresh in
    remember (evalBoolExpFunTot b) as EEL eqn:EELEQ;
    destruct EEL; try solve [inversion EELEQ];
    match type of EELEQ with
    | true = _ => 
      symmetry in EELEQ; gen_disc_acts p'; lift_act_then b p'; clear EELEQ
    | _ => false
    end
  | ?p1 $+$ ?p2 => gen_disc_acts p1; gen_disc_acts p2; repeat lift_act_sum p1 p2
  | ?h $( ?l2 )$ => gen_disc_acts (subProcTerm (listsToSub (fst (def h)) l2) (snd (def h)));
    repeat lift_act_app h l2
  | subProcTerm ?s ?p' =>
    let p'' := fresh "p" in let Hp1 := fresh "Hp1" in 
    let Hp2 := fresh "Hp2" in
    remember p as p'' eqn:Hp1; lets Hp2 : Hp1; simpl in Hp2;
    remove_resets_hyp Hp2; remove_updates_hyp Hp2;
    match type of Hp2 with _ = ?q => gen_disc_acts q end;
    symmetry in Hp2; subst_all Hp2; subst_all Hp1
  | $< ?e >$ ?p' => idtac
  end.

(*If p and q are bisimlar, and p can do an action, then so can q.*)
Lemma bisim_disc_match p p' q a : p ~p~ q -> p -PA- a -PA> p' ->
  exists q', q -PA- a -PA> q'. intros. inversion H.
  apply stepPDisc in H0. apply H1 in H0. ex_flat. and_flat.
  exists x. inversion AND. assumption. Qed.

(*A richer inversion on a transition that tries to get rid of definition hypotheses
and clean up some substitution stuff.*)
Ltac invert_trans_rich := invert_trans; try invert_def; clean_proc_trans.

(*Given a hypothesis V1 which says p ~ q, this tactic finds a hypotheses
of the form p -a> p', applies the bisimulation to yield the same for q, and then
tries to solve the goal by contradiction on this q-transition. If the contradiction
fails, then the tactic moves on to the next p-transition, and fails when there are
no more p-transitions left.*)
Ltac bisim_contra_rec V1 :=
  match type of V1 with ?p ~p~ ?q =>
  match goal with [V2 : p -PA- _ -PA> _ |- _] =>
  eapply bisim_disc_match in V2; [ | apply V1];
  let q' := fresh "q'" in let TR := fresh in
  invertClearAs2 V2 q' TR; first [
  solve [clear - TR; repeat invert_trans_rich]
  | bisim_contra_rec V1]
  end
  end.

(*Tried to solve by contradiction the assumption that two processes
are bisimilar, by generating the action of one, and trying to contradict
with the other. The parameter V1 that is passed in is a hypothesis of
bisimilarity between two process. Note that the contradiction generated
is only one-way.*)
Ltac bisim_contra V1 :=
  match type of V1 with ?p ~p~ ?q =>
  gen_disc_acts p; bisim_contra_rec V1
  end.

(*-TIDY?*)

(*TIDY*)

(*Generates a bisimilarity via transitivity by combining two hypotheses
with the bisim_trans result. Works even if the order of one of the 
bisimilarities in the hypotheses is flipped- uses symmetry in this case.
The new bisimilarity is named "BT"- or a fresh instance thereof.*)
Ltac bisim_trans_tac BT :=
  match goal with
  | [V : ?p ~p~ ?x, V1 : ?p ~p~ ?y |- _] =>
    assert (x ~p~ y) as BT; [eapply bisim_trans; [apply bisim_symm | ];
    eassumption | ]
  | [V : ?x ~p~ ?p, V1 : ?p ~p~ ?y |- _] =>
    assert (x ~p~ y) as BT; [eapply bisim_trans; eassumption | ]
  end.
  
(*Every time something of the form P -P- a -P> P' is encountered as a
hypotheses it is inverted and cleared, leaving the underlying discrete
or timed transition that gave rise to it.*)
Ltac invert_steps := repeat
  (match goal with [V : _ -P- _ -P> _ |- _] =>
  invertClear V end; subst).

(*-TIDY*)

(*TOGO: ProcEquiv, bisimulation*)

Lemma bisim_dae p q a : p ~p~ q -> discActEnabled p a ->
  discActEnabled q a. introz U. inversion U0.
  apply stepPDisc in H. apply U in H. exand_flat.
  eexists. inversion AND. eassumption. Qed.

(*-TOGO*)

(****************** Activation ******************)
(**Results about whether certain actions are enabled or not.
Activation results take a p and a predicate on p, and infer
that a certain action is available to p.*)

(*** Activation tactic stuff ***)

Ltac activation_pre_tac :=
  let U := fresh in 
  intro U; eapply bisim_dae; [apply bisim_symm; apply U | ];
  match goal with [ |- discActEnabled ?p ?a] =>
    match p with
    | ?p' => unfold p'
    | ?p' ?x1 => unfold p'
    | ?p' ?x1 ?x2 => unfold p'
    | ?p' ?x1 ?x2 ?x3 => unfold p'
    | ?p' ?x1 ?x2 ?x3 ?x4 => unfold p'
    | ?p' ?x1 ?x2 ?x3 ?x4 ?x5 => unfold p'
    end
  end.

Ltac activation_post_tac :=
  match goal with
  [ |- discActEnabled ?p ?a] => 
    match p with
    (*For sum, recursively go left and see if it succeeds, else go right.*)
    | _ $< _ >$ ? _  => apply dae_inPfx; reflexivity
    | _ $< _ >$ ! _  => apply dae_outPfx; constructor
    | ?p1 $+$ ?p2 => first [solve [apply daeSumL; activation_post_tac] |
      solve [apply daeSumR; activation_post_tac]]
    end
  end; repeat constructor.

Ltac activation_tac := activation_pre_tac; activation_post_tac.

(*** Results ***)

Lemma bcReady_outProc_out m l p :
  bcReadyState m l p -> discActEnabled p (chanOutProc ;! [baseMode m, basePosition l]).
  activation_tac. Qed.

Lemma tfsStart_mCurr_in (p : ProcTerm) (m : Mode) : tfsStartState p ->
  discActEnabled p (chanMCurr ;? [baseMode m]). activation_tac. Qed.

Lemma tfsNext_mStable_out (p : ProcTerm) (m : Mode) : tfsNextState m p ->
  discActEnabled p (chanMStable *!). activation_tac. Qed.

Lemma tfsNext_mNext_out (p : ProcTerm) (m : Mode) : tfsNextState m p ->
  discActEnabled p (chanMNext ;! ([baseMode (failSafeSucc m)])).
  activation_tac; apply daeSumL; apply dae_outPfx; constructor;
  constructor; try rewrite updateAppEq; assumption; constructor. Qed.

Lemma switchCurr_mCurr_out (p : ProcTerm) : switchCurrState p ->
  discActEnabled p (chanMCurr *!). activation_tac. Qed.

Lemma switchListen_unpause_out (p : ProcTerm) : switchListenState p ->
  discActEnabled p (chanUnpause *!). activation_tac. Qed.

Lemma tfsCurr_bad_in (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma tfsCurr_abort_in (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma tfsCurr_mCurr_out (p : ProcTerm) : tfsCurrState p ->
  discActEnabled p (chanMCurr *!). activation_tac. Qed.

Lemma tfsListen_bad_in (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma tfsListen_abort_in (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma tfsListen_unpause_out (p : ProcTerm) : tfsListenState p ->
  discActEnabled p (chanUnpause *!). activation_tac. Qed.

Lemma dormant_bad_in (p : ProcTerm) : dormantState p ->
  discActEnabled p (chanBad *?). activation_tac. Qed.

Lemma dormant_abort_in (p : ProcTerm) : dormantState p ->
  discActEnabled p (chanAbort *?). activation_tac. Qed.

Lemma dormant_mNext_in (p : ProcTerm) (m : Mode) : dormantState p ->
  discActEnabled p (chanMNext ;? [baseMode m]). activation_tac.
  Qed.

Lemma switchBc_wake_out m p : switchBcState m p ->
  discActEnabled p (chanWake ;! [baseMode m]). activation_tac. Qed.

Lemma sleeping_wake_in m p : sleepingState p ->
  discActEnabled p (chanWake ;? [baseMode m]). activation_tac. Qed.

Lemma bcWait_wake_in m m' x p : bcWaitState m' x p ->
  discActEnabled p (chanWake ;? [baseMode m]). activation_tac. Qed.

Lemma ovAbort_stable_out p : ovAbortState p -> discActEnabled p (chanMStable *!).
  activation_tac. Qed.
 
Lemma tfsBc_trans_out p : tfsBcState p -> discActEnabled p (chanTrans *!).
  activation_tac. Qed.

Lemma bcWait_trans_in p m x : bcWaitState m x p -> discActEnabled p (chanTrans *?).
  activation_tac. Qed.

Lemma sleep_trans_in p : sleepingState p -> discActEnabled p (chanTrans *?).
  activation_tac. Qed.

Lemma paused_unpause_in p : pausedState p -> discActEnabled p (chanUnpause *?).
  activation_tac. Qed.

(*** Versions of activation using sort ***)

Lemma paused_unpause_in_sort d p : pausedState p -> sort (chanUnpause *?) d p.
  intro Q. apply paused_unpause_in in Q. apply enabledInSort_in. assumption. Qed.
  
Lemma switchListen_unpause_out_sort d p : switchListenState p -> sort (chanUnpause *!) d p.
  intro Q. apply switchListen_unpause_out in Q. apply enabledInSort_out. assumption. Qed.

Lemma tfsListen_unpause_out_sort d p : tfsListenState p -> sort (chanUnpause *!) d p.
  intro Q. apply tfsListen_unpause_out in Q. apply enabledInSort_out. assumption. Qed.








(*** Non standard activation results - need a bit more thinking***)

(*Come up with an anti-activation tactic: inversion on the transition that was claimed
and show that none of the cases generated match any of the cases for the state predicate.*)
(**A listener process cannot output on the channel outProc.*)
(* begin helpers for listener_outProc_out_not *)
(** Given [Q : p ~p~ X] and [TR : p -P- a -P> p'], transfers the transition
across the bisimulation to obtain [X -P- a -P> q'] (and [p' ~p~ q']). *)
Ltac listener_outProc_out_not_bisim_fwd :=
  match goal with [Q : ?p ~p~ ?X, TR : ?p -P- ?a -P> ?p' |- _] =>
    let F1 := fresh "F" in let F2 := fresh "F" in
    inversion Q as [F1 F2]; clear Q; apply F1 in TR; clear F1 F2 end.
(* end helpers *)

Theorem listener_outProc_out_not (p p' : ProcTerm) (v : list BaseType) : 
  listenerState p -> p -PA- chanOutProc ;! v -PA> p' -> False.
Proof.
  intros LS TR. apply stepPDisc in TR.
  inversion LS as [Q|m Q|m Q|Q|Q|m r Q]; clear LS; cbv in Q;
  listener_outProc_out_not_bisim_fwd; exand_flat; invert_steps;
  repeat invert_trans.
Qed.
(**Proof sketch: Because none of its constituents can output on said channel.*)

(*!Think this needs to be changed from generic "v" to specific list of [r, m'']...*)           
(** A process in the listening state is listening on the channel AN.*)
Lemma listening_AN_prot p v :
  listeningStateProt p -> discActEnabled p (chanAN ;? v).
  Admitted. (*C*)(*5*)
(**Proof: Lift an activation result from simple level.
Come up with a general tactic for that lifting?*)


(****************** Tracking ******************)
(**Results which take a transition across processes and derive information on this
transition based on the nature of the source/derivative process. Fwd tracking takes
p -PA- a -PA> p' and a predicate on p & infers something about a & p' (usuall the channel
& tuple type of a and a simple state predicate on p'). Back tracking is similar,
but works the opposite direction: starting with a predicate on p' and inferring a
and p from there.*)

(*** Bidirectional tracking (action/variable matching) ***)

(* begin helpers for goMsg_gotRange_track *)
Lemma goMsg_gotRange_track_tot X Y A B :
  evalBoolExpFunTot (bPossInc X Y (eSubtract A B)) = false /\
  evalBoolExpFunTot (bNot (bPossInc X Y (eSubtract A B))) = false.
Proof.
  unfold evalBoolExpFunTot; simpl.
  destruct (evalExpFun A) as [b1| ]; destruct (evalExpFun B) as [b2| ];
  try destruct (evalBaseNonnegFun b1); try destruct (evalBaseNonnegFun b2);
  destruct (evalExpFun X) as [b3| ]; try destruct b3;
  destruct (evalExpFun Y) as [b4| ]; try destruct b4; split; reflexivity.
Qed.

Lemma goMsg_gotRange_track_live (m' : Mode) (r : Distance) : exists (a1 : DiscAct) g2,
  subProcTerm (listsToSub [vM] (listBaselistExp [baseMode m']))
    (app currPincCheckN [eVar vM, eBase m', eBase r]) -PA- a1 -PA> g2.
Proof.
  simpl. remove_updates.
  destruct (possIncBool m' m' r) eqn:PI.
  - do 2 eexists. eapply stepDpApp; [reflexivity | ].
    unfold currPincCheck. simpl. remove_resets. remove_updates.
    apply stepDpChoiceR. eapply stepDpThen.
    + eapply stepDpApp; [reflexivity | ]. unfold badOvlp. simpl.
      apply stepDpOut. constructor.
    + unfold evalBoolExpFunTot. simpl. rewrite PI. reflexivity.
  - do 2 eexists. eapply stepDpApp; [reflexivity | ].
    unfold currPincCheck. simpl. remove_resets. remove_updates.
    apply stepDpChoiceL. eapply stepDpThen.
    + eapply stepDpApp; [reflexivity | ]. unfold currComp. simpl.
      apply stepDpChoiceL. apply (stepDpIn chanMStable [] []). reflexivity.
    + unfold evalBoolExpFunTot. simpl. rewrite PI. reflexivity.
Qed.

Ltac goMsg_gotRange_track_kill :=
  match goal with
  | [H : evalBoolExpFunTot (bPossInc ?X ?Y (eSubtract ?A ?B)) = true |- _] =>
    rewrite (proj1 (goMsg_gotRange_track_tot X Y A B)) in H; discriminate H
  | [H : evalBoolExpFunTot (bNot (bPossInc ?X ?Y (eSubtract ?A ?B))) = true |- _] =>
    rewrite (proj2 (goMsg_gotRange_track_tot X Y A B)) in H; discriminate H
  end.

Lemma goMsg_gotRange_track_stuck E1 A B (m' : Mode) q1 a1 q2 :
  app gotRangeN [E1, eSubtract A B] -PA- chanMCurr ;? [baseMode m'] -PA> q1 ->
  q1 -PA- a1 -PA> q2 -> False.
Proof.
  intros S1 S2.
  inversion S1; subst. clear S1.
  invert_def.
  unfold gotRange in *. simpl in *.
  match goal with [H : stepDiscProc (inPrefix _ _ _) _ _ |- _] => rename H into S4 end.
  remove_resets_hyp S4. remove_updates_hyp S4.
  inversion S4; subst. clear S4.
  simpl in S2. remove_updates_hyp S2.
  inversion S2; subst. clear S2.
  invert_def.
  unfold currPincCheck in *. simpl in *.
  match goal with [H : stepDiscProc (_ $+$ _) _ _ |- _] => rename H into SS end.
  remove_resets_hyp SS. remove_updates_hyp SS.
  inversion SS; subst; clear SS;
  match goal with [H : stepDiscProc (_ $> _) _ _ |- _] => inversion H; subst end;
  goMsg_gotRange_track_kill.
Qed.
(* end helpers *)

Lemma goMsg_gotRange_track m m' l r p p' a :
  gotMsgState m l p -> gotRangeState m' r p' ->
  p -PA- a -PA> p' -> exists l',
  a = chanPos ;? [basePosition l'] /\
  r = mkDistance (dist2d l l' -nn- speedMax *nn* msgLatency).
Proof.
  intros GM GR ST.
  destruct GM as [F _].
  destruct (F a p' (stepPDisc _ _ _ ST)) as [q' [QS PQ]].
  inversion QS; subst.
  match goal with [H : stepDiscProc (gotMsg _ _) _ _ |- _] => unfold gotMsg in H; inversion H; subst end.
  match type of PQ with _ ~p~ ?Q =>
  assert (BT : gotRange m' r ~p~ Q) by (eapply bisim_trans; [apply bisim_symm; exact GR | exact PQ]) end.
  clear GR PQ F QS ST.
  destruct BT as [G _].
  assert (G1 : gotRange m' r -P- (chanMCurr ;? [baseMode m']) -P>
     subProcTerm (listsToSub [vM] (listBaselistExp [baseMode m'])) (app currPincCheckN [eVar vM, eBase m', eBase r])).
  { constructor. unfold gotRange. apply stepDpIn. reflexivity. }
  destruct (G _ _ G1) as [q1 [Q1 B1]].
  clear G G1.
  inversion Q1; subst. clear Q1.
  match goal with [H : stepDiscProc _ _ q1 |- _] => rename H into Q1 end.
  simpl in Q1.
  destruct (goMsg_gotRange_track_live m' r) as [a1 [g2 GS]].
  destruct B1 as [F1 _].
  destruct (F1 _ _ (stepPDisc _ _ _ GS)) as [q2 [QS2 _]].
  inversion QS2; subst.
  exfalso. eapply goMsg_gotRange_track_stuck; eassumption.
Qed.

Lemma currOK_listening_track m p p' a : currOKState m p ->
  listeningState p' -> p -PA- a -PA> p' -> a = (chanMStable *?).
  Admitted.

Lemma abortOvlp_listening_track (p p' : ProcTerm) (a : DiscAct) :
  abortOvlpState p -> listeningState p' -> p -PA- a -PA> p' ->
  a = chanAbort;! [].
Proof.
  intros CS LS TR. apply stepPDisc in TR. unfold abortOvlpState in CS.
  unfold abortOvlp in CS.
  listener_outProc_out_not_bisim_fwd. exand_flat. invert_steps.
  repeat invert_trans.
  match goal with [H : evalExpLists [] _ |- _] => inversion H end.
  reflexivity.
Qed.

(*** Tactics ***)

(**Does some pre-processing on a back-tracking result, in the form of
some transition followed by two state predicates as premises. TR2 is
just a hypothesis that needs to be cleared.*)
Ltac backtrack_pre p TR2 :=
  let TR1 := fresh "TR" in
  let SP1 := fresh "SP" in let SP2 := fresh "SP" in
  intros TR1 SP1 SP2; cbv in SP2; apply stepPDisc in TR1;
  lets TR2 : TR1;
  invertClear SP1; match goal with [V : _ p |- _] =>
  apply V in TR1 end; exand_flat.

(** Given a context already pre-processed by backtrack_pre, this tactic
attempts to generate a contradiction via bisimilarities that are set up.
TR2 is just a hypothesis that needs to be cleared.*)
Ltac backtrack_post TR2 :=
  clear TR2; let BT := fresh "BT" in
  bisim_trans_tac BT; invert_steps;
  (*This bit may be a bit susceptible to freezing the whole thing-
  so I'd say just be prepared to change it if need be.*)
  repeat invert_trans; try bisim_contra BT;
  try (apply bisim_symm in BT; bisim_contra BT).

(*Weeds out contradictions for a back-tracking result, leaving only
the valid transition(s).*)
Ltac backtrack_weed p := let TR := fresh in
  backtrack_pre p TR; backtrack_post TR.

(*** Results ***)

(*Assuming we've already been through m existentials, this tactic works
by matching P with a function applied to some number of arguments and then
converts the required amount of arguments to existentials.*)

(*** Back tracking ***)

Theorem tfsNext_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> overlapState p -> tfsNextState m p' ->
  tfsStartState p. backtrack_weed p. Qed. 

Theorem ovWait_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (t x y : Time) :
  p -PA- a -PA> p' -> overlapState p -> ovWaitState m t x y p' ->
  initStateProt m p \/ exists l,
  ovReadyState m (addTime t (period m)) l p /\ x = t
  /\ y = period m /\ a = (chanOutProc ;! [baseMode m, basePosition l]).
  backtrack_weed p. Qed.

Theorem ovReady_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) (t : Time) (l : Position) :
  p -PA- a -PA> p' -> overlapState p -> ovReadyState m t l p' ->
  exists x, ovWaitState m t x zeroTime p. backtrack_weed p.
  Admitted.

Theorem switchBc_prev (p p' : ProcTerm) (a : DiscAct) (m : Mode) :
  p -PA- a -PA> p' -> overlapState p -> switchBcState m p' ->
  exists t, exists y, ovWaitState m t zeroTime y p.
Proof.
  backtrack_weed p.
  match goal with [H : evalExpFunTime _ = Some zeroTime |- _] =>
    unfold liftTimeExp, evalExpFunTime in H end.
  match goal with [H : context [evalExpFun (eBase (baseTime ?x))] |- _] =>
    destruct x as [xr]; simpl in H; inversion H; subst end.
  match goal with [B : ?X ~p~ switchBcN $( _ )$ |- _] =>
    let T0 := fresh "T" in let q := fresh "q" in
    assert (exists q, X -PA- chanWake ;! [baseMode m] -PA> q) as [q T0]
      by (eexists; repeat constructor);
    apply stepPDisc in T0; let F1 := fresh "F" in let F2 := fresh "F" in
    inversion B as [F1 F2]; apply F1 in T0 end.
  exand_flat. invert_steps. invert_app_trans. repeat invert_trans.
  match goal with [H : evalExpLists [_] [_] |- _] =>
    let E1 := fresh in let E2 := fresh in
    inversion H as [ | ? ? ? ? E1 E2]; subst; inversion E1; subst end.
  do 2 eexists. eassumption.
Qed.

Theorem switchCurr_prev (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> overlapState p -> switchCurrState p' ->
  exists m, switchBcState m p. backtrack_weed p. Qed. 

(*** Fwd tracking ***)

(** Tactics **)

(**This is an activation-esque pre-tactic that instead of proving a dae,
matches to an actual transition, possibly with an eVar.*)
Ltac activation_trans_pre := match goal with [U : _ ?p |- ?p -PA- _ -PA> _] =>
  inversion U; try (econstructor; [reflexivity | ]); remove_resets;
  remove_updates end.

Ltac fwd_track_pre := intros; repeat eexists_safe;
  match goal with [ |- ?P /\ _] => assert P end.

(** Results **)




(*
(Tatic definition is to go in above tactics section)
-Idea for fwd-tracking tactic:
>First assert and name a new hypothesis equivalent to the LHS of the goal
=>(match exists xs, P /\ Q and assert exists xs, P)
>Then repeat eexists
>Then apply an activation tactic
>Then remove existentials from the newly asserted hypothesis (maybe a tactic to do this-
maybe it already exists, has to work for arbitrary number of variables,
don't worry about naming the variables)
>Then repeat eexists
>Then split the goal
>Apply the asserted hypothesis to the LHS
>Apply state_trans_src, strengthening the asserted hypothesis
>From here perform a number of inversions (invert_trans?) and you should have something
very close to your goal
>Potentially use the tactics below as a template
>Potentially use tactics developed for listening_inProc e.g. fwd_track_pre

Ltac activation_pre_tac :=
  intro X; invertClear X;
  [eapply daeApp; [reflexivity | simpl] |
  match goal with
  | [Q : ?pred ?x1 ?x2 ?x3 = ?proc |- _] => unfold pred
  | [Q : ?pred ?x1 ?x2 = ?proc |- _] => unfold pred
  | [Q : ?pred ?x1 = ?proc |- _] => unfold pred
  | [Q : ?pred = ?proc |- _] => unfold pred
  end].

Ltac activation_post_tac :=
  match goal with
  [ |- discActEnabled ?p ?a] => 
    match p with
    (*For sum, recursively go left and see if it succeeds, else go right.*)
    | _ $< _ >$ ? _  => apply dae_inPfx; reflexivity
    | _ $< _ >$ ! _  => apply dae_outPfx; constructor
    | ?p1 $+$ ?p2 => first [solve [apply daeSumL; activation_post_tac] |
      solve [apply daeSumR; activation_post_tac]]
    end
  end.
*)

(*** Conditional fwd tracking ***)
(* Hopefully I can copy the tactics for regular forward tracking, or even use them.
If I'm clever I'll make the tactics as modular as possible, allowing them to be
reused in multiple places. For example, there should be one tactic to do all the
pre-processing and get rid of all the contradictary cases. Then after this tactic,
another tactic sweeps in and solves the goal directly from the hypotheses- a
disjunction is not a big problem here, a regular old "assumption" might even
work, or if not I'm sure there's a tactic for this. The main work anyway is
inversions and eliminations of contradictory cases.*)

(* begin helpers for currOK_next *)
(** An application process is bisimilar to its (substituted) definition body. *)
Lemma currOK_next_app_bisim n l :
  n $( l )$ ~p~ subProcTerm (listsToSub (fst (def n)) l) (snd (def n)).
Proof.
  constructor; intros a q T.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + constructor. apply stepDpApp_alt. assumption.
    + constructor. remember (def n) as dn. destruct dn as [l1 b].
      eapply stepTpApp. symmetry. eassumption. assumption.
Qed.
(** Rewrites a goal [app N args ~p~ T] into [body[args/vars] ~p~ T], with the
substitution computed away. *)
Ltac currOK_next_unfold_app :=
  eapply bisim_trans; [apply currOK_next_app_bisim | ];
  cbn [def fst snd listsToSub liftVarList liftExpList subProcTerm subExp subBoolExp
    listSub map liftNameProc listBaselistExp
    bcWait sleeping bcReady dormant init ovWait ovReady switchBc switchCurr
    switchListen tfsStart tfsNext tfsCurr tfsBc tfsListen ovAbort listening
    checkRange rangeBad currEq badOvlp currOK nextEq abortOvlp gotMsg gotRange
    currPincCheck currComp nextPincCheck paused];
  remove_updates.

(** Closes a goal [listeningN $( [] )$ ~p~ listening]. *)
Ltac currOK_next_listening_app :=
  eapply bisim_trans; [apply currOK_next_app_bisim | ];
  cbn [def fst snd listsToSub]; rewrite subProc_id_eq; apply bisim_refl.

(** Pre-processing for forward tracking: from [TR : p -PA- a -PA> p'] and a simple
state predicate [p ~p~ X] in the context, generates all transitions of [X]
and leaves the goal with [p' ~p~ D] for each derivative [D]. *)
Ltac currOK_next_fwd_pre :=
  match goal with [TR : _ -PA- _ -PA> _ |- _] => apply stepPDisc in TR end;
  listener_outProc_out_not_bisim_fwd; exand_flat; invert_steps;
  repeat invert_trans;
  try match goal with [H : length ?l = length _ |- _] =>
    destruct l as [ | ?b [ | ?b' ?l]]; simpl in H; try discriminate H end;
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp] in *;
  repeat match goal with [H : _ ~p~ _ |- _] => remove_updates_hyp H end.
(* end helpers *)

Theorem currOK_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> currOKState m'' p ->
  (exists m, nextEqState m m'' p') \/
  listeningState p'.
Proof.
  intros TR CS. unfold currOKState in CS. unfold currOK in CS.
  currOK_next_fwd_pre.
  - right. unfold listeningState. eapply bisim_trans; [eassumption | ].
    currOK_next_listening_app.
  - match goal with [b : BaseType |- _] => destruct b as [m|t|l|d|d|r] end.
    1: left; exists m; unfold nextEqState; eapply bisim_trans; [eassumption | ];
     currOK_next_unfold_app; apply bisim_refl.
    all: right; unfold listeningState; eapply bisim_trans; [eassumption | ];
    currOK_next_unfold_app.
    all: (eapply bisim_trans; [apply if_then_bisim_false; eapply bevalEqualFalse | ]).
    all: first [apply evalBase | discriminate | currOK_next_listening_app].
Qed.

Theorem rangeBad_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> rangeBadState m'' p ->
  (exists m, currEqState m m'' p'). Admitted. (*#fwd-track*)

Theorem gotMessage_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (l : Position) :
  p -PA- a -PA> p' -> gotMsgState m'' l p ->
  (exists r, gotRangeState m'' r p'). Admitted. (*#fwd-track*)

Theorem gotRange_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> gotRangeState m'' r p ->
  (exists m, currPincCheckState m m'' r p'). Admitted. (*#fwd-track*)

Theorem currComp_next (p p' : ProcTerm)
  (a : DiscAct) (m'' : Mode) (r : Distance) :
  p -PA- a -PA> p' -> currCompState m'' r p ->
  (exists m, nextPincCheckState m m'' r p') \/
  listeningState p'. Admitted. (*#fwd-track*)

Theorem badOvlp_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> badOvlpState p -> listeningState p'.
Proof.
  intros TR CS. unfold badOvlpState in CS. unfold badOvlp in CS.
  currOK_next_fwd_pre.
  unfold listeningState. eapply bisim_trans; [eassumption | ].
  currOK_next_listening_app.
Qed.

Theorem abortOvlp_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> abortOvlpState p -> listeningState p'.
Proof.
  intros TR CS. unfold abortOvlpState in CS. unfold abortOvlp in CS.
  currOK_next_fwd_pre.
  unfold listeningState. eapply bisim_trans; [eassumption | ].
  currOK_next_listening_app.
Qed.

Lemma tfsStart_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> tfsStartState p ->
  exists m, tfsNextState m p'.
  Admitted. (*#fwd-track*)
  
(****************** Conditionals ******************)
(* In here are resuls relating conditional state predicates to their branches.
In general, the results are of the form "If some conditional state predicate S
is true, and the condition is true (say), then the state predicate S' corresponding
to the true branch of S is true"*)

(* begin helpers for currEq_cond_true *)
(** Unfolding an application process yields a bisimilar process. *)
Lemma currEq_cond_true_app n l1 l2 p q :
  def n = (l1, p) -> subProcTerm (listsToSub l1 l2) p = q -> app n l2 ~p~ q.
Proof.
  intros D E. subst q. constructor; intros a p' S.
  - exists p'. split; [ | apply bisim_refl].
    inversion S; subst.
    + match goal with H : app n l2 -PA- _ -PA> _ |- _ => inversion H; subst end.
      rewrite D in *.
      match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end.
      apply stepPDisc; assumption.
    + match goal with H : app n l2 -PD- _ -PD> _ |- _ => inversion H; subst end.
      rewrite D in *.
      match goal with H : (_, _) = (_, _) |- _ => injection H; intros; subst end.
      apply stepPTimed; assumption.
  - exists p'. split; [ | apply bisim_refl].
    inversion S; subst.
    + apply stepPDisc. eapply stepDpApp; eassumption.
    + apply stepPTimed. eapply stepTpApp; eassumption.
Qed.
(* end helpers *)

Lemma currEq_cond_true m m'' p :
  m = m'' -> currEqState m m'' p -> badOvlpState p.
Proof.
  intros E S. unfold currEqState, badOvlpState in *. subst m''.
  assert (B : evalBoolExp (m =b= m) true)
    by (eapply bevalEqualTrue; apply evalBase).
  eapply bisim_trans. apply S. unfold currEq.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  eapply currEq_cond_true_app; reflexivity.
Qed.

Lemma currEq_cond_false m m'' p :
  m <> m'' -> currEqState m m'' p -> currOKState m'' p.
Proof.
  intros NE S. unfold currEqState, currOKState in *.
  assert (B : evalBoolExp (m =b= m'') false).
  { eapply bevalEqualFalse; [apply evalBase | apply evalBase | ].
    intro E. inversion E. contradiction. }
  eapply bisim_trans. apply S. unfold currEq.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  eapply currEq_cond_true_app. reflexivity. clean_proc. reflexivity.
Qed.

Lemma nextEq_cond_true m' m'' p :
  m' = m'' -> nextEqState m' m'' p -> abortOvlpState p.
Proof.
  intros E S. unfold nextEqState, abortOvlpState in *. subst m''.
  assert (B : evalBoolExp (m' =b= m') true)
    by (eapply bevalEqualTrue; apply evalBase).
  eapply bisim_trans. apply S. unfold nextEq.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  eapply currEq_cond_true_app; reflexivity.
Qed.

Lemma nextEq_cond_false m' m'' p :
  m' <> m'' -> nextEqState m' m'' p -> listeningState p.
Proof.
  intros NE S. unfold nextEqState, listeningState in *.
  assert (B : evalBoolExp (m' =b= m'') false).
  { eapply bevalEqualFalse; [apply evalBase | apply evalBase | ].
    intro E. inversion E. contradiction. }
  eapply bisim_trans. apply S. unfold nextEq.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  eapply currEq_cond_true_app. reflexivity. apply subProc_id_eq.
Qed.

Lemma currPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r -> currPincCheckState m m'' r p ->
  badOvlpState p.
Proof.
  intros PI S. unfold currPincCheckState, badOvlpState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) true).
  { rewrite <- (possInc_possIncBool m m'' r PI).
    apply bevalPossInc; apply evalBase. }
  eapply bisim_trans. apply S. unfold currPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  eapply currEq_cond_true_app; reflexivity.
Qed.

Lemma currPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  currPincCheckState m m'' r p -> currCompState m'' r p.
Proof.
  intros NPI S. unfold currPincCheckState, currCompState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) false).
  { assert (F : possIncBool m m'' r = false).
    { unfold possIncBool. destruct (possIncDec m m'' r);
      [contradiction | reflexivity]. }
    rewrite <- F. apply bevalPossInc; apply evalBase. }
  eapply bisim_trans. apply S. unfold currPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_false _ _ _ B).
  eapply currEq_cond_true_app. reflexivity. clean_proc. reflexivity.
Qed.

Lemma nextPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> abortOvlpState p.
Proof.
  intros PI S. unfold nextPincCheckState, abortOvlpState in *.
  assert (B : evalBoolExp (bPossInc m m'' r) true).
  { rewrite <- (possInc_possIncBool m m'' r PI).
    apply bevalPossInc; apply evalBase. }
  eapply bisim_trans. apply S. unfold nextPincCheck.
  eapply bisim_trans. apply choice_bisim_symm.
  eapply bisim_trans. apply (if_then_bisim_true _ _ _ B).
  eapply currEq_cond_true_app; reflexivity.
Qed.

(* begin helpers for nextPincCheck_cond_false *)
(** An application process is bisimilar to its (substituted) body. *)
Lemma nextPincCheck_cond_false_app n l1 l2 p :
  def n = (l1, p) -> app n l2 ~p~ subProcTerm (listsToSub l1 l2) p.
Proof.
  intros D. constructor.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst.
    + apply stepPDisc. match goal with [S0 : app _ _ -PA- _ -PA> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
    + apply stepPTimed. match goal with [S0 : app _ _ -PD- _ -PD> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst; [apply stepPDisc; eapply stepDpApp |
      apply stepPTimed; eapply stepTpApp]; eassumption.
Qed.
(* end helpers *)

Lemma nextPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> listeningState p.
Proof.
  intros NP U. red in U. red.
  assert (PB : possIncBool m m'' r = false).
  { unfold possIncBool. destruct (possIncDec m m'' r); [contradiction | reflexivity]. }
  eapply bisim_trans; [exact U | ].
  unfold nextPincCheck.
  eapply bisim_trans.
  { apply choice_bisim_context.
    - apply cond_bisim_true. change true with (negb false). apply bevalNot.
      rewrite <- PB. apply bevalPossInc; constructor.
    - apply cond_bisim_false. unfold evalBoolExpFunTot. simpl.
      first [exact PB | rewrite PB; reflexivity]. }
  eapply bisim_trans; [apply choice_bism_unit_r | ].
  eapply bisim_trans;
    [apply (nextPincCheck_cond_false_app listeningN [] [] listening); reflexivity | ].
  change (listsToSub [] []) with idSubst. rewrite subProc_id_eq. apply bisim_refl.
Qed.

(****************** Delay Preservation ******************)

(*NOTE- IN HERE WE ACTUALLY WANT BACKWARDS AND FORWARDS PRESERVATION
EITHER DO SEPARATE THEOREMS FOR EACH, AND ADD BACK AND FWD TO RESULT
NAMES, OR DO BOTH IN ONE THEOREM, USING THE <-> OPERATOR.*)

(**In this section, we would like to collect a number of results asserting
that the delay relation preserves certain state predicates. Here we will
write a few examples, but there is no need to write out all the cases,
especially since the way these things are defined might change. Just
enough to get a general idea.*)

(*** Tactics ***)

(*del_pres_fwd_tac*)

(**Very similar to existentialise_evals but for a delay transition rather
than a discrete transition.*)
Ltac existentialise_evals_del H :=
  let y1 := fresh in let y2 := fresh in
  let y3 := fresh in let y4 := fresh in let U := fresh in
  match type of H with
  | ?P /\ ?Q =>
    match P with
    | (((?e1 |_| ?v1 /\ ?e2 |_| ?v2) /\
      ?e3 |_| ?v3) /\ ?e4 |_| ?v4) =>
      match Q with ?f ?e1 ?e2 ?e3 ?e4 -PD- ?d -PD> ?p' => 
      assert (exists y1 y2 y3 y4, f y1 y2 y3 y4 -PD- d -PD> p'
      /\ (((y1 |_| v1 /\ y2 |_| v2) /\
      y3 |_| v3) /\ y4 |_| v4)) as U;
      [repeat eexists; apply H | clear H]; rename U into H
      end
    | ((?e1 |_| ?v1 /\ ?e2 |_| ?v2) /\
      ?e3 |_| ?v3) =>
      match Q with ?f ?e1 ?e2 ?e3 -PD- ?d -PD> ?p' => 
      assert (exists y1 y2 y3, f y1 y2 y3 -PD- d -PD> p'
      /\ ((y1 |_| v1 /\ y2 |_| v2) /\
      y3 |_| v3)) as U;
      [repeat eexists; apply H | clear H]; rename U into H
      end
    | (?e1 |_| ?v1 /\ ?e2 |_| ?v2) =>
      match Q with ?f ?e1 ?e2 -PD- ?d -PD> ?p' => 
      assert (exists y1 y2, f y1 y2 -PD- d -PD> p'
      /\ (y1 |_| v1 /\ y2 |_| v2)) as U;
      [repeat eexists; apply H | clear H]; rename U into H
      end
    | ?e1 |_| ?v1 =>
      match Q with ?f ?e1 -PD- ?d -PD> ?p' => 
      assert (exists y1, f y1 y2 -PD- d -PD> p'
      /\ y1 |_| v1) as U;
      [repeat eexists; apply H | clear H]; rename U into H
      end
    end
  | _ => idtac
  end.

Ltac invert_trans_del := match goal with [P : _ -PD- _ -PD> _ |- _]
  => invertClear P; subst end.

(*** Simple Predicate Preservation ***)

Lemma ovWait_del_pres m t x y p p' d :
  ovWaitState m t x y p -> p -PD- d -PD> p' ->
  ovWaitState m t x y p'.
  
  introz U.
   Admitted. (*#delay-pres*)

(* begin helpers for ovReady_del_pres *)
(** Generic delay-preservation tactic for state predicates of the form
  [XState args p := p ~p~ X args] where [X args] is built from prefixes and
  sums only (so it delays to itself). Expects the goal
  [XState args p -> p -PD- d -PD> p' -> XState args p']. *)
Ltac ovReady_del_pres_tac :=
  let U := fresh "U" in let V := fresh "V" in
  let U1 := fresh "U" in let U2 := fresh "U" in
  let q := fresh "q" in let W := fresh "W" in let B := fresh "B" in
  intros U V; red in U; destruct U as [U1 U2];
  apply stepPTimed in V; apply U1 in V; destruct V as [q [W B]];
  clear U1 U2; inversion W; subst;
  match goal with [H : ?X -PD- _ -PD> q |- _] =>
    let X' := eval red in X in change X with X' in H end;
  repeat match goal with
    | [H : outPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : inPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : sum _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    end;
  exact B.
(* end helpers *)

Lemma ovReady_del_pres m t l p p' d :
  ovReadyState m t l p -> p -PD- d -PD> p' ->
  ovReadyState m t l p'.
Proof.
  ovReady_del_pres_tac.
Qed.

Lemma switchBc_del_pres m p p' d :
  switchBcState m p -> p -PD- d -PD> p' ->
  switchBcState m p'.
Proof.
  ovReady_del_pres_tac.
Qed.

Lemma switchCurr_del_pres p p' d :
  switchCurrState p -> p -PD- d -PD> p' ->
  switchCurrState p'.
Proof.
  ovReady_del_pres_tac.
Qed.

(*** Compound Predicate Preservation ***)

(**The delay relation preserves the nextSinceState predicate.*)
Theorem del_pres_nextSinceState (p p' : ProcTerm) (d : Delay) : 
  nextSinceState p -> p -PD- d -PD> p' -> nextSinceState p'.
  (*Proof: Inversion on nextSinceState into all possible cases*)
  introz U. inversion U.
  (*Now simply apply delay preservation results on these.*)
  lets AUX : ovWait_del_pres H U0. eapply nexsOvwSt; eassumption.
  lets AUX : ovReady_del_pres H U0. eapply nexsOvrSt; eassumption.
  lets AUX : switchBc_del_pres H U0. eapply nexsSbcSt; eassumption.
  lets AUX : switchCurr_del_pres H U0. eapply nexsScSt; eassumption.
  Qed.

(**The delay relation preserves the tfsState predicate.*)
Theorem del_pres_tfsState (p p' : ProcTerm) (d : Delay): 
  tfsState p -> p -PD- d -PD> p' -> tfsState p'.
Proof.
  intros U V. destruct U as [H|m H|H|H|H];
    [apply tfsStaSt | apply (tfsNexSt _ m) | apply tfsCurSt | apply tfsBcSt |
     apply tfsLisSt]; revert H V; ovReady_del_pres_tac.
Qed.
(*Proof: lift delay preservation results in a similar fashion to del_pres_nextSinceState*)

(****************** Linking ******************)

Lemma link_par_triple_discEx (p1 p2 p3 p' : ProcTerm) (a : DiscAct) :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p' -> exists p1' p2' p3',
  p' = p1' $||$ p2' $||$ p3'. intros. apply stepPDisc in H.
  apply parStructPres in H. decompEx2 H p1' q' U. andflat U.
  apply parStructPres2 in U2. decompEx2 U2 p2' p3' Y. andflat U.
  rewrite U0. rewrite U1. exists p1' p2' p3'. reflexivity. Qed.

Ltac link_partripdiscex_tac U p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?a -PA> ?p' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_discEx H;
  let U1 := fresh U in decompEx3 Q1 p1' p2' p3' U1
  end.

Ltac link_partripdiscex_tac2 p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?a -PA> ?p' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_discEx H;
  let U1 := fresh in decompEx3 Q1 p1' p2' p3' U1;
  rewrite U1 in H; clear U1
  end.

Lemma link_par_triple_delEx (p1 p2 p3 p' : ProcTerm) (d : Delay) :
  p1 $||$ p2 $||$ p3 -PD- d -PD> p' -> exists p1' p2' p3',
  p' = p1' $||$ p2' $||$ p3'. intros. apply stepPTimed in H.
  apply parStructPres in H. decompEx2 H p1' q' U. andflat U.
  apply parStructPres2 in U2. decompEx2 U2 p2' p3' Y. andflat U.
  rewrite U0. rewrite U1. exists p1' p2' p3'. reflexivity. Qed.

Ltac link_partripdelex_tac U p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PD- ?d -PD> ?p' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_delEx H;
  let U1 := fresh U in decompEx3 Q1 p1' p2' p3' U1
  end.

Ltac link_partripdelex_tac2 p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PD- ?d -PD> ?p' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_delEx H;
  let U1 := fresh in decompEx3 Q1 p1' p2' p3' U1;
  rewrite U1 in H; clear U1
  end.

Lemma link_par_triple_out (p1 p2 p3 p1' p2' p3' : ProcTerm)
  (c : Channel) (v : list BaseType) :
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  (p1 -PA- c ;! v -PA> p1' /\ p2 = p2' /\ p3 = p3' \/
  p2 -PA- c ;! v -PA> p2' /\ p1 = p1' /\ p3 = p3' \/
  p3 -PA- c ;! v -PA> p3' /\ p1 = p1' /\ p2 = p2').
  introz U. inversion U. left. subst.
  split; [assumption | ]. split; reflexivity.
  inversion H2; subst. right. left.
  split; [assumption | ]. split; reflexivity.
  right. right. split; [assumption | ]. split; reflexivity.
  Qed.

Ltac link_partripout_tac U :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?c ;! ?v -PA> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  let H1 := fresh in lets H1 : link_par_triple_out H;
  let H2 := fresh in elimOr3 H1 H2; andflat U
  end.

Lemma link_par_triple_in (p1 p2 p3 p1' p2' p3' : ProcTerm)
  (c : Channel) (v : list BaseType) :
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  (p1 -PA- c ;? v -PA> p1' /\ p2 = p2' /\ p3 = p3' \/
  p2 -PA- c ;? v -PA> p2' /\ p1 = p1' /\ p3 = p3' \/
  p3 -PA- c ;? v -PA> p3' /\ p1 = p1' /\ p2 = p2').
  introz U. inversion U. left. subst.
  split; [assumption | ]. split; reflexivity.
  inversion H2; subst. right. left.
  split; [assumption | ]. split; reflexivity.
  right. right. split; [assumption | ]. split; reflexivity.
  Qed.

Ltac link_partripin_tac U :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?c ;? ?v -PA> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  let H1 := fresh in lets H1 : link_par_triple_in H;
  let H2 := fresh in elimOr3 H1 H2; andflat U
  end.

(* begin helpers for link_reach_triple_tau *)
(** Repeatedly inverts discrete transitions whose source is a sum, a prefix,
  a delay-guard or a conditional, discharging the impossible branches. *)
Ltac link_reach_triple_tau_inv :=
  repeat match goal with
   | [H : sum _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : del _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : ifThen _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
  end.

(** Given [S : XState args p] (i.e. [p ~p~ X args]) and [T : p -PA- a -PA> p'],
  transfers [T] to the specification process [X args], unfolds it and inverts
  the transition. Closes the goal when [X args] cannot perform [a]. *)
Ltac link_reach_triple_tau_noact S T :=
  let q := fresh "q" in let T' := fresh "T" in
  red in S; destruct (bisim_disc_match _ _ _ _ S T) as [q T'];
  match type of T' with ?X -PA- _ -PA> _ =>
    let X' := eval red in X in change X with X' in T' end;
  link_reach_triple_tau_inv.

Lemma link_reach_triple_tau_bc p p' :
  broadcastState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct S as [m x S | S | m l S]; link_reach_triple_tau_noact S T.
Qed.

Lemma link_reach_triple_tau_ov p p' :
  overlapState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct S as [S | m t x y S]; link_reach_triple_tau_noact S T.
Qed.

Lemma link_reach_triple_tau_ls p p' :
  listenerState p -> p -PA- tauAct -PA> p' -> False.
Proof.
  intros S T. destruct S as [S | m S | m S | S | S | m r S];
    link_reach_triple_tau_noact S T.
Qed.

Ltac link_reach_triple_tau_pick :=
  let tac := split; [eassumption | split; [eassumption | reflexivity]] in
  first [ left; tac | right; left; tac | right; right; left; tac
        | right; right; right; left; tac | right; right; right; right; left; tac
        | right; right; right; right; right; tac ].
(* end helpers *)

Lemma link_reach_triple_tau (p1 p2 p3 p1' p2' p3' : ProcTerm) :
  p1 $||$ p2 $||$ p3 -PA- tauAct -PA> p1' $||$ p2' $||$ p3' ->
  protocolState (p1 $||$ p2 $||$ p3) -> exists c v,
  (p1 -PA- c ;! v -PA> p1' /\ p2 -PA- c ;? v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;? v -PA> p1' /\ p2 -PA- c ;! v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;! v -PA> p1' /\ p3 -PA- c ;? v -PA> p3' /\ p2 = p2') \/
  (p1 -PA- c ;? v -PA> p1' /\ p3 -PA- c ;! v -PA> p3' /\ p2 = p2') \/
  (p2 -PA- c ;! v -PA> p2' /\ p3 -PA- c ;? v -PA> p3' /\ p1 = p1') \/
  (p2 -PA- c ;? v -PA> p2' /\ p3 -PA- c ;! v -PA> p3' /\ p1 = p1').
Proof.
  intros T P. inversion P; subst. clear P.
  invertClear T; subst;
    try (match goal with [H : _ $||$ _ -PA- _ -PA> _ |- _] => invertClear H; subst end);
    try solve [exfalso; first [eapply link_reach_triple_tau_bc; eassumption |
      eapply link_reach_triple_tau_ov; eassumption |
      eapply link_reach_triple_tau_ls; eassumption]];
    do 2 eexists; link_reach_triple_tau_pick.
Qed.
(**Prove more general result including taus and then eliminate the taus by anti-activation
  on each broadcast, listener and overlap process?
  Proof: From reachable, we have that p1, p2, p3 are braodcast, overlap, listener
  protocol components respectively. We then invert on the tau action and eliminate the tau
  cases for pi -tau-> pi' as they come up because none of the protocol components can ever
  do a tau (show this elsewhere). Leaving us our goal.*)
  
Ltac link_partriptau_tac c v U :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- tauAct -PA> ?p1' $||$ ?p2' $||$ ?p3',
  H0 : protocolState (?p1 $||$ ?p2 $||$ ?p3) |- _] =>
  let H1 := fresh in lets H1 : link_reach_triple_tau H H0;
  let Q1 := fresh in decompEx2 H1 c v Q1;
  let H2 := fresh in elimOr6 Q1 H2; andflat U
  end.

Lemma link_par_triple_del (p1 p2 p3 p1' p2' p3' : ProcTerm)
  (d : Delay) :
  p1 $||$ p2 $||$ p3 -PD- d -PD> p1' $||$ p2' $||$ p3' ->
  (p1 -PD- d -PD> p1' /\ p2 -PD- d-PD> p2' /\ p3 -PD- d -PD> p3').
  introz U. inversion U. inversion H5.
  repeat (split; [assumption | ]). assumption.
  Qed.

(**Proof: Immediate from semantics.*)

Ltac link_partripdel_tac U :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PD- ?d -PD> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_del H; andflat U
  end.

(****************** Reachability Results ******************)
(**In here we put results that are specific to reachable processes,
i.e. ones that can be reached by the transition semantics via the
protocol process. Results about the relationship between states of
the various components belong here e.g. "If the overlap component
is in such a state, then the listener is paused".*)

(**If a reachable process is paused, then it is in the process of a
mode switch and vice versa.*)
Theorem paused_switch (p : ProcTerm) : 
  reachableProt p ->
  (pausedStateProt p <-> switchStateProt p). Admitted. (*5*)
(**Proof: Induction on reachable. Then show that whenever either of these states happens initially, the other happens. Then show that if
both are true, and a transition happens, then either bother are still true or an unpause happens from switchListenState and both become
false. This is all evident on inspection of the overlap and listener component diagrams.*)

(**If p is reachable from the "protocol" process via
the semantics, then it has the "shape" of a protocol process.*)
Theorem reachableProt_triple (p : ProcTerm) : 
  reachableProt p -> protocolState p.
  intro.
  (*Need support lemmas: disc pres & del pres for ovlp, broadcast, listener state components.*)
  Admitted. (*5*)
(**Proof: Induction on reachable and use results that show broadcast, overlap and listener processes are closed under transitions*)

Ltac reachprot U :=
  match goal with
  [H : reachableProt ?p |- _] => let U1 := fresh U in
  lets U1 : reachableProt_triple H
  end.

(****************** Brute Force ******************)
(*I think these can be solved by inversion on the complex state predicate
followed by activation or anti-activation. Or could be followed by some
sort of tracking tactic e.g. gotMsg_state.*)

(* begin helpers for bc_outProc_out *)
(** An application process is bisimilar to its (substituted) body. *)
Lemma bc_outProc_out_app n l1 l2 p :
  def n = (l1, p) -> app n l2 ~p~ subProcTerm (listsToSub l1 l2) p.
Proof.
  intros D. constructor.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst.
    + apply stepPDisc. match goal with [S0 : app _ _ -PA- _ -PA> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
    + apply stepPTimed. match goal with [S0 : app _ _ -PD- _ -PD> _ |- _] =>
        inversion S0; subst end.
      match goal with [D0 : def n = _ |- _] => rewrite D in D0;
        inversion D0; subst end. assumption.
  - intros a x S. exists x. split; [ | apply bisim_refl].
    inversion S; subst; [apply stepPDisc; eapply stepDpApp |
      apply stepPTimed; eapply stepTpApp]; eassumption.
Qed.

(** A delay-guarded process only depends on the value of its guard. *)
Lemma bc_outProc_out_del_sim e1 e2 P t a x :
  evalExpFunTime e1 = Some t -> evalExpFunTime e2 = Some t ->
  del e1 P -P- a -P> x -> del e2 P -P- a -P> x.
Proof.
  intros E1 E2 S. inversion S; subst.
  - apply stepPDisc. match goal with [S0 : del _ _ -PA- _ -PA> _ |- _] =>
      inversion S0; subst end.
    apply stepDpTimeOut; [assumption | congruence].
  - apply stepPTimed. match goal with [S0 : del _ _ -PD- _ -PD> _ |- _] =>
      inversion S0; subst end.
    + apply stepTpDelAdd; [assumption | congruence].
    + apply stepTpDelSub. congruence.
    + congruence.
Qed.

Lemma bc_outProc_out_del_bisim e1 e2 P t :
  evalExpFunTime e1 = Some t -> evalExpFunTime e2 = Some t ->
  del e1 P ~p~ del e2 P.
Proof.
  intros E1 E2. constructor.
  - intros a x S. exists x. split;
      [apply (bc_outProc_out_del_sim e1 e2 P t); assumption | apply bisim_refl].
  - intros a x S. exists x. split;
      [apply (bc_outProc_out_del_sim e2 e1 P t); assumption | apply bisim_refl].
Qed.
(* end helpers *)

Theorem bc_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> broadcastState p ->
  bcReadyState m l p /\ bcWaitState m (period m) p'.
Proof.
  intros T B. destruct B as [m0 x S | S | m0 l0 S];
    [exfalso; link_reach_triple_tau_noact S T | exfalso; link_reach_triple_tau_noact S T | ].
  pose proof S as S0. red in S. destruct S as [S1 S2].
  apply stepPDisc in T. apply S1 in T. destruct T as [q [T1 B1]].
  inversion T1; subst.
  match goal with [H : bcReady _ _ -PA- _ -PA> _ |- _] => unfold bcReady in H;
    inversion H; subst end.
  repeat match goal with [H : evalExpLists (_ :: _) _ |- _] => inversion H; subst; clear H end.
  repeat match goal with [H : evalExp (eBase _) _ |- _] => inversion H; subst; clear H end.
  split; [exact S0 | ].
  red. eapply bisim_trans; [exact B1 | ].
  eapply bisim_trans;
    [apply (bc_outProc_out_app bcWaitN [vM, vX] _ (bcWait (eVar vM) (eVar vX)));
     reflexivity | ].
  unfold bcWait. simpl. clean_proc.
  apply choice_bisim_context; [ | apply bisim_refl].
  apply choice_bisim_context; [apply bisim_refl | ].
  apply (bc_outProc_out_del_bisim _ _ _ (period m));
    unfold evalExpFunTime; simpl; destruct (period m); reflexivity.
Qed.
(**Proof: Brute force try all the other possible broadcast states (auto tactic) and this is the only one that matches*)

Theorem ovlp_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> overlapState p ->
  exists t f, ovReadyState m t l p /\ 
  ovWaitState m (minusTime t (period m) f) (minusTime t (period m) f) (period m) p'.
Proof.
  intros T O. exfalso. destruct O as [S | m0 t0 x0 y0 S]; link_reach_triple_tau_noact S T.
Qed.
(**Proof: Brute force. Analogous to bc_outProc_out but with overlap states*)

(**A protocol process cannot input on the channel outProc.*)
(* begin helpers for prot_outProc_in_not *)
(** Repeatedly inverts every discrete transition hypothesis whose source is a
    syntactic sum, prefix, timeout, conditional or nil. Used for brute-force
    anti-activation on the bodies of the protocol component processes. *)
Ltac prot_outProc_in_not_inv :=
  repeat match goal with
  | [V : (_ $+$ _) -PA- _ -PA> _ |- _] => inversion V; clear V; subst
  | [V : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; clear V; subst
  | [V : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion V; clear V; subst
  | [V : del _ _ -PA- _ -PA> _ |- _] => inversion V; clear V; subst
  | [V : ifThen _ _ -PA- _ -PA> _ |- _] => inversion V; clear V; subst
  | [V : nilProc -PA- _ -PA> _ |- _] => inversion V
  end.

(** Unfolds the simple state predicates into bisimilarities. *)
Ltac prot_outProc_in_not_unfold :=
  unfold bcWaitState, sleepingState, bcReadyState, dormantState, ovWaitState,
    ovReadyState, switchBcState, switchCurrState, switchListenState,
    tfsStartState, tfsNextState, tfsCurrState, tfsBcState, tfsListenState,
    initState, ovAbortState, listeningState, rangeBadState, currOKState,
    abortOvlpState, badOvlpState, currCompState, pausedState, gotMsgState,
    gotRangeState, currEqState, nextEqState, currPincCheckState,
    nextPincCheckState in *.

(** Unfolds the bodies of the protocol component processes. *)
Ltac prot_outProc_in_not_body :=
  unfold bcWait, sleeping, bcReady, dormant, init, ovWait, ovReady, switchBc,
    switchCurr, switchListen, tfsStart, tfsNext, tfsCurr, tfsBc, tfsListen,
    ovAbort, listening, checkRange, rangeBad, currEq, badOvlp, currOK, nextEq,
    abortOvlp, gotMsg, gotRange, currPincCheck, currComp, nextPincCheck,
    paused in *.

(** Anti-activation: given p ~p~ q and p -a-> p', transfer the transition to
    the concrete body q and refute it by brute-force inversion. *)
Ltac prot_outProc_in_not_contra :=
  prot_outProc_in_not_unfold;
  match goal with
  | [B : ?p ~p~ ?q, TR : ?p -PA- ?a -PA> ?p' |- _] =>
    let q' := fresh "q'" in let TR' := fresh "TR'" in
    destruct (bisim_disc_match _ _ _ _ B TR) as [q' TR'];
    prot_outProc_in_not_body; solve [prot_outProc_in_not_inv]
  end.
(* end helpers *)

Theorem prot_outProc_in_not (p p' : ProcTerm) (v : list BaseType) : 
  p -PA- chanOutProc ;? v -PA> p' -> protocolState p -> False.
Proof.
  intros TR PS. inversion PS as [p1 p2 p3 BS OS LS]; subst; clear PS.
  inversion TR; subst; clear TR.
  - inversion BS; prot_outProc_in_not_contra.
  - match goal with [V : p2 $||$ p3 -PA- _ -PA> _ |- _] =>
      inversion V; subst; clear V end.
    + inversion OS; prot_outProc_in_not_contra.
    + inversion LS; prot_outProc_in_not_contra.
Qed.
(**Proof sketch: Brute force. Because none of its constituents can input on said channel.*)

Theorem bc_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem bc_abort_in_not (p p' : ProcTerm) : 
  p -PA- chanAbort*? -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem listen_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> listenerState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis of all listener states and none of them are enabled on this action*)

(**The two cases where the overlap component can output on mCurr.*)
Theorem ovlp_mCurr_out (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> overlapState p ->
  (switchCurrState p /\ switchListenState p') \/
  (tfsCurrState p /\ tfsBcState p').
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.
(**Proof: Brute force analysis on overlap states and show that these are the only two matches*)

Lemma bc_abort_out_not (p p' : ProcTerm) : 
  p -PA- chanAbort;! [] -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.

Lemma ovlp_abort_out_not (p p' : ProcTerm) : 
  p -PA- chanAbort;! [] -PA> p' -> overlapState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.

(**The two cases where the overlap component can output on mCurr.*)
(* begin helpers for ovlp_abort_in *)
(** A bisimilarity transfers a discrete transition together with the
    bisimilarity of the derivatives. *)
Lemma ovlp_abort_in_bisim_step p q a p' : p ~p~ q -> p -PA- a -PA> p' ->
  exists q', q -PA- a -PA> q' /\ p' ~p~ q'.
Proof.
  intros B TR. inversion B as [F _].
  destruct (F _ _ (stepPDisc _ _ _ TR)) as [q' [TQ BQ]].
  exists q'. split; [ | exact BQ]. inversion TQ; subst; assumption.
Qed.

(** A process name applied to arguments is bisimilar to its unfolded body. *)
Lemma ovlp_abort_in_appbisim n l2 :
  app n l2 ~p~ subProcTerm (listsToSub (fst (def n)) l2) (snd (def n)).
Proof.
  constructor.
  - intros a p' H. exists p'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc.
      match goal with [V : stepDiscProc (app n l2) _ _ |- _] =>
        inversion V; subst end.
      match goal with [E : def n = _ |- _] => rewrite E end. assumption.
    + apply stepPTimed.
      match goal with [V : stepTimedProc (app n l2) _ _ |- _] =>
        inversion V; subst end.
      match goal with [E : def n = _ |- _] => rewrite E end. assumption.
  - intros a q' H. exists q'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc. eapply stepDpApp; [apply surjective_pairing | eassumption].
    + apply stepPTimed. eapply stepTpApp; [apply surjective_pairing | eassumption].
Qed.

(** Specialisation to parameterless process names. *)
Lemma ovlp_abort_in_appbisim0 n p : def n = ([], p) -> app n [] ~p~ p.
Proof.
  intro D. eapply bisim_trans. apply (ovlp_abort_in_appbisim n []).
  rewrite D. cbn [fst snd listsToSub]. rewrite subProc_id_eq. apply bisim_refl.
Qed.
(* end helpers *)

Theorem ovlp_abort_in (p p' : ProcTerm) (m : Mode) :
  p -PA- chanAbort*? -PA> p' -> overlapState p ->
  (dormantState p /\ dormantState p') \/
  ovAbortState p' \/
  (tfsCurrState p /\ tfsCurrState p') \/
  (tfsListenState p /\ tfsListenState p').
Proof.
  intros TR OS. inversion OS as [B | m0 t x y B]; prot_outProc_in_not_unfold.
  - left. split; [assumption | ].
    destruct (ovlp_abort_in_bisim_step _ _ _ _ B TR) as [q' [TQ BQ]].
    unfold dormant in TQ. prot_outProc_in_not_inv.
    eapply bisim_trans; [exact BQ | ].
    exact (ovlp_abort_in_appbisim0 dormantN dormant eq_refl).
  - right. left.
    destruct (ovlp_abort_in_bisim_step _ _ _ _ B TR) as [q' [TQ BQ]].
    unfold ovWait in TQ. prot_outProc_in_not_inv.
    eapply bisim_trans; [exact BQ | ].
    exact (ovlp_abort_in_appbisim0 ovAbortN ovAbort eq_refl).
Qed.
(**Proof: Brute force analysis of overlap states and these are the only ones that fit the transition*)

Theorem bc_mStable_out_not (p p' : ProcTerm) : 
  p -PA- chanMStable*! -PA> p' -> broadcastState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.

Theorem ovlp_mStable_out_not (p p' : ProcTerm) : 
  p -PA- chanMStable*! -PA> p' -> overlapState p -> False.
Proof.
  intros TR S. inversion S; prot_outProc_in_not_contra.
Qed.

(*NEEDS TO BE EDITED! PROTOCOL PROCESS HYPOTHESIS DOESN'T LOOK LIKE IT'S THERE.
NAME COULD BE CHANGED TO SOMETHING A BIT MORE NORMAL TOO.*)
Lemma gotMsg_state p p' m l :
  p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p'.
  Admitted. (*6*)
(**Proof: p is a protocol process, so can be decomposed into p1 | p2 | p3. Brute force on p1, p2 shows that these don't match. Brute force analysis on listener states shows that the only state that fits for p3 is gotMsgState.*)

(*LOCAL TIDY*)

Lemma link_ent_soft_disc p p' l l' h h' k k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p = p' \/ exists b, p -PA- b -PA> p'.
Proof.
  intro H. inversion H; subst;
  first [left; reflexivity | right; eexists; eassumption].
Qed.

(** Destructs any entities into constituent parts, looks for a
discrete entity transition in the goal, extracts a process transition
or a process equality from this.*)
Ltac link_entsoftdisc_tac :=
  destrEnts_norm; match goal with
  [V : [|_, _, _, _|] -EA- _ ->> [|_, _, _, _|] |- _] =>
  let U := fresh in let U1 := fresh "LES" in
  let U2 := fresh "LES" in
  lets U : link_ent_soft_disc V; elim_intro U U1 U2; [ | ex_flat];subst end.

(*Togo: beside link_partripdiscex_tac2*)
Ltac link_partripdiscex_tac_subst p1' p2' p3' :=
  match goal with
  [H : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?a -PA> ?p' |- _] =>
  let Q1 := fresh in lets Q1 : link_par_triple_discEx H;
  let U1 := fresh in decompEx3 Q1 p1' p2' p3' U1; subst
  end.

Ltac link_partripdiscex_tac_norm :=
  let p1' := fresh "p1'" in let p2' := fresh "p2'" in
  let p3' := fresh "p3'" in
  link_partripdiscex_tac_subst p1' p2' p3'.

(** If a parallel process triple can do an action, then the first component is either
preserved or it too can do some action.*)
(* begin helpers for link_par_triple_discW_1 *)
(** Shared by link_par_triple_discW_1/2/3: invert the triple-parallel step
(and the inner parallel step, if any), then close each case either by the
component being preserved or by exhibiting its own transition. *)
Ltac link_par_triple_discW_1_tac :=
  let H := fresh in intro H; inversion H; clear H; subst;
  repeat match goal with
  [V : parComp _ _ -PA- _ -PA> parComp _ _ |- _] => inversion V; clear V; subst
  end;
  first [left; reflexivity | right; eexists; eassumption].
(* end helpers *)

Lemma link_par_triple_discW_1 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p1 = p1' \/ exists a', p1 -PA- a' -PA> p1'.
Proof.
  link_par_triple_discW_1_tac.
Qed.
(*+*)
(** If a parallel process triple can do an action, then the second component is either
preserved or it too can do some action.*)
Lemma link_par_triple_discW_2 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p2 = p2' \/ exists a', p2 -PA- a' -PA> p2'.
Proof.
  link_par_triple_discW_1_tac.
Qed.
(*+*)
(** If a parallel process triple can do an action, then the third component is either
preserved or it too can do some action.*)
Lemma link_par_triple_discW_3 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p3 = p3' \/ exists a', p3 -PA- a' -PA> p3'.
Proof.
  link_par_triple_discW_1_tac.
Qed.

(* begin helpers for link_par_triple_out_neq1 *)
(** Shared by link_par_triple_{out,in}_neq{1,2,3}: split the triple-parallel
input/output step (lemma L = link_par_triple_out / link_par_triple_in) into
its three cases; the case for the changed component closes the goal, and the
other two contradict the disequality hypothesis. *)
Ltac link_par_triple_out_neq1_tac L :=
  let N := fresh in let H := fresh in let U := fresh in
  intros N H; lets U : L H;
  destruct U as [[? [? ?]] | [[? [? ?]] | [? [? ?]]]];
  first [ solve [split; [assumption | split; assumption]]
        | solve [exfalso; apply N; assumption] ].
(* end helpers *)

Lemma link_par_triple_out_neq1 p1 p1' p2 p2' p3 p3' c v :
  p1 <> p1' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p1 -PA- c ;! v -PA> p1' /\ p2 = p2' /\ p3 = p3'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_out.
Qed.

Lemma link_par_triple_out_neq2 p1 p1' p2 p2' p3 p3' c v :
  p2 <> p2' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p2 -PA- c ;! v -PA> p2' /\ p1 = p1' /\ p3 = p3'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_out.
Qed.

Lemma link_par_triple_out_neq3 p1 p1' p2 p2' p3 p3' c v :
  p3 <> p3' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p3 -PA- c ;! v -PA> p3' /\ p1 = p1' /\ p2 = p2'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_out.
Qed.

Lemma link_par_triple_in_neq1 p1 p1' p2 p2' p3 p3' c v :
  p1 <> p1' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p1 -PA- c ;? v -PA> p1' /\ p2 = p2' /\ p3 = p3'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_in.
Qed.

Lemma link_par_triple_in_neq2 p1 p1' p2 p2' p3 p3' c v :
  p2 <> p2' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p2 -PA- c ;? v -PA> p2' /\ p1 = p1' /\ p3 = p3'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_in.
Qed.

Lemma link_par_triple_in_neq3 p1 p1' p2 p2' p3 p3' c v :
  p3 <> p3' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p3 -PA- c ;?v -PA> p3' /\ p1 = p1' /\ p2 = p2'.
Proof.
  link_par_triple_out_neq1_tac link_par_triple_in.
Qed.

Ltac link_partripneq_out_tac :=
  let LPO := fresh "LPO" in
  match goal with
  [V : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?c ;! ?v -PA> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  match goal with
  | [V1 :  p1 <> p1' |- _ ] => lets LPO : link_par_triple_out_neq1 V1 V
  | [V1 :  p2 <> p2' |- _ ] => lets LPO : link_par_triple_out_neq2 V1 V
  | [V1 :  p3 <> p3' |- _ ] => lets LPO : link_par_triple_out_neq3 V1 V
  end;
  and_flat
  end.

Ltac link_partripneq_in_tac :=
  let LPO := fresh "LPO" in
  match goal with
  [V : ?p1 $||$ ?p2 $||$ ?p3 -PA- ?c ;? ?v -PA> ?p1' $||$ ?p2' $||$ ?p3' |- _] =>
  match goal with
  | [V1 :  p1 <> p1' |- _ ] => lets LPO : link_par_triple_in_neq1 V1 V
  | [V1 :  p2 <> p2' |- _ ] => lets LPO : link_par_triple_in_neq2 V1 V
  | [V1 :  p3 <> p3' |- _ ] => lets LPO : link_par_triple_in_neq3 V1 V
  end;
  and_flat
  end.  

Ltac link_partripneq_tac := first [link_partripneq_in_tac | link_partripneq_out_tac].

(* begin helpers for ovlp_abort_in_notNextSince *)
(** If p is bisimilar to both q and r, then any discrete action of q can be
matched by r. *)
Lemma ovlp_abort_in_notNextSince_aux p q r a q' :
  p ~p~ q -> p ~p~ r -> q -PA- a -PA> q' -> exists r', r -PA- a -PA> r'.
Proof.
  intros B1 B2 S. destruct B1 as [_ B1]. destruct B2 as [B2 _].
  apply stepPDisc in S. apply B1 in S. destruct S as [p' [S _]].
  apply B2 in S. destruct S as [r' [S _]]. inversion S; subst.
  eexists; eassumption.
Qed.

(** Search a sum of prefixes for an enabled input prefix. *)
Ltac ovlp_abort_in_notNextSince_step :=
  first [ apply stepDpIn; reflexivity
        | apply stepDpChoiceL; ovlp_abort_in_notNextSince_step
        | apply stepDpChoiceR; ovlp_abort_in_notNextSince_step ].

(** The dormant state can input a mode on mNext. *)
Lemma ovlp_abort_in_notNextSince_dorm m :
  exists r, liftNameProc dormantN -PA- chanMNext;? [baseMode m] -PA> r.
Proof.
  eexists. eapply stepDpApp; [reflexivity | ]. simpl.
  ovlp_abort_in_notNextSince_step.
Qed.

(** The ovAbort state can output on mStable. *)
Lemma ovlp_abort_in_notNextSince_ovab :
  exists r, liftNameProc ovAbortN -PA- chanMStable *! -PA> r.
Proof.
  eexists. eapply stepDpApp; [reflexivity | ]. simpl.
  apply stepDpOut. constructor.
Qed.

(** Brute-force inversion of discrete steps out of unfolded sums of prefixes. *)
Ltac ovlp_abort_in_notNextSince_inv := repeat match goal with
  | [W : sum _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  | [W : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  | [W : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  | [W : del _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  end.

Ltac ovlp_abort_in_notNextSince_ns X S' :=
  try unfold ovWaitState in X; try unfold ovReadyState in X;
  try unfold switchBcState in X; try unfold switchCurrState in X;
  try unfold ovWait in S'; try unfold ovReady in S';
  try unfold switchBc in S'; try unfold switchCurr in S';
  ovlp_abort_in_notNextSince_inv.
(* end helpers *)

Lemma ovlp_abort_in_notNextSince p p' :
  p -PA- chanAbort;? [] -PA> p' -> overlapState p -> ~ nextSinceState p'.
Proof.
  intros P O N. apply stepPDisc in P.
  destruct O as [D | m t x y D]; unfold dormantState, ovWaitState in D;
  destruct D as [D1 _]; apply D1 in P; destruct P as [q' [Q B]];
  inversion Q; subst; clear Q.
  - (* dormant: the only abort input leads back to dormant, which can
       input on mNext, unlike every nextSince state. *)
    match goal with [V : dormant -PA- _ -PA> _ |- _] => unfold dormant in V end.
    ovlp_abort_in_notNextSince_inv. simpl in B.
    destruct N as [m0 t0 x0 y0 X | m0 t0 l0 X | m0 X | m0 X];
    destruct (ovlp_abort_in_notNextSince_dorm m0) as [r S];
    edestruct (ovlp_abort_in_notNextSince_aux _ _ _ _ _ B X S) as [r' S'];
    clear S; ovlp_abort_in_notNextSince_ns X S'.
  - (* ovWait: the only abort input leads to ovAbort, which can output on
       mStable, unlike every nextSince state. *)
    match goal with [V : ovWait _ _ _ _ -PA- _ -PA> _ |- _] => unfold ovWait in V end.
    ovlp_abort_in_notNextSince_inv. simpl in B.
    destruct N as [m0 t0 x0 y0 X | m0 t0 l0 X | m0 X | m0 X];
    destruct ovlp_abort_in_notNextSince_ovab as [r S];
    edestruct (ovlp_abort_in_notNextSince_aux _ _ _ _ _ B X S) as [r' S'];
    clear S; ovlp_abort_in_notNextSince_ns X S'.
Qed.

Lemma listening_abort_contra p :
  listeningState p -> abortOvlpState p -> False.
Proof.
  intros L A. unfold listeningState, abortOvlpState in *.
  (* abortOvlp can output on abort; so p can, and hence so can listening. *)
  assert (S : abortOvlp -P- chanAbort *! -P> liftNameProc listeningN).
  { apply stepPDisc. unfold abortOvlp. apply stepDpOut. constructor. }
  destruct A as [_ A2]. apply A2 in S. destruct S as [p' [P1 _]].
  destruct L as [L1 _]. apply L1 in P1. destruct P1 as [q' [Q1 _]].
  inversion Q1; subst.
  match goal with [V : listening -PA- _ -PA> _ |- _] => unfold listening in V end.
  (* But listening is a sum of input prefixes: no output on abort. *)
  repeat match goal with
  | [W : sum _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  | [W : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion W; clear W; subst
  end.
Qed.

(*-LOCAL TIDY*)