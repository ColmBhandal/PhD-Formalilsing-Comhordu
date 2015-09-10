(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".  
Require Import LibTactics.

(***************************** Specialised Imports *****************************)

Require Import GenTacs.
Require Import StandardResults.
Require Import ComhBasics.
Require Import LanguageFoundations.
Require Import SoftwareLanguage.
Require Import ProtAuxDefs.
Require Import Bool.
Require Import EntityLanguage.
Require Import ProcEquiv.

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
Fixpoint genBaseList (n : nat) : list Base :=
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
Theorem listener_outProc_out_not (p p' : ProcTerm) (v : list Base) : 
  listenerState p -> p -PA- chanOutProc ;! v -PA> p' -> False. Admitted. (*5*)
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

Lemma goMsg_gotRange_track m m' l r p p' a :
  gotMsgState m l p -> gotRangeState m' r p' ->
  p -PA- a -PA> p' -> exists l',
  a = chanPos ;? [basePosition l'] /\
  r = mkDistance (dist l l' -nn- speedMax *nn* msgLatency). Admitted.

Lemma currOK_listening_track m p p' a : currOKState m p ->
  listeningState p' -> p -PA- a -PA> p' -> a = (chanMStable *?).
  Admitted.

Lemma abortOvlp_listening_track (p p' : ProcTerm) (a : DiscAct) :
  abortOvlpState p -> listeningState p' -> p -PA- a -PA> p' ->
  a = chanAbort;! []. Admitted.

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
  backtrack_weed p. Admitted.

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

Theorem currOK_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  p -PA- a -PA> p' -> currOKState m'' p ->
  (exists m, nextEqState m m'' p') \/
  listeningState p'. Admitted. (*#fwd-track*)

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
  Admitted. (*#fwd-track*)

Theorem abortOvlp_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> abortOvlpState p -> listeningState p'.
  Admitted. (*#fwd-track*)

Lemma tfsStart_next (p p' : ProcTerm) (a : DiscAct) :
  p -PA- a -PA> p' -> tfsStartState p ->
  exists m, tfsNextState m p'.
  Admitted. (*#fwd-track*)
  
(****************** Conditionals ******************)
(* In here are resuls relating conditional state predicates to their branches.
In general, the results are of the form "If some conditional state predicate S
is true, and the condition is true (say), then the state predicate S' corresponding
to the true branch of S is true"*)

Lemma currEq_cond_true m m'' p :
  m = m'' -> currEqState m m'' p -> badOvlpState p.
  Admitted.

Lemma currEq_cond_false m m'' p :
  m <> m'' -> currEqState m m'' p -> currOKState m'' p.  
  Admitted.

Lemma nextEq_cond_true m' m'' p :
  m' = m'' -> nextEqState m' m'' p -> abortOvlpState p.  
  Admitted.

Lemma nextEq_cond_false m' m'' p :
  m' <> m'' -> nextEqState m' m'' p -> listeningState p.  
  Admitted.

Lemma currPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r -> currPincCheckState m m'' r p ->
  badOvlpState p.  
  Admitted.

Lemma currPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  currPincCheckState m m'' r p -> currCompState m'' r p.  
  Admitted.

Lemma nextPincCheck_cond_true m m'' (r : Distance) p :
  possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> abortOvlpState p.  
  Admitted.

Lemma nextPincCheck_cond_false m m'' (r : Distance) p :
  ~possiblyIncompatible m m'' r ->
  nextPincCheckState m m'' r p -> listeningState p.  
  Admitted.

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

Lemma ovReady_del_pres m t l p p' d :
  ovReadyState m t l p -> p -PD- d -PD> p' ->
  ovReadyState m t l p'. Admitted. (*#delay-pres*)

Lemma switchBc_del_pres m p p' d :
  switchBcState m p -> p -PD- d -PD> p' ->
  switchBcState m p'. Admitted. (*#delay-pres*)

Lemma switchCurr_del_pres p p' d :
  switchCurrState p -> p -PD- d -PD> p' ->
  switchCurrState p'. Admitted. (*#delay-pres*)

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
  Admitted. (*6*)
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
  (c : Channel) (v : list Base) :
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
  (c : Channel) (v : list Base) :
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

Lemma link_reach_triple_tau (p1 p2 p3 p1' p2' p3' : ProcTerm) :
  p1 $||$ p2 $||$ p3 -PA- tauAct -PA> p1' $||$ p2' $||$ p3' ->
  protocolState (p1 $||$ p2 $||$ p3) -> exists c v,
  (p1 -PA- c ;! v -PA> p1' /\ p2 -PA- c ;? v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;? v -PA> p1' /\ p2 -PA- c ;! v -PA> p2' /\ p3 = p3') \/
  (p1 -PA- c ;! v -PA> p1' /\ p3 -PA- c ;? v -PA> p3' /\ p2 = p2') \/
  (p1 -PA- c ;? v -PA> p1' /\ p3 -PA- c ;! v -PA> p3' /\ p2 = p2') \/
  (p2 -PA- c ;! v -PA> p2' /\ p3 -PA- c ;? v -PA> p3' /\ p1 = p1') \/
  (p2 -PA- c ;? v -PA> p2' /\ p3 -PA- c ;! v -PA> p3' /\ p1 = p1').
  intros. Admitted. (*6*)
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

Theorem bc_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> broadcastState p ->
  bcReadyState m l p /\ bcWaitState m (period m) p'. Admitted. (*6*)
(**Proof: Brute force try all the other possible broadcast states (auto tactic) and this is the only one that matches*)

Theorem ovlp_outProc_out (p p' : ProcTerm) (m : Mode) (l : Position) : 
  p -PA- chanOutProc ;! [baseMode m, basePosition l] -PA> p' -> overlapState p ->
  exists t f, ovReadyState m t l p /\ 
  ovWaitState m (minusTime t (period m) f) (minusTime t (period m) f) (period m) p'.
  Admitted. (*6*)
(**Proof: Brute force. Analogous to bc_outProc_out but with overlap states*)

(**A protocol process cannot input on the channel outProc.*)
Theorem prot_outProc_in_not (p p' : ProcTerm) (v : list Base) : 
  p -PA- chanOutProc ;? v -PA> p' -> protocolState p -> False. Admitted. (*6*)
(**Proof sketch: Brute force. Because none of its constituents can input on said channel.*)

Theorem bc_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> broadcastState p -> False. Admitted. (*6*)
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem bc_abort_in_not (p p' : ProcTerm) : 
  p -PA- chanAbort*? -PA> p' -> broadcastState p -> False. Admitted. (*6*)
(**Proof: Brute force analysis of all broadcast states and none of them are enabled on this action*)

Theorem listen_mCurr_out_not (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> listenerState p -> False. Admitted. (*6*)
(**Proof: Brute force analysis of all listener states and none of them are enabled on this action*)

(**The two cases where the overlap component can output on mCurr.*)
Theorem ovlp_mCurr_out (p p' : ProcTerm) : 
  p -PA- chanMCurr ;! [] -PA> p' -> overlapState p ->
  (switchCurrState p /\ switchListenState p') \/
  (tfsCurrState p /\ tfsBcState p'). Admitted. (*6*)
(**Proof: Brute force analysis on overlap states and show that these are the only two matches*)

Lemma bc_abort_out_not (p p' : ProcTerm) : 
  p -PA- chanAbort;! [] -PA> p' -> broadcastState p -> False.
  Admitted.

Lemma ovlp_abort_out_not (p p' : ProcTerm) : 
  p -PA- chanAbort;! [] -PA> p' -> overlapState p -> False.
  Admitted.

(**The two cases where the overlap component can output on mCurr.*)
Theorem ovlp_abort_in (p p' : ProcTerm) (m : Mode) :
  p -PA- chanAbort*? -PA> p' -> overlapState p ->
  (dormantState p /\ dormantState p') \/
  ovAbortState p' \/
  (tfsCurrState p /\ tfsCurrState p') \/
  (tfsListenState p /\ tfsListenState p'). Admitted. (*6*)
(**Proof: Brute force analysis of overlap states and these are the only ones that fit the transition*)

Theorem bc_mStable_out_not (p p' : ProcTerm) : 
  p -PA- chanMStable*! -PA> p' -> broadcastState p -> False. Admitted.

Theorem ovlp_mStable_out_not (p p' : ProcTerm) : 
  p -PA- chanMStable*! -PA> p' -> overlapState p -> False. Admitted.

(*NEEDS TO BE EDITED! PROTOCOL PROCESS HYPOTHESIS DOESN'T LOOK LIKE IT'S THERE.
NAME COULD BE CHANGED TO SOMETHING A BIT MORE NORMAL TOO.*)
Lemma gotMsg_state p p' m l :
  p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p'.
  Admitted. (*6*)
(**Proof: p is a protocol process, so can be decomposed into p1 | p2 | p3. Brute force on p1, p2 shows that these don't match. Brute force analysis on listener states shows that the only state that fits for p3 is gotMsgState.*)

(*LOCAL TIDY*)

Lemma link_ent_soft_disc p p' l l' h h' k k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  p = p' \/ exists b, p -PA- b -PA> p'. Admitted.

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
Lemma link_par_triple_discW_1 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p1 = p1' \/ exists a', p1 -PA- a' -PA> p1'. Admitted.
(*+*)
(** If a parallel process triple can do an action, then the second component is either
preserved or it too can do some action.*)
Lemma link_par_triple_discW_2 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p2 = p2' \/ exists a', p2 -PA- a' -PA> p2'. Admitted.
(*+*)
(** If a parallel process triple can do an action, then the third component is either
preserved or it too can do some action.*)
Lemma link_par_triple_discW_3 p1 p1' p2 p2' p3 p3' a :
  p1 $||$ p2 $||$ p3 -PA- a -PA> p1' $||$ p2' $||$ p3' ->
  p3 = p3' \/ exists a', p3 -PA- a' -PA> p3'. Admitted.

Lemma link_par_triple_out_neq1 p1 p1' p2 p2' p3 p3' c v :
  p1 <> p1' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p1 -PA- c ;! v -PA> p1' /\ p2 = p2' /\ p3 = p3'.
  (*Proof: link_partripout_tac U*) Admitted.

Lemma link_par_triple_out_neq2 p1 p1' p2 p2' p3 p3' c v :
  p2 <> p2' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p2 -PA- c ;! v -PA> p2' /\ p1 = p1' /\ p3 = p3'.
  (*Proof: link_partripout_tac U*) Admitted.

Lemma link_par_triple_out_neq3 p1 p1' p2 p2' p3 p3' c v :
  p3 <> p3' ->
  p1 $||$ p2 $||$ p3 -PA- c ;! v -PA> p1' $||$ p2' $||$ p3' ->
  p3 -PA- c ;! v -PA> p3' /\ p1 = p1' /\ p2 = p2'.
  (*Proof: link_partripout_tac U*) Admitted.

Lemma link_par_triple_in_neq1 p1 p1' p2 p2' p3 p3' c v :
  p1 <> p1' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p1 -PA- c ;? v -PA> p1' /\ p2 = p2' /\ p3 = p3'.
  (*Proof: link_partripout_tac U*) Admitted.

Lemma link_par_triple_in_neq2 p1 p1' p2 p2' p3 p3' c v :
  p2 <> p2' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p2 -PA- c ;? v -PA> p2' /\ p1 = p1' /\ p3 = p3'.
  (*Proof: link_partripout_tac U*) Admitted.

Lemma link_par_triple_in_neq3 p1 p1' p2 p2' p3 p3' c v :
  p3 <> p3' ->
  p1 $||$ p2 $||$ p3 -PA- c ;? v -PA> p1' $||$ p2' $||$ p3' ->
  p3 -PA- c ;?v -PA> p3' /\ p1 = p1' /\ p2 = p2'.
  (*Proof: link_partripout_tac U*) Admitted.

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

Lemma ovlp_abort_in_notNextSince p p' :
  p -PA- chanAbort;? [] -PA> p' -> overlapState p -> ~ nextSinceState p'.
  Admitted.

Lemma listening_abort_contra p :
  listeningState p -> abortOvlpState p -> False.
  (*Proof: Use state_pred_elim (bisim version).*)
  Admitted.

(*-LOCAL TIDY*)