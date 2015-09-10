(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".

(***************************** Specialised Imports *****************************)

Require Import StandardResults.
Require Import ComhBasics.
Require Import LanguageFoundations.
Require Import SoftwareLanguage.
Require Import GenTacs.

(********************** Bisimulation **********************)

(** Single step equivlance on process terms is defined as a bisimulation.*)
CoInductive bisimulation p q : Prop :=
  bisimWitness :
  (forall a p', p -P- a -P> p' ->
  exists q', q -P- a -P> q' /\ bisimulation p' q') ->
  (forall a q', q -P- a -P> q' ->
  exists p', p -P- a -P> p' /\ bisimulation p' q') ->
  bisimulation p q.
Notation "p ~p~ q" := (bisimulation p q) (at level 70).

(*** Generic Properties of the Relation ***)

(** The siumlation relation is reflexive.*)
CoFixpoint bisim_refl p : p ~p~ p. constructor.
  intros. exists p'. split. assumption. apply bisim_refl.
  intros. exists q'. split. assumption. apply bisim_refl. Qed.

(** The siumlation relation is transitive.*)
CoFixpoint bisim_trans p1 p2 p3 : p1 ~p~ p2 -> p2 ~p~ p3 ->
  p1 ~p~ p3. introz U. constructor.
  intros a p'. introz U. apply U in U1. ex_flat. and_flat.
  apply U0 in AND. ex_flat. and_flat. exists x0. split.
  assumption. eapply bisim_trans; eassumption.
  intros a q'. introz U. apply U0 in U1. ex_flat. and_flat.
  apply U in AND. ex_flat. and_flat. exists x0. split.
  assumption. eapply bisim_trans; eassumption. Qed.

CoFixpoint bisim_symm p q : p ~p~ q -> q ~p~ p.
  intros. inversion H. constructor.
  intros. apply H1 in H2. ex_flat. and_flat.
  apply bisim_symm in AND0. exists x. split; assumption.
  intros. apply H0 in H2. ex_flat. and_flat.
  apply bisim_symm in AND0. exists x. split; assumption.
  Qed.

(*** Slightly more Specific ***)

(*TIDY*)

(*TOGO: GenTacs*)
Ltac plus_le_left_red := match goal with [Q : ?a + ?b = ?a + ?c |-
  ?b = ?c] => replace b with (a + b - a);[ | ring];
  rewrite Q; ring end.

Require Import LibTactics.
Open Scope R_scope.

(*TOGO: Wherever the sort shit is.*)

(** If a is in the sort relation for d, p, and p is capable of doing a delay
of d, then there is some d' < d and p' such that p can delay to this p' by
d' and the resulting p' is capable of doing the action a.*)
Lemma sort_del a d p : sort a d p -> timedActEnabled p d ->
  (exists p' d', p -PD- d' -PD> p' /\ d' < d /\ discActEnabled p' a)
  \/ discActEnabled p a.
  introz U. invertClearAs2 U0 p' PD.
  (*Induction on the delay rule.*)
  induction PD; inversion U; subst.
  (*Out pfx*)
  right; do 2 econstructor; assumption.
  (*In pfx*)
  right; do 2 econstructor. symmetry. assumption.
  (*If true*)
  apply IHPD in H5. clear IHPD. invertClear H5. ex_flat. and_flat.
  invertClear AND2.
  left. repeat eexists; try eassumption. econstructor; eassumption.
  right. inversion H0. do 2 econstructor; eassumption.
  (*If false*)
  apply evalBoolExpTrueTot in H4. rewrite H in H4. inversion H4.
  (*Sum left*)
  apply IHPD1 in H2. clear IHPD1 IHPD2.
  invertClear H2; ex_flat; and_flat. left.
  assert (timedActEnabled p2 x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD2. assumption. invertClearAs2 TAE q' TP.
  do 2 eexists; try eassumption. split; [ | split; [eassumption | ]].
  econstructor; eassumption. apply daeSumL; assumption.
  right. apply daeSumL; assumption.
  (*Sum right*)
  apply IHPD2 in H2. clear IHPD1 IHPD2.
  invertClear H2; ex_flat; and_flat. left.
  assert (timedActEnabled p1 x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD1. assumption. invertClearAs2 TAE q' TP.
  do 2 eexists; try eassumption. split; [ | split; [eassumption | ]].
  econstructor; eassumption. apply daeSumR; assumption.
  right. apply daeSumR; assumption.
  (*Par left*)
  apply IHPD1 in H3. clear IHPD1 IHPD2.
  invertClear H3; ex_flat; and_flat. left.
  assert (timedActEnabled q x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD2. assumption.
  invertClearAs2 TAE q0 TP. do 2 eexists; try eassumption.
  split; [ | split; [eassumption | ]]. econstructor; try eassumption.
  unfold not. intros. assert (x0 <= d) as XLE. apply Rlt_le. assumption.
  eapply H; eapply sortLe; eassumption.
  apply daeParL; assumption.
  right. apply daeParL; assumption. 
  (*Par right*)
  apply IHPD2 in H3. clear IHPD1 IHPD2.
  invertClear H3; ex_flat; and_flat. left.
  assert (timedActEnabled p x0) as TAE. eapply delShortenStrict.
  econstructor. apply PD1. assumption.
  invertClearAs2 TAE q0 TP. do 2 eexists; try eassumption.
  split; [ | split; [eassumption | ]]. econstructor; try eassumption.
  unfold not. intros. assert (x0 <= d) as XLE. apply Rlt_le. assumption.
  eapply H; eapply sortLe; eassumption.
  apply daeParR; assumption.
  right. apply daeParR; assumption.
  (*App*)
  rewrite H in H4. invertClear H4; subst.
  apply IHPD in H5. clear IHPD. or_flat. ex_flat. and_flat.
  left. do 2 eexists. split. econstructor; eassumption.
  split; assumption. right. eapply daeApp; eassumption.
  (*Del pfx*)
  rewrite H in H4. invertClear H4. subst.
  assert (d0 = d). apply delayEqR.
  plus_le_left_red.
  clear H0. subst. apply IHPD in H5.
  or_flat. ex_flat. and_flat. left. exists x (t0 +dt+ x0).
  split. apply stepTpDelAdd; assumption. split.
  apply Rplus_le_lt_compat. apply Rle_refl. assumption.
  assumption.
  (*Is the time 0 or some non-zero time.*)
  lets TLZ : Rle_lt_or_eq_dec zeroTime (nonneg t0) (cond_nonneg t0).
  (*Sub-case: Positive time, then we must assert a delay.*)
  elim_intro TLZ TL TE. mkdel t0 TL d0. assert (d0 <= t0) as Q.
  rewrite Heqd0. apply Rle_refl. left. exists ($< minusTime t0 d0 Q >$ p).
  exists d0. split. constructor. assumption. split.
  simpl. eapply Rle_lt_trans. eassumption. Rplus_lt_tac.
  delPos. subst. apply daeTimeout. simpl.
  apply evalExp_evalExpFunTime. lets EB : evalBase zeroTime.
  my_applys_eq EB. repeat f_equal. apply timeEqR. simpl.
  ring. assumption.
  (*Sub-case: Zero time, then the action is available now.*)
  right. apply daeTimeout. my_applys_eq H. f_equal.
  apply timeEqR. inversion TE. rewrite H1. simpl. 
  symmetry. assumption. assumption.
  (*Some contradictions that were floating around...?*)
  rewrite H0 in H5. inversion H5. rewrite H2 in H.
  false. eapply Rle_not_lt. apply H. simpl. Rplus_lt_tac.
  delPos.
  rewrite H in H4. inversion H4. Qed.

(*-TOGO*)

Lemma bisim_dae p q a : p ~p~ q -> discActEnabled p a ->
  discActEnabled q a. introz U. invertClear U0.
  apply stepPDisc in H. apply U in H. ex_flat. and_flat.
  econstructor. inversion AND. eassumption. Qed.

(*-TIDY*)

Lemma bisim_del_sort p q a d : p ~p~ q -> timedActEnabled p d ->
  sort a d p -> sort a d q. introz U.
  lets SD : sort_del U1 U0. elim_intro SD PD DA.
  ex_flat. and_flat. apply stepPTimed in AND. apply U in AND.
  ex_flat. and_flat. invertClear AND.
  lets DAX : bisim_dae AND0 AND2.
  apply sort_complete. split. eapply sortNotTau. eassumption.
  right. exists x0 x1. repeat (split; [assumption | ]).
  assumption.
  lets BD : bisim_dae U DA. apply enabledInSort. assumption.
  eapply sortNotTau. eassumption. Qed.

(*** Bisimulation and Syntax ***)

CoFixpoint choice_bisim_symm p1 p2 : p1 $+$ p2 ~p~ p2 $+$ p1. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  exists p'. split. apply stepPDisc. apply stepDpChoiceR.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  exists p'. split. apply stepPDisc. apply stepDpChoiceL.
  assumption. apply bisim_refl.
  (*Timed case*)
  inversion H0. exists (p2' $+$ p1'). split.
  apply stepPTimed. constructor; assumption.
  apply choice_bisim_symm .
  (*Repeat everything again for symmetric case*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  exists q'. split. apply stepPDisc. apply stepDpChoiceR.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  exists q'. split. apply stepPDisc. apply stepDpChoiceL.
  assumption. apply bisim_refl.
  (*Timed case*)
  inversion H0. exists (p2' $+$ p1'). split.
  apply stepPTimed. constructor; assumption.
  apply choice_bisim_symm . Qed.

CoFixpoint par_bisim_symm p1 p2 : p1 $||$ p2 ~p~ p2 $||$ p1. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Left sub-case*)
  exists (p2 $||$ p'0). split. apply stepPDisc. apply stepDpParR.
  assumption. apply par_bisim_symm.
  (*Right sub-case*)
  exists (q' $||$ p1). split. apply stepPDisc. apply stepDpParL.
  assumption. apply par_bisim_symm.
  (*Sync LR*)
  exists (q' $||$ p'0). split. apply stepPDisc. eapply stepDpSyncRL;
  eassumption. apply par_bisim_symm.
  (*Sync RL*)
  exists (q' $||$ p'0). split. apply stepPDisc. eapply stepDpSyncLR;
  eassumption. apply par_bisim_symm.
  (*Timed case*)
  inversion H0. exists (q' $||$ p'0). split.
  apply stepPTimed. constructor; try assumption.
  unfold not. intros. eapply H9. eassumption.
  my_applys_eq H10. symmetry. apply complementInvol.
  apply par_bisim_symm.
  (*Repeat everything again for symmetric case-
  with left and right reversed.*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Right sub-case*)
  exists (p1 $||$ p'). split. apply stepPDisc. apply stepDpParR.
  assumption. apply par_bisim_symm.
  (*Left sub-case*)
  exists (q'0 $||$ p2). split. apply stepPDisc. apply stepDpParL.
  assumption. apply par_bisim_symm.
  (*Sync LR*)
  exists (q'0 $||$ p'). split. apply stepPDisc. eapply stepDpSyncRL;
  eassumption. apply par_bisim_symm.
  (*Sync RL*)
  exists (q'0 $||$ p'). split. apply stepPDisc. eapply stepDpSyncLR;
  eassumption. apply par_bisim_symm.
  (*Timed case*)
  inversion H0. exists (q'0 $||$ p'). split.
  apply stepPTimed. constructor; try assumption.
  unfold not. intros. eapply H9. eassumption.
  my_applys_eq H10. symmetry. apply complementInvol.
  apply par_bisim_symm. Qed.

CoFixpoint choice_bism_unit_r p : p $+$ nilProc ~p~ p.
  constructor; intros; inversion H.
  (*Discrete case*)
  inversion H0; subst.
  (*Left sub-case*)
  apply stepPDisc in H7. exists p'. split.
  assumption. apply bisim_refl.
  (*Right sub-case*)
  inversion H7.
  (*Timed case*)
  inversion H0; inversion H8; subst.
  exists p1'. split. apply stepPTimed.
  assumption. apply choice_bism_unit_r.
  (*Right to left case is easy.*)
  (*Discrete case*)
  subst. exists q'. split. apply stepPDisc.
  eapply stepDpChoiceL. assumption. apply bisim_refl.
  (*Timed case*)
  subst. exists (q' $+$ nilProc). split. apply stepPTimed.
  eapply stepTpSum. assumption. constructor.
  apply choice_bism_unit_r. Qed.

CoFixpoint choice_bism_unit_l p : nilProc $+$ p ~p~ p.
  eapply bisim_trans. apply choice_bisim_symm.
  apply choice_bism_unit_r. Qed.

CoFixpoint choice_bisim_context p1 p2 p1' p2' :
  p1 ~p~ p1' -> p2 ~p~ p2' ->
  p1 $+$ p2 ~p~ p1' $+$ p2'. introz U. constructor.
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  apply stepPDisc in H7. apply U in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceL. assumption. assumption.
  (*Right sub-case*)
  apply stepPDisc in H7. apply U0 in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceR. assumption. assumption.
  (*Timed case*)
  inversion H0.
  apply stepPTimed in H5. apply stepPTimed in H8.
  apply U in H5. apply U0 in H8. ex_flat. and_flat.
  exists (x0 $+$ x). inversion AND. inversion AND1.
  split. apply stepPTimed. constructor; assumption.
  apply choice_bisim_context; assumption.
  (*Repeat everything again for symmetric case*)
  intros. inversion H.
  (*Discrete case*)
  inversion H0.
  (*Left sub-case*)
  apply stepPDisc in H7. apply U in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceL. assumption. assumption.
  (*Right sub-case*)
  apply stepPDisc in H7. apply U0 in H7. ex_flat. and_flat.
  exists x. split. apply stepPDisc. inversion AND.
  apply stepDpChoiceR. assumption. assumption.
  (*Timed case*)
  inversion H0.
  apply stepPTimed in H5. apply stepPTimed in H8.
  apply U in H5. apply U0 in H8. ex_flat. and_flat.
  exists (x0 $+$ x). inversion AND. inversion AND1.
  split. apply stepPTimed. constructor; assumption.
  apply choice_bisim_context; assumption.
  Qed.

(*LOCAL TIDY*)

Ltac bisim_disc_tac_parm U V :=
  apply stepPDisc in V; apply U in V; ex_flat; and_flat;
  match goal with [U1 : _ -P- _ -P> _ |- _] => inversion U1; subst end.

(**If there are bisimilar processes in the context and there's a discrete
transition from the first bisimilar process then this tactic generates a
matching discrete transition from the second bisimilar process.*)
Ltac bisim_disc_tac :=
  match goal with
  | [U : ?p ~p~ ?q, V : ?p -PA- _ -PA> _ |- _] =>
    bisim_disc_tac_parm U V
  | [U : ?p ~p~ ?q, V : ?q -PA- _ -PA> _ |- _] =>
    bisim_disc_tac_parm U V
  end.

Ltac bisim_timed_tac_parm U V :=
  apply stepPTimed in V; apply U in V; ex_flat; and_flat;
  match goal with [U1 : _ -P- _ -P> _ |- _] => inversion U1; subst end.

(**Similar to bisim_disc_tac but matches a delay rather than a discrete step.*)
Ltac bisim_timed_tac :=
  match goal with
  | [U : ?p ~p~ ?q, V : ?p -PD- _ -PD> _ |- _] =>
    bisim_timed_tac_parm U V
  | [U : ?p ~p~ ?q, V : ?q -PD- _ -PD> _ |- _] =>
    bisim_timed_tac_parm U V
  end.

(*-LOCAL TIDY*)

Lemma cond_bisim_lift_true p q b : p ~p~ q -> evalBoolExp b true ->
  b $> p ~p~ b $> q. intros. constructor.
  intros. inversion H1.
  (*Disc case*)
  inversion H2.
  bisim_disc_tac. exists x. split. do 2 constructor;
  assumption. assumption.
  (*Timed case*)
  inversion H2. bisim_timed_tac. exists x. split.
  do 2 constructor; assumption. assumption.
  apply evalBoolExpTrueTot in H0. rewrite H0 in H9.
  inversion H9.
  (*Repeat everything. Ugh.*)
  intros. inversion H1.
  (*Disc case*)
  inversion H2.
  bisim_disc_tac. exists x. split. do 2 constructor;
  assumption. assumption.
  (*Timed case*)
  inversion H2. bisim_timed_tac. exists x. split.
  do 2 constructor; assumption. assumption.
  apply evalBoolExpTrueTot in H0. rewrite H0 in H9.
  inversion H9.
  Qed.

CoFixpoint par_bisim_context p p' q :
  p ~p~ p' -> p $||$ q ~p~ p' $||$ q.
  intros. constructor. 
  (*We discriminate the cases*)
  intros. invertClear H0; subst.
  (*First, the discrete case.*)
  invertClear H1; subst.
  (*Sub case: left component action*)
  bisim_disc_tac. exists (x $||$ q). split. apply stepPDisc.
  apply stepDpParL. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: right component action*)
  exists (p' $||$ q'). split. apply stepPDisc.
  apply stepDpParR. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: left to right synch*)
  bisim_disc_tac. exists (x $||$ q'). split. apply stepPDisc.
  eapply stepDpSyncLR; eassumption. apply par_bisim_context.
  assumption.
  (*Sub case: right to left synch*)
  bisim_disc_tac. exists (x $||$ q'). split. apply stepPDisc.
  eapply stepDpSyncRL; eassumption. apply par_bisim_context.
  assumption.
  (*Now the delay case. This is where we need to use that quirky,
  beautiful little result about sort.*)
  invertClear H1; subst. bisim_timed_tac.
  exists (x $||$ q'). split. do 2 constructor; [assumption.. | ].
  unfold not. intros. eapply H7. eapply bisim_del_sort.
  apply bisim_symm. eassumption. econstructor. eassumption.
  eassumption. assumption.
  apply par_bisim_context. assumption.
  (*Symmetric case*)
  (*We discriminate the cases*)
  intros. invertClear H0; subst.
  (*First, the discrete case.*)
  invertClear H1; subst.
  (*Sub case: left component action*)
  bisim_disc_tac. exists (x $||$ q). split. apply stepPDisc.
  apply stepDpParL. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: right component action*)
  exists (p $||$ q'0). split. apply stepPDisc.
  apply stepDpParR. assumption. apply par_bisim_context.
  assumption.
  (*Sub case: left to right synch*)
  bisim_disc_tac. exists (x $||$ q'0). split. apply stepPDisc.
  eapply stepDpSyncLR; eassumption. apply par_bisim_context.
  assumption.
  (*Sub case: right to left synch*)
  bisim_disc_tac. exists (x $||$ q'0). split. apply stepPDisc.
  eapply stepDpSyncRL; eassumption. apply par_bisim_context.
  assumption.
  (*Now the delay case. This is where we need to use that quirky,
  beautiful little result about sort.*)
  invertClear H1; subst. bisim_timed_tac.
  exists (x $||$ q'0). split. do 2 constructor; [assumption.. | ].
  unfold not. intros. eapply H7. eapply bisim_del_sort.
  apply bisim_symm. apply bisim_symm in H. eassumption. econstructor.
  eassumption. eassumption. assumption.
  apply par_bisim_context. assumption.
  Qed.

Corollary par_bisim_context2 p q q' :
  q ~p~ q' -> p $||$ q ~p~ p $||$ q'. intros.
  eapply bisim_trans. apply par_bisim_symm.
  eapply bisim_trans. apply par_bisim_context.
  eassumption. apply par_bisim_symm. Qed.

Corollary par_bisim_context_strong p p' q q' :
  p ~p~ p' -> q ~p~ q' -> p $||$ q ~p~ p' $||$ q'.
  intros. eapply bisim_trans. apply par_bisim_context.
  eassumption. apply par_bisim_context2. assumption. Qed.

Corollary par_bisim_triple p1 p1' p2 p2' p3 p3' :
  p1 ~p~ p1' -> p2 ~p~ p2' -> p3 ~p~ p3' ->
  p1 $||$ p2 $||$ p3 ~p~ p1' $||$ p2' $||$ p3'.
  introz U. apply par_bisim_context_strong.
  assumption. apply par_bisim_context_strong;
  assumption. Qed.

Lemma cond_bisim_true p b : evalBoolExp b true ->
  b $> p ~p~ p. introz U.
  split; intros. exists p'. split;[ | apply bisim_refl].
  inversion H; inversion H0. apply stepPDisc. assumption.
  apply stepPTimed. assumption. apply evalBoolExpTrueTot in U.
  rewrite U in H7. inversion H7.
  (*Other direction*)
  inversion H. exists q'. split;[ | apply bisim_refl]. 
  do 2 constructor. assumption. apply evalBoolExpTrueTot.
  assumption. exists q'. split;[ | apply bisim_refl].
  do 2 constructor. assumption. apply evalBoolExpTrueTot.
  assumption. Qed.

(*TOGO: LanguageFoundations*)

Theorem evalBoolExpFalseTot : forall (e : BoolExp),
  evalBoolExp e false <-> evalBoolExpFunTot e = false.
  split; intros. apply evalBoolExpRelFun in H.
  unfold evalBoolExpFunTot. rewrite H. reflexivity.
  unfold evalBoolExpFunTot in H.
  remember (evalBoolExpFun e) as EV. destruct EV.
  subst. symmetry in HeqEV. apply evalBoolExpFunRel in HeqEV.
  assumption. symmetry in HeqEV. Admitted.
  

(*TOGO*)

CoFixpoint cond_bisim_false p b : evalBoolExpFunTot b = false ->
  b $> p ~p~ nilProc. introz U. split; intros. 
  inversion H; inversion H0.
  apply evalBoolExpTrueTot in H8.
  apply evalBoolExpTrueTot in H8. rewrite U in H8.
  inversion H8. rewrite U in H8. inversion H8.
  subst. exists nilProc. split. do 2 constructor.
  apply cond_bisim_false; assumption.
  inversion H; inversion H0; subst.
  exists (b $> p). split. constructor.
  apply stepTpIfFalse; assumption. apply cond_bisim_false.
  assumption. Qed.

Lemma if_then_bisim_true b p q :
  evalBoolExp b true -> b $> p $+$ !~b $> q ~p~ p.
  introz U. cut (!~b $> q ~p~ nilProc). intro NP.
  eapply bisim_trans. eapply choice_bisim_context.
  apply bisim_refl. apply NP. eapply bisim_trans.
  apply choice_bism_unit_r. apply cond_bisim_true.
  assumption. apply cond_bisim_false.
  unfold evalBoolExpFunTot. simpl.
  apply evalBoolExpRelFun in U. rewrite U.
  simpl. reflexivity. Qed.

Lemma if_then_bisim_false b p q :
  evalBoolExp b false -> b $> p $+$ !~b $> q ~p~ q.
  introz U. cut (b $> p ~p~ nilProc). intro NP.
  eapply bisim_trans. eapply choice_bisim_context.
  apply NP. apply bisim_refl. eapply bisim_trans.
  apply choice_bism_unit_l. apply cond_bisim_true.
  apply bevalNot in U. apply U.
  apply cond_bisim_false. apply evalBoolExpRelFun in U.
  unfold evalBoolExpFunTot. rewrite U. simpl.
  reflexivity. Qed.

