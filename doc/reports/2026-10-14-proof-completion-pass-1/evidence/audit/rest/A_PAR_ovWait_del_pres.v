Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProcEquiv.
Require Import ComhCoq.ProtAuxResults.

(* ===== audit evidence ===== *)

From Stdlib Require Import Lra.
(** Counterexample: ovWait m t x x delays (by d = x) to a process whose
  pause-timer has expired, so it is no longer bisimilar to ovWait m t x x. *)
Lemma ovWait_del_pres_cex m t d :
  exists p p', ovWaitState m t (delToTime d) (delToTime d) p /\
  p -PD- d -PD> p' /\ ~ ovWaitState m t (delToTime d) (delToTime d) p'.
Proof.
  destruct d as [[r rpos]].
  assert (Hle : pos (delay (mkDelay (mkposreal r rpos))) <=
    nonneg (time (delToTime (mkDelay (mkposreal r rpos))))).
  { simpl. apply Rle_refl. }
  eexists. eexists. split; [apply bisim_refl | split].
  { unfold ovWait. apply stepTpSum;
      [apply stepTpSum; [apply stepTpSum; apply stepTpIn | ] | ];
      apply (stepTpDelSub _ _ _ _ Hle); reflexivity. }
  intro B. red in B. destruct B as [B1 B2].
  edestruct B1 as [q [S1 _]].
  { apply stepPDisc. apply stepDpChoiceR. apply stepDpTimeOut;
      [apply stepDpOut; constructor | ].
    unfold evalExpFunTime. simpl. f_equal. apply timeEqR. simpl. ring. }
  inversion S1; subst.
  match goal with [H : ovWait _ _ _ _ -PA- _ -PA> _ |- _] => unfold ovWait in H end.
  repeat match goal with
   | [H : sum _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : outPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : inPrefix _ _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
   | [H : del _ _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
  end.
  match goal with [E : evalExpFunTime _ = Some zeroTime |- _] =>
    apply (f_equal (fun o => match o with Some t0 => nonneg (time t0) | None => 0%R end)) in E;
    simpl in E end.
  lra.
Qed.

(** Hence the statement of ovWait_del_pres is refuted for every m, t, d. *)
Lemma ovWait_del_pres_refuted m t d :
  ~ (forall x y p p', ovWaitState m t x y p -> p -PD- d -PD> p' ->
     ovWaitState m t x y p').
Proof.
  intro F. destruct (ovWait_del_pres_cex m t d) as [p [p' [U [V W]]]].
  apply W. eapply F; eassumption.
Qed.

(** Corrected statement (proved): after a delay the process is still an
  ovWait with the same mode/time parameters but (possibly) different timers. *)
Lemma ovWait_del_pres_zero_bisim q :
  $<eBase (baseTime zeroTime)>$ q ~p~ q.
Proof.
  constructor.
  - intros a q' S. exists q'. split; [ | apply bisim_refl].
    inversion S as [a0 q0 H | d0 q0 H]; subst.
    + inversion H; subst. apply stepPDisc; assumption.
    + inversion H; subst.
      * match goal with [E : evalExpFunTime _ = Some ?t0 |- _] =>
          rewrite evalExpFunTime_time in E; inversion E; subst end.
        match goal with [ |- _ -P- actTime (?t0 +dt+ ?d1) -P> _] =>
          replace (t0 +dt+ d1) with d1 by (apply delayEqR; simpl; ring) end.
        apply stepPTimed; assumption.
      * match goal with [E : evalExpFunTime _ = Some ?t0 |- _] =>
          rewrite evalExpFunTime_time in E; inversion E; subst end.
        exfalso. match goal with [L : pos (delay ?d1) <= _ |- _] =>
          simpl in L; pose proof (cond_pos d1); lra end.
      * match goal with [E : evalExpFunTime _ = None |- _] =>
          rewrite evalExpFunTime_time in E; inversion E end.
  - intros a q' S. exists q'. split; [ | apply bisim_refl].
    inversion S as [a0 q0 H | d0 q0 H]; subst.
    + apply stepPDisc. apply stepDpTimeOut; [assumption | apply evalExpFunTime_time].
    + apply stepPTimed.
      replace d0 with (zeroTime +dt+ d0) by (apply delayEqR; simpl; ring).
      apply stepTpDelAdd; [assumption | apply evalExpFunTime_time].
Qed.

Lemma ovWait_del_pres_timer_aux (e : Time) (P q : ProcTerm) (d : Delay) :
  $<eBase (baseTime e)>$ P -PD- d -PD> q ->
  (forall d' q', P -PD- d' -PD> q' -> q' = P) ->
  exists e', q ~p~ $<eBase (baseTime e')>$ P.
Proof.
  intros S F. inversion S; subst.
  - exists zeroTime. apply bisim_symm.
    match goal with [H : P -PD- _ -PD> q |- _] => apply F in H; subst end.
    apply ovWait_del_pres_zero_bisim.
  - match goal with [E : evalExpFunTime _ = Some ?t0 |- _] =>
      rewrite evalExpFunTime_time in E; inversion E; subst end.
    eexists. apply bisim_refl.
  - match goal with [E : evalExpFunTime _ = None |- _] =>
      rewrite evalExpFunTime_time in E; inversion E end.
Qed.

Lemma ovWait_del_pres_fixed m t x y p p' d :
  ovWaitState m t x y p -> p -PD- d -PD> p' ->
  exists x' y', ovWaitState m t x' y' p'.
Proof.
  intros U V. red in U. destruct U as [U1 U2].
  apply stepPTimed in V. apply U1 in V. destruct V as [q [W B]].
  clear U1 U2. inversion W; subst.
  match goal with [H : ovWait _ _ _ _ -PD- _ -PD> q |- _] => unfold ovWait in H end.
  repeat match goal with
    | [H : sum _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : inPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    end.
  match goal with [H : $<eBase (baseTime y)>$ _ -PD- _ -PD> _ |- _] =>
    apply ovWait_del_pres_timer_aux in H;
    [destruct H as [y' Hy] | intros ? ? Z; inversion Z; reflexivity] end.
  match goal with [H : $<eBase (baseTime x)>$ _ -PD- _ -PD> _ |- _] =>
    apply ovWait_del_pres_timer_aux in H;
    [destruct H as [x' Hx] | intros ? ? Z; inversion Z; reflexivity] end.
  exists x'. exists y'. red. eapply bisim_trans; [exact B | ]. unfold ovWait.
  repeat apply choice_bisim_context; first [apply bisim_refl | assumption].
Qed.

(** Quantitative version for delays within both timers (proved). *)
Lemma ovWait_del_pres_timer_aux2 (e : Time) (P q : ProcTerm) (d : Delay) (He : d <= e) :
  $<eBase (baseTime e)>$ P -PD- d -PD> q ->
  q = $<eBase (baseTime (minusTime e d He))>$ P.
Proof.
  intros S. inversion S; subst.
  - match goal with [E : evalExpFunTime _ = Some ?t0 |- _] =>
      rewrite evalExpFunTime_time in E; inversion E; subst end.
    exfalso. simpl in He.
    match goal with [ |- _] => idtac end.
    match type of He with context [pos (delay ?d1)] => pose proof (cond_pos d1) end.
    lra.
  - match goal with [E : evalExpFunTime _ = Some ?t0 |- _] =>
      rewrite evalExpFunTime_time in E; inversion E; subst end.
    do 3 f_equal. apply timeEqR. reflexivity.
  - match goal with [E : evalExpFunTime _ = None |- _] =>
      rewrite evalExpFunTime_time in E; inversion E end.
Qed.

Lemma ovWait_del_pres_strong (m : Mode) (t x y : Time) (p p' : ProcTerm) (d : Delay) (Hx : d <= x) (Hy : d <= y) :
  ovWaitState m t x y p -> p -PD- d -PD> p' ->
  ovWaitState m t (minusTime x d Hx) (minusTime y d Hy) p'.
Proof.
  intros U V. red in U. destruct U as [U1 U2].
  apply stepPTimed in V. apply U1 in V. destruct V as [q [W B]].
  clear U1 U2. inversion W; subst.
  match goal with [H : ovWait _ _ _ _ -PD- _ -PD> q |- _] => unfold ovWait in H end.
  repeat match goal with
    | [H : sum _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    | [H : inPrefix _ _ _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
    end.
  match goal with [H : $<eBase (baseTime y)>$ _ -PD- _ -PD> _ |- _] =>
    apply (ovWait_del_pres_timer_aux2 _ _ _ _ Hy) in H; subst end.
  match goal with [H : $<eBase (baseTime x)>$ _ -PD- _ -PD> _ |- _] =>
    apply (ovWait_del_pres_timer_aux2 _ _ _ _ Hx) in H; subst end.
  exact B.
Qed.

(** The corrected statement suffices for the only user, del_pres_nextSinceState. *)
Lemma ovWait_del_pres_user_ok m t x y p p' d :
  ovWaitState m t x y p -> p -PD- d -PD> p' -> nextSinceState p'.
Proof.
  intros U V. destruct (ovWait_del_pres_fixed _ _ _ _ _ _ _ U V) as [x' [y' W]].
  eapply nexsOvwSt; eassumption.
Qed.


Print Assumptions ovWait_del_pres_refuted.

Print Assumptions ovWait_del_pres_fixed.

Print Assumptions ovWait_del_pres_strong.
