Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxResults.

(* ===== HELPERS copied verbatim from w1b-16/EntAuxResults.gotRange_currPincCheck_track_ent.v ===== *)

From Stdlib Require Import Lra.

(* Demonstration helpers for a counterexample (see the .fail.md). *)

(** A sum whose left summand is a false-guarded conditional is bisimilar to its
right summand: the dead branch never fires and idles under delays. *)
Lemma gotRange_currPincCheck_track_ent_ifFalse_sum c q :
  evalBoolExpFunTot c = false ->
  forall X, ProcEquiv.bisimulation (ifThen c q $+$ X) X.
Proof.
  intro F. cofix CIH. intro X. constructor.
  - intros a p' S. inversion S; subst.
    + match goal with [V : (ifThen c q $+$ X) -PA- _ -PA> _ |- _] => inversion V; subst end.
      * match goal with [V : ifThen c q -PA- _ -PA> _ |- _] => inversion V; subst end.
        congruence.
      * eexists. split; [apply stepPDisc; eassumption | apply ProcEquiv.bisim_refl].
    + match goal with [V : (ifThen c q $+$ X) -PD- _ -PD> _ |- _] => inversion V; subst end.
      match goal with [V : ifThen c q -PD- _ -PD> _ |- _] => inversion V; subst end.
      * congruence.
      * eexists. split; [apply stepPTimed; eassumption | apply CIH].
  - intros a q' S. inversion S; subst.
    + exists q'. split; [ | apply ProcEquiv.bisim_refl].
      apply stepPDisc. apply stepDpChoiceR. assumption.
    + exists (ifThen c q $+$ q'). split; [ | apply CIH].
      apply stepPTimed. apply stepTpSum; [apply stepTpIfFalse; assumption | assumption].
Qed.

(** A true-guarded conditional is bisimilar to its body. *)
Lemma gotRange_currPincCheck_track_ent_ifTrue c X :
  evalBoolExpFunTot c = true -> ProcEquiv.bisimulation (ifThen c X) X.
Proof.
  intro T. constructor.
  - intros a p' S. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S; subst.
    + apply stepPDisc.
      match goal with [V : ifThen c X -PA- _ -PA> _ |- _] => inversion V; subst end.
      assumption.
    + apply stepPTimed.
      match goal with [V : ifThen c X -PD- _ -PD> _ |- _] => inversion V; subst end.
      * assumption.
      * congruence.
  - intros a q' S. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S; subst.
    + apply stepPDisc. apply stepDpThen; assumption.
    + apply stepPTimed. apply stepTpIfTrue; assumption.
Qed.

Lemma gotRange_currPincCheck_track_ent_not_true B :
  evalBoolExpFunTot B = true -> evalBoolExpFunTot (!~ B) = false.
Proof.
  unfold evalBoolExpFunTot. simpl.
  destruct (evalBoolExpFun B) as [[ | ] | ]; simpl; congruence.
Qed.

(** The shape of currPincCheck/nextPincCheck: when the guard B holds, the whole
sum behaves exactly like the B-branch, whatever the other parameters are. *)
Lemma gotRange_currPincCheck_track_ent_guard_sum B q X :
  evalBoolExpFunTot B = true ->
  ProcEquiv.bisimulation ((!~ B $> q) $+$ (B $> X)) X.
Proof.
  intro T. eapply ProcEquiv.bisim_trans.
  - apply gotRange_currPincCheck_track_ent_ifFalse_sum.
    apply gotRange_currPincCheck_track_ent_not_true. exact T.
  - apply gotRange_currPincCheck_track_ent_ifTrue. exact T.
Qed.

(** An application process is bisimilar to its unfolded body. *)
Lemma gotRange_currPincCheck_track_ent_app_bisim n l2 :
  ProcEquiv.bisimulation (app n l2)
    (subProcTerm (listsToSub (fst (def n)) l2) (snd (def n))).
Proof.
  destruct (def n) as [l1 b] eqn:D. simpl. constructor.
  - intros a p' H. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion H; subst.
    + apply stepPDisc.
      match goal with [V : app n l2 -PA- _ -PA> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
    + apply stepPTimed.
      match goal with [V : app n l2 -PD- _ -PD> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
  - intros a q' H. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion H; subst.
    + apply stepPDisc. eapply stepDpApp; eassumption.
    + apply stepPTimed. eapply stepTpApp; eassumption.
Qed.

(** possIncDist is bounded below by a positive constant. *)
Lemma gotRange_currPincCheck_track_ent_pid m m' :
  2 * speedMax * adaptNotif <= possIncDist m m'.
Proof.
  unfold possIncDist.
  assert (A : 0 <= minDistComp m m') by apply cond_nonneg.
  assert (B : adaptNotif <= Rmax adaptNotif transMax) by apply Rmax_l.
  assert (C : 0 <= trans m') by apply cond_nonneg.
  assert (D : 0 < period m') by apply period_positive.
  assert (S : 0 < speedMax) by apply speedMax_pos.
  assert (E : 0 <= speedMax * (Rmax adaptNotif transMax - adaptNotif + period m' + trans m'))
    by (apply Rmult_le_pos; lra).
  nra.
Qed.

(** Counterexample: the target statement is refuted by any Mode. *)
Lemma gotRange_currPincCheck_track_ent_cex (m : Mode) :
  ~ (forall (m2 m1' m2' : Mode) (l l' : Position)
       (r r' : Distance) (p p' : ProcTerm) h h' k k' a,
     gotRangeStateEnt m2 r ([|p, l, h, k|]) ->
     currPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
     [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
     m2 = m2' /\ r = r' /\ m1' = currModeMState k).
Proof.
  intro H.
  assert (SA : 0 < speedMax * adaptNotif).
  { apply Rmult_lt_0_compat; [apply speedMax_pos | apply adaptNotif_positive]. }
  pose (r0 := mkDistance zeroNonneg).
  pose (r1 := mkDistance (mknonnegreal (speedMax * adaptNotif) (Rlt_le _ _ SA))).
  pose (l := mkPosition 0 0).
  pose (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  assert (P0 : possIncBool m m r0 = true).
  { unfold possIncBool. destruct (possIncDec m m r0) as [Y | N]; [reflexivity | ].
    exfalso. apply N. unfold possiblyIncompatible. simpl.
    pose proof (gotRange_currPincCheck_track_ent_pid m m). lra. }
  assert (P1 : possIncBool m m r1 = true).
  { unfold possIncBool. destruct (possIncDec m m r1) as [Y | N]; [reflexivity | ].
    exfalso. apply N. unfold possiblyIncompatible. simpl.
    pose proof (gotRange_currPincCheck_track_ent_pid m m). lra. }
  assert (B1 : ProcEquiv.bisimulation (currPincCheck m m r1) badOvlpN).
  { unfold currPincCheck. apply gotRange_currPincCheck_track_ent_guard_sum.
    unfold evalBoolExpFunTot. simpl. exact P1. }
  assert (ST : exists q, gotRange m r0 -PA- chanMCurr ;? [baseMode m] -PA> q /\
                 ProcEquiv.bisimulation q (currPincCheck m m r1)).
  { eexists. split.
    - unfold gotRange. apply stepDpIn. reflexivity.
    - eapply ProcEquiv.bisim_trans; [ | apply ProcEquiv.bisim_symm; exact B1].
      clean_proc.
      eapply ProcEquiv.bisim_trans; [apply gotRange_currPincCheck_track_ent_app_bisim | ].
      clean_proc.
      apply gotRange_currPincCheck_track_ent_guard_sum.
      unfold evalBoolExpFunTot. simpl. exact P0. }
  destruct ST as [q3 [ST BQ]].
  assert (E : r0 = r1).
  { edestruct (H m m m l l r0 r1 (nilProc $||$ nilProc $||$ gotRange m r0)
       (nilProc $||$ nilProc $||$ q3) h h (sing m) (sing m) aeTau) as [_ [E _]].
    - do 2 constructor. apply ProcEquiv.bisim_refl.
    - do 2 constructor. exact BQ.
    - eapply stepDeCurrRead; [ | apply stepMsOutCurrSing].
      apply stepDpParR. apply stepDpParR. exact ST.
    - exact E. }
  apply (f_equal (fun d : Distance => nonneg (distance d))) in E.
  unfold r0, r1, zeroNonneg in E. simpl in E. lra.
Qed.

(* ===== end of copied helpers ===== *)

Lemma audit_grcp_Mode_False : Mode -> False.
Proof. intro m. exact (gotRange_currPincCheck_track_ent_cex m gotRange_currPincCheck_track_ent). Qed.

Print Assumptions gotRange_currPincCheck_track_ent_cex.
Print Assumptions audit_grcp_Mode_False.
