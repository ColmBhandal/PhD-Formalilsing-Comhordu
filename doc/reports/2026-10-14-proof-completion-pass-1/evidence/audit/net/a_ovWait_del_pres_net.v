From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.NetAuxBasics.

(* ===== helpers copied verbatim from work/w1b-07/NetAuxBasics.ovWait_del_pres_bkwd_net_strong.v ===== *)

From Stdlib Require Import Lra.

Local Lemma ovWait_del_pres_bkwd_net_strong_cx_eval t :
  evalExpFunTime (liftTimeExp t) = Some t.
Proof. destruct t as [[r rnn]]. reflexivity. Qed.

Local Lemma ovWait_del_pres_bkwd_net_strong_cx_eval_ne (t : Time) : 0 < t ->
  evalExpFunTime (liftTimeExp t) <> Some zeroTime.
Proof.
  intros P E. rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in E. inversion E. subst.
  simpl in P. exact (Rlt_irrefl 0 P).
Qed.

Local Lemma ovWait_del_pres_bkwd_net_strong_cx_del e Y a q :
  evalExpFunTime e <> Some zeroTime -> ~ del e Y -PA- a -PA> q.
Proof. intros E S. inversion S; subst. contradiction. Qed.

(** The overlap component sits in the middle of the triple. *)
Local Lemma ovWait_del_pres_bkwd_net_strong_cx_noact e Y a :
  evalExpFunTime e <> Some zeroTime ->
  ~ discActEnabled (nilProc $||$ (del e Y $||$ nilProc)) a.
Proof.
  intros E D. destruct D as [p' S].
  inversion S; subst;
  repeat match goal with
   | H : nilProc -PA- _ -PA> _ |- _ => inversion H
   | H : del _ _ -PA- _ -PA> _ |- _ =>
       eapply ovWait_del_pres_bkwd_net_strong_cx_del; [exact E | exact H]
   | H : parComp _ _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H
  end.
Qed.

(** A delay prefix whose guard evaluates to zero is bisimilar to its body.*)
Local Lemma ovWait_del_pres_bkwd_net_strong_cx_del0 e Y :
  evalExpFunTime e = Some zeroTime ->
  ComhCoq.ProcEquiv.bisimulation (del e Y) Y.
Proof.
  intro E. constructor.
  - intros a p' S. exists p'. split; [ | apply ComhCoq.ProcEquiv.bisim_refl].
    inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + inversion S0; subst. apply stepPDisc. assumption.
    + inversion S0; subst.
      * match goal with H : evalExpFunTime e = Some _ |- _ =>
          rewrite E in H; inversion H; subst end.
        match goal with |- _ -P- actTime (zeroTime +dt+ ?d1) -P> _ =>
          replace (zeroTime +dt+ d1) with d1 by (apply delayEqR; simpl; ring) end.
        apply stepPTimed. assumption.
      * match goal with H : evalExpFunTime e = Some _ |- _ =>
          rewrite E in H; inversion H; subst end.
        exfalso. destruct d0 as [[v vp]]. simpl in *. lra.
      * match goal with H : evalExpFunTime e = None |- _ =>
          rewrite E in H; discriminate H end.
  - intros a q' S. exists q'. split; [ | apply ComhCoq.ProcEquiv.bisim_refl].
    inversion S as [a0 t0 S0 | d0 t0 S0]; subst.
    + apply stepPDisc. apply stepDpTimeOut; assumption.
    + apply stepPTimed.
      replace d0 with (zeroTime +dt+ d0) by (apply delayEqR; simpl; ring).
      eapply stepTpDelAdd; eassumption.
Qed.

Local Lemma ovWait_del_pres_bkwd_net_strong_cx_abort m t x y p :
  ovWaitState m t x y p -> discActEnabled p (chanAbort *?).
Proof. activation_tac. Qed.

(** COUNTEREXAMPLE to ovWait_del_pres_bkwd_net_strong as stated (any mode m). *)
Lemma ovWait_del_pres_bkwd_net_strong_cx (m : Mode) :
  exists (n n' : Network) (d : Delay) (t x y : Time) (i : nat),
  n -ND- d -ND> n' /\ ovWaitStateNet m t x y i n' /\
  ~ ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n.
Proof.
  set (T1 := mkTime (mknonnegreal 1 Rle_0_1)).
  set (D1 := mkDelay (mkposreal 1 Rlt_0_1)).
  assert (HD : pos (delay D1) <= nonneg (time T1)) by (simpl; apply Rle_refl).
  set (X := ovWait m zeroTime zeroTime zeroTime).
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (P := nilProc $||$ (del (liftTimeExp T1) X $||$ nilProc)).
  set (P' := nilProc $||$ (del (liftTimeExp (minusTime T1 D1 HD)) X $||$ nilProc)).
  exists [ [| P, origin, h0, sing m |] ] [ [| P', addPos origin origin, h0, sing m |] ].
  exists D1 zeroTime zeroTime zeroTime O.
  split; [ | split].
  - apply stepTnCons; [ | apply stepTnEmp].
    apply stepTeDel.
    + unfold P, P'. apply stepTpPar.
      * apply stepTpNil.
      * apply stepTpPar.
        -- apply stepTpDelSub. apply ovWait_del_pres_bkwd_net_strong_cx_eval.
        -- apply stepTpNil.
        -- intros a _ S. inversion S.
      * intros a S. inversion S.
    + unfold h0. apply stepIntDel. apply stepIlDel.
      apply stepOlLift. apply stepTlDelEmp. apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement, dist2d, origin. simpl. rewrite distance_refl.
      apply Rmult_le_pos; [apply speedMax_nonneg | simpl; lra].
    + intro a. split.
      * intro D. exfalso. eapply ovWait_del_pres_bkwd_net_strong_cx_noact; [ | exact D].
        apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. apply Rlt_0_1.
      * intros p' i' k' d' Lt TP TI TK D. exfalso. unfold P in TP.
        inversion TP; subst. clear TP.
        repeat match goal with H : nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        match goal with H : del _ X $||$ nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        repeat match goal with H : nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        match goal with H : del _ X -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; inversion H; subst end.
           match goal with H : _ -PD- ?d0 -PD> _ |- _ =>
             destruct d0 as [[v vp]] end.
           simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; inversion H; subst end.
           eapply ovWait_del_pres_bkwd_net_strong_cx_noact; [ | exact D].
           apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = None |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; discriminate H end.
  - apply lenWitness with (e := [|P', addPos origin origin, h0, sing m|]);
      [ | constructor].
    constructor. unfold P'. constructor. unfold ovWaitState.
    apply ovWait_del_pres_bkwd_net_strong_cx_del0.
    rewrite ovWait_del_pres_bkwd_net_strong_cx_eval.
    f_equal. apply timeEqR. simpl. ring.
  - intro B. destruct B as [e Be Ein]. inversion Ein; subst.
    inversion Be; subst. unfold P in *.
    match goal with H : ovWaitStateProt _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : ovWaitState _ _ _ _ _ |- _ =>
      apply ovWait_del_pres_bkwd_net_strong_cx_abort in H;
      destruct H as [q S] end.
    eapply ovWait_del_pres_bkwd_net_strong_cx_del; [ | exact S].
    apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. apply Rlt_0_1.
Qed.

Lemma ovWait_del_pres_bkwd_net_strong_refuted :
  forall m : Mode, ~ (forall n n' d t x y i,
    n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
    ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n).
Proof.
  intros m F. destruct (ovWait_del_pres_bkwd_net_strong_cx m)
    as [n [n' [d [t [x [y [i [S [W NW]]]]]]]]].
  apply NW. eapply F; eassumption.
Qed.
(* ===== audit wrapper ===== *)
(* Auditor-constructed: w1b-07 counterexample network, same parameters on both sides. *)
(** COUNTEREXAMPLE to ovWait_del_pres_bkwd_net_strong as stated (any mode m). *)
Lemma audit_ovWait_del_pres_net_cx (m : Mode) :
  exists (n n' : Network) (d : Delay) (t x y : Time) (i : nat),
  n -ND- d -ND> n' /\ ovWaitStateNet m t x y i n' /\
  ~ ovWaitStateNet m t x y i n.
Proof.
  set (T1 := mkTime (mknonnegreal 1 Rle_0_1)).
  set (D1 := mkDelay (mkposreal 1 Rlt_0_1)).
  assert (HD : pos (delay D1) <= nonneg (time T1)) by (simpl; apply Rle_refl).
  set (X := ovWait m zeroTime zeroTime zeroTime).
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (P := nilProc $||$ (del (liftTimeExp T1) X $||$ nilProc)).
  set (P' := nilProc $||$ (del (liftTimeExp (minusTime T1 D1 HD)) X $||$ nilProc)).
  exists [ [| P, origin, h0, sing m |] ] [ [| P', addPos origin origin, h0, sing m |] ].
  exists D1 zeroTime zeroTime zeroTime O.
  split; [ | split].
  - apply stepTnCons; [ | apply stepTnEmp].
    apply stepTeDel.
    + unfold P, P'. apply stepTpPar.
      * apply stepTpNil.
      * apply stepTpPar.
        -- apply stepTpDelSub. apply ovWait_del_pres_bkwd_net_strong_cx_eval.
        -- apply stepTpNil.
        -- intros a _ S. inversion S.
      * intros a S. inversion S.
    + unfold h0. apply stepIntDel. apply stepIlDel.
      apply stepOlLift. apply stepTlDelEmp. apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement, dist2d, origin. simpl. rewrite distance_refl.
      apply Rmult_le_pos; [apply speedMax_nonneg | simpl; lra].
    + intro a. split.
      * intro D. exfalso. eapply ovWait_del_pres_bkwd_net_strong_cx_noact; [ | exact D].
        apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. apply Rlt_0_1.
      * intros p' i' k' d' Lt TP TI TK D. exfalso. unfold P in TP.
        inversion TP; subst. clear TP.
        repeat match goal with H : nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        match goal with H : del _ X $||$ nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        repeat match goal with H : nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        match goal with H : del _ X -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; inversion H; subst end.
           match goal with H : _ -PD- ?d0 -PD> _ |- _ =>
             destruct d0 as [[v vp]] end.
           simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; inversion H; subst end.
           eapply ovWait_del_pres_bkwd_net_strong_cx_noact; [ | exact D].
           apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = None |- _ =>
             rewrite ovWait_del_pres_bkwd_net_strong_cx_eval in H; discriminate H end.
  - apply lenWitness with (e := [|P', addPos origin origin, h0, sing m|]);
      [ | constructor].
    constructor. unfold P'. constructor. unfold ovWaitState.
    apply ovWait_del_pres_bkwd_net_strong_cx_del0.
    rewrite ovWait_del_pres_bkwd_net_strong_cx_eval.
    f_equal. apply timeEqR. simpl. ring.
  - intro B. destruct B as [e Be Ein]. inversion Ein; subst.
    inversion Be; subst. unfold P in *.
    match goal with H : ovWaitStateProt _ _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : ovWaitState _ _ _ _ _ |- _ =>
      apply ovWait_del_pres_bkwd_net_strong_cx_abort in H;
      destruct H as [q S] end.
    eapply ovWait_del_pres_bkwd_net_strong_cx_del; [ | exact S].
    apply ovWait_del_pres_bkwd_net_strong_cx_eval_ne. simpl. apply Rlt_0_1.
Qed.


Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.ovWait_del_pres_net in exact T).
Lemma audit_ovWait_del_pres_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  destruct (audit_ovWait_del_pres_net_cx m) as (n & n' & d & t & x & y & i & S & OW & NOW).
  exact (NOW (proj2 (H m t x y i n n' d S) OW)).
Qed.
Print Assumptions audit_ovWait_del_pres_net.
