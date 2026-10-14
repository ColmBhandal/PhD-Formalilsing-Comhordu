From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
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

(* ===== helpers copied verbatim from work/NetAuxBasics-2/NetAuxBasics.bcWaitNet_del_bkwd.counterexample.v ===== *)

From Stdlib Require Import Lra.

Local Lemma bcWaitNet_del_bkwd_cx_eval t : evalExpFunTime (liftTimeExp t) = Some t.
Proof. destruct t as [[r rnn]]. reflexivity. Qed.

Local Lemma bcWaitNet_del_bkwd_cx_eval_ne (t : Time) : 0 < t ->
  evalExpFunTime (liftTimeExp t) <> Some zeroTime.
Proof.
  intros P E. rewrite bcWaitNet_del_bkwd_cx_eval in E. inversion E. subst.
  simpl in P. exact (Rlt_irrefl 0 P).
Qed.

Local Lemma bcWaitNet_del_bkwd_cx_nil a q : ~ (nilProc $||$ nilProc) -PA- a -PA> q.
Proof.
  intro S. inversion S; subst;
  match goal with H : nilProc -PA- _ -PA> _ |- _ => inversion H end.
Qed.

Local Lemma bcWaitNet_del_bkwd_cx_del e Y a q :
  evalExpFunTime e <> Some zeroTime -> ~ del e Y -PA- a -PA> q.
Proof. intros E S. inversion S; subst. contradiction. Qed.

Local Lemma bcWaitNet_del_bkwd_cx_noact e Y a :
  evalExpFunTime e <> Some zeroTime ->
  ~ discActEnabled (del e Y $||$ (nilProc $||$ nilProc)) a.
Proof.
  intros E D. destruct D as [p' S]. inversion S; subst;
  first [ eapply bcWaitNet_del_bkwd_cx_del; eassumption
        | eapply bcWaitNet_del_bkwd_cx_nil; eassumption ].
Qed.

(** A delay prefix whose guard evaluates to zero is bisimilar to its body.*)
Local Lemma bcWaitNet_del_bkwd_cx_del0 e Y : evalExpFunTime e = Some zeroTime ->
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

(** COUNTEREXAMPLE to bcWaitNet_del_bkwd as stated (for any mode m).*)
Lemma bcWaitNet_del_bkwd_cx (m : Mode) : exists (n n' : Network) (x : Time)
  (i : nat) (d : Delay), n -ND- d -ND> n' /\ bcWaitStateNet m x i n' /\
  ~ bcWaitStateNet m (x +dt+ d) i n.
Proof.
  set (T1 := mkTime (mknonnegreal 1 Rle_0_1)).
  set (D1 := mkDelay (mkposreal 1 Rlt_0_1)).
  assert (HD : pos (delay D1) <= nonneg (time T1)) by (simpl; apply Rle_refl).
  set (X := bcWait m zeroTime).
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (P := del (liftTimeExp T1) X $||$ (nilProc $||$ nilProc)).
  set (P' := del (liftTimeExp (minusTime T1 D1 HD)) X $||$ (nilProc $||$ nilProc)).
  exists [ [| P, origin, h0, sing m |] ] [ [| P', addPos origin origin, h0, sing m |] ].
  exists zeroTime O D1.
  split; [ | split].
  - apply stepTnCons; [ | apply stepTnEmp].
    apply stepTeDel.
    + unfold P, P'. apply stepTpPar.
      * apply stepTpDelSub. apply bcWaitNet_del_bkwd_cx_eval.
      * apply stepTpPar; [apply stepTpNil | apply stepTpNil | ].
        intros a S. inversion S.
      * intros a _ S. inversion S; subst;
        match goal with H : sort _ _ nilProc |- _ => inversion H end.
    + unfold h0. apply stepIntDel. apply stepIlDel.
      apply stepOlLift. apply stepTlDelEmp. apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement, dist2d, origin. simpl. rewrite distance_refl.
      apply Rmult_le_pos; [apply speedMax_nonneg | simpl; lra].
    + intro a. split.
      * intro D. exfalso. eapply bcWaitNet_del_bkwd_cx_noact; [ | exact D].
        apply bcWaitNet_del_bkwd_cx_eval_ne. simpl. apply Rlt_0_1.
      * intros p' i' k' d' Lt TP TI TK D. exfalso. unfold P in TP.
        inversion TP; subst. clear TP.
        match goal with H : nilProc $||$ nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        repeat match goal with H : nilProc -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        match goal with H : del _ X -PD- _ -PD> _ |- _ =>
          inversion H; subst; clear H end.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite bcWaitNet_del_bkwd_cx_eval in H; inversion H; subst end.
           match goal with H : _ -PD- ?d0 -PD> _ |- _ =>
             destruct d0 as [[v vp]] end.
           simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite bcWaitNet_del_bkwd_cx_eval in H; inversion H; subst end.
           eapply bcWaitNet_del_bkwd_cx_noact; [ | exact D].
           apply bcWaitNet_del_bkwd_cx_eval_ne. simpl. simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = None |- _ =>
             rewrite bcWaitNet_del_bkwd_cx_eval in H; discriminate H end.
  - apply lenWitness with (e := [|P', addPos origin origin, h0, sing m|]);
      [ | constructor].
    constructor. unfold P'. constructor. unfold bcWaitState.
    apply bcWaitNet_del_bkwd_cx_del0. rewrite bcWaitNet_del_bkwd_cx_eval.
    f_equal. apply timeEqR. simpl. ring.
  - intro B. destruct B as [e Be Ein]. inversion Ein; subst.
    inversion Be; subst. unfold P in *.
    match goal with H : bcWaitStateProt _ _ _ |- _ => inversion H; subst end.
    match goal with H : bcWaitState _ _ _ |- _ => apply bcWait_trans_in in H;
      destruct H as [q S] end.
    eapply bcWaitNet_del_bkwd_cx_del; [ | exact S].
    apply bcWaitNet_del_bkwd_cx_eval_ne. simpl. apply Rlt_0_1.
Qed.
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.bcWaitNet_del_bkwd in exact T).
Lemma audit_bcWaitNet_del_bkwd : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  destruct (bcWaitNet_del_bkwd_cx m) as (n & n' & x & i & d & D & B & NB).
  exact (NB (H n n' m x i d D B)).
Qed.
Print Assumptions audit_bcWaitNet_del_bkwd.
