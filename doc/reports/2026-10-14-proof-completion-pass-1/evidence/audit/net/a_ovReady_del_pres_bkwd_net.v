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

(* ===== helpers copied verbatim from work/w1b-17/NetAuxBasics.ovReady_del_pres_bkwd_net.v ===== *)

From Stdlib Require Import Lra.

(* Counterexample machinery adapted from NetAuxBasics-2's verified
   bcWaitNet_del_bkwd counterexample. *)
Local Lemma ovReady_del_pres_bkwd_net_cx_eval t : evalExpFunTime (liftTimeExp t) = Some t.
Proof. destruct t as [[r rnn]]. reflexivity. Qed.

Local Lemma ovReady_del_pres_bkwd_net_cx_eval_ne (t : Time) : 0 < t ->
  evalExpFunTime (liftTimeExp t) <> Some zeroTime.
Proof.
  intros P E. rewrite ovReady_del_pres_bkwd_net_cx_eval in E. inversion E. subst.
  simpl in P. exact (Rlt_irrefl 0 P).
Qed.

Local Lemma ovReady_del_pres_bkwd_net_cx_del e Y a q :
  evalExpFunTime e <> Some zeroTime -> ~ del e Y -PA- a -PA> q.
Proof. intros E S. inversion S; subst. contradiction. Qed.

Local Lemma ovReady_del_pres_bkwd_net_cx_noact e Y a :
  evalExpFunTime e <> Some zeroTime ->
  ~ discActEnabled (nilProc $||$ (del e Y $||$ nilProc)) a.
Proof.
  intros E D. destruct D as [p' S].
  inversion S; subst;
  repeat match goal with
  | H : nilProc -PA- _ -PA> _ |- _ => inversion H
  | H : del e Y -PA- _ -PA> _ |- _ =>
      exfalso; exact (ovReady_del_pres_bkwd_net_cx_del _ _ _ _ E H)
  | H : del e Y $||$ nilProc -PA- _ -PA> _ |- _ => inversion H; subst; clear H
  end.
Qed.

(** A delay prefix whose guard evaluates to zero is bisimilar to its body.*)
Local Lemma ovReady_del_pres_bkwd_net_cx_del0 e Y : evalExpFunTime e = Some zeroTime ->
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

(** Anything bisimilar to ovReady m t l can output on chanOutProc now. *)
Local Lemma ovReady_del_pres_bkwd_net_cx_out m t l p :
  ovReadyState m t l p -> discActEnabled p (chanOutProc ;! [baseMode m, basePosition l]).
Proof. activation_tac. Qed.

(** COUNTEREXAMPLE to ovReady_del_pres_bkwd_net as stated (for any mode m). *)
Lemma ovReady_del_pres_bkwd_net_cx (m : Mode) : exists (n n' : Network) (d : Delay)
  (t : Time) (l : Position) (i : nat), n -ND- d -ND> n' /\
  ovReadyStateNet m t l i n' /\ ~ ovReadyStateNet m t l i n.
Proof.
  set (T1 := mkTime (mknonnegreal 1 Rle_0_1)).
  set (D1 := mkDelay (mkposreal 1 Rlt_0_1)).
  assert (HD : pos (delay D1) <= nonneg (time T1)) by (simpl; apply Rle_refl).
  set (X := ovReady m zeroTime origin).
  set (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  set (P := nilProc $||$ (del (liftTimeExp T1) X $||$ nilProc)).
  set (P' := nilProc $||$ (del (liftTimeExp (minusTime T1 D1 HD)) X $||$ nilProc)).
  exists [ [| P, origin, h0, sing m |] ] [ [| P', addPos origin origin, h0, sing m |] ].
  exists D1 zeroTime origin O.
  split; [ | split].
  - apply stepTnCons; [ | apply stepTnEmp].
    apply stepTeDel.
    + unfold P, P'. apply stepTpPar.
      * apply stepTpNil.
      * apply stepTpPar.
        -- apply stepTpDelSub. apply ovReady_del_pres_bkwd_net_cx_eval.
        -- apply stepTpNil.
        -- intros a _ S. inversion S.
      * intros a S. inversion S.
    + unfold h0. apply stepIntDel. apply stepIlDel.
      apply stepOlLift. apply stepTlDelEmp. apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement, dist2d, origin. simpl. rewrite distance_refl.
      apply Rmult_le_pos; [apply speedMax_nonneg | simpl; lra].
    + intro a. split.
      * intro D. exfalso. eapply ovReady_del_pres_bkwd_net_cx_noact; [ | exact D].
        apply ovReady_del_pres_bkwd_net_cx_eval_ne. simpl. apply Rlt_0_1.
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
             rewrite ovReady_del_pres_bkwd_net_cx_eval in H; inversion H; subst end.
           match goal with H : _ -PD- ?d0 -PD> _ |- _ =>
             destruct d0 as [[v vp]] end.
           simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = Some _ |- _ =>
             rewrite ovReady_del_pres_bkwd_net_cx_eval in H; inversion H; subst end.
           eapply ovReady_del_pres_bkwd_net_cx_noact; [ | exact D].
           apply ovReady_del_pres_bkwd_net_cx_eval_ne. simpl. simpl in Lt. lra.
        -- match goal with H : evalExpFunTime _ = None |- _ =>
             rewrite ovReady_del_pres_bkwd_net_cx_eval in H; discriminate H end.
  - apply lenWitness with (e := [|P', addPos origin origin, h0, sing m|]);
      [ | constructor].
    constructor. unfold P'. constructor. unfold ovReadyState.
    apply ovReady_del_pres_bkwd_net_cx_del0. rewrite ovReady_del_pres_bkwd_net_cx_eval.
    f_equal. apply timeEqR. simpl. ring.
  - intro B. destruct B as [e Be Ein]. inversion Ein; subst.
    inversion Be; subst. unfold P in *.
    match goal with H : ovReadyStateProt _ _ _ _ |- _ => inversion H; subst end.
    match goal with H : ovReadyState _ _ _ _ |- _ =>
      apply ovReady_del_pres_bkwd_net_cx_out in H; destruct H as [q S] end.
    eapply ovReady_del_pres_bkwd_net_cx_del; [ | exact S].
    apply ovReady_del_pres_bkwd_net_cx_eval_ne. simpl. apply Rlt_0_1.
Qed.

(** Hence the statement as given implies False for any mode. *)
Lemma ovReady_del_pres_bkwd_net_false :
  (forall n n' d m t l i, n -ND- d -ND> n' -> ovReadyStateNet m t l i n' ->
    ovReadyStateNet m t l i n) -> forall m : Mode, False.
Proof.
  intros H m. destruct (ovReady_del_pres_bkwd_net_cx m) as
    (n & n' & d & t & l & i & D & R & NR).
  exact (NR (H _ _ _ _ _ _ _ D R)).
Qed.
(* Print Assumptions ovReady_del_pres_bkwd_net_cx: only model axioms + proof_irrelevance, functional_extensionality_dep, ClassicalDedekindReals; no admitted lemma. *)
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.ovReady_del_pres_bkwd_net in exact T).
Lemma audit_ovReady_del_pres_bkwd_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (ovReady_del_pres_bkwd_net_false H m).
Qed.
Print Assumptions audit_ovReady_del_pres_bkwd_net.
