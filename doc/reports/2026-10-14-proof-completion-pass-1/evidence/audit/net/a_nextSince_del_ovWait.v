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

(* ===== helpers copied verbatim from work/NetAuxBasics-3/NetAuxBasics.nextSince_del_ovWait.v ===== *)

From Stdlib Require Import Lra.

(* ---- Counterexample development for nextSince_del_ovWait ---- *)

Definition nextSince_del_ovWait_okChanb (c : Channel) : bool :=
  match c with
  | chanAbort | chanBad | chanPos | chanPause => true
  | _ => false
  end.

Definition nextSince_del_ovWait_okAct (a : DiscAct) : Prop :=
  match a with
  | inAct c _ => nextSince_del_ovWait_okChanb c = true
  | outAct c _ => nextSince_del_ovWait_okChanb c = true
  | tauAct => True
  end.

Inductive nextSince_del_ovWait_okProc : ProcTerm -> Prop :=
  | nextSince_del_ovWait_ok_nil : nextSince_del_ovWait_okProc nilProc
  | nextSince_del_ovWait_ok_in c l r : nextSince_del_ovWait_okChanb c = true ->
    nextSince_del_ovWait_okProc (inPrefix c l r)
  | nextSince_del_ovWait_ok_out c l r : nextSince_del_ovWait_okChanb c = true ->
    nextSince_del_ovWait_okProc (outPrefix c l r)
  | nextSince_del_ovWait_ok_sum p q : nextSince_del_ovWait_okProc p ->
    nextSince_del_ovWait_okProc q -> nextSince_del_ovWait_okProc (sum p q)
  | nextSince_del_ovWait_ok_par p q : nextSince_del_ovWait_okProc p ->
    nextSince_del_ovWait_okProc q -> nextSince_del_ovWait_okProc (parComp p q)
  | nextSince_del_ovWait_ok_del e p : nextSince_del_ovWait_okProc p ->
    nextSince_del_ovWait_okProc (del e p).

Lemma nextSince_del_ovWait_ok_disc p a p' :
  nextSince_del_ovWait_okProc p -> p -PA- a -PA> p' -> nextSince_del_ovWait_okAct a.
Proof.
  intros Hok S; revert Hok; induction S; intro Hok; inversion Hok; subst; simpl; auto.
Qed.

Lemma nextSince_del_ovWait_ok_delay p d p' :
  nextSince_del_ovWait_okProc p -> p -PD- d -PD> p' -> nextSince_del_ovWait_okProc p'.
Proof.
  intros Hok S; revert Hok; induction S; intro Hok; inversion Hok; subst;
  first [assumption | solve [constructor; auto] | solve [auto]].
Qed.

Lemma nextSince_del_ovWait_inter_not a h :
  discActEnabledInter (a^) h -> nextSince_del_ovWait_okAct a -> False.
Proof.
  intros D O. destruct a as [c v | c v | ]; simpl in D, O; inversion D; subst;
  match goal with S : stepInter _ _ _ |- _ => inversion S end; subst;
  simpl in O; discriminate.
Qed.

Lemma nextSince_del_ovWait_mstate_not a k :
  discActEnabledMState (a^) k -> nextSince_del_ovWait_okAct a -> False.
Proof.
  intros D O. destruct a as [c v | c v | ]; simpl in D, O; inversion D; subst;
  match goal with S : stepModeState _ _ _ |- _ => inversion S end; subst;
  simpl in O; discriminate.
Qed.

Lemma nextSince_del_ovWait_ok_noSync p h k d :
  nextSince_del_ovWait_okProc p -> noSync p h k d.
Proof.
  intros H a. split.
  - intros [p' S]. pose proof (nextSince_del_ovWait_ok_disc _ _ _ H S) as O.
    split; intro D'.
    + exact (nextSince_del_ovWait_inter_not _ _ D' O).
    + exact (nextSince_del_ovWait_mstate_not _ _ D' O).
  - intros p' h' k' d' _ PD _ _ [p'' S].
    pose proof (nextSince_del_ovWait_ok_delay _ _ _ H PD) as H'.
    pose proof (nextSince_del_ovWait_ok_disc _ _ _ H' S) as O.
    split; intro D'.
    + exact (nextSince_del_ovWait_inter_not _ _ D' O).
    + exact (nextSince_del_ovWait_mstate_not _ _ D' O).
Qed.

(** The overlap component in ovWait with both timers already expired. *)
Definition nextSince_del_ovWait_P0 (m : Mode) : ProcTerm :=
  ovWait m zeroTime zeroTime zeroTime.

Definition nextSince_del_ovWait_h0 : Interface :=
  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []).

(** The one-entity network used in the counterexample. *)
Definition nextSince_del_ovWait_net (m : Mode) : Network :=
  [ [| nilProc $||$ nextSince_del_ovWait_P0 m $||$ nilProc, origin,
       nextSince_del_ovWait_h0, sing m |] ].

(** It can delay by any amount (here 0 +dt+ d1, i.e. by d1). *)
Lemma nextSince_del_ovWait_net_del (m : Mode) (d1 : Delay) :
  exists n', nextSince_del_ovWait_net m -ND- (zeroTime +dt+ d1) -ND> n'.
Proof.
  eexists. unfold nextSince_del_ovWait_net. apply stepTnCons; [ | apply stepTnEmp].
  eapply stepTeDel with (delta := origin).
  - apply stepTpPar.
    + apply stepTpNil.
    + apply stepTpPar.
      * unfold nextSince_del_ovWait_P0, ovWait.
        repeat (first [apply stepTpSum | apply stepTpIn | apply stepTpOut |
          (apply stepTpDelAdd; [ | reflexivity])]).
      * apply stepTpNil.
      * intros a _ S. inversion S.
    + intros a S. inversion S.
  - unfold nextSince_del_ovWait_h0. apply stepIntDel.
    + apply stepIlDel.
    + apply stepOlLift. apply stepTlDelEmp.
    + apply stepNlLift. apply stepTlDelEmp.
  - apply stepMsDelSing.
  - unfold displacement, dist2d, origin. simpl. rewrite distance_refl.
    apply Rmult_le_pos. apply speedMax_nonneg. destruct d1 as [[r rpos]]. simpl. lra.
  - apply nextSince_del_ovWait_ok_noSync.
    unfold nextSince_del_ovWait_P0, ovWait. repeat constructor.
Qed.

Lemma nextSince_del_ovWait_net_nextSince (m : Mode) :
  nextSinceStateNet 0 (nextSince_del_ovWait_net m).
Proof.
  unfold nextSinceStateNet, nextSince_del_ovWait_net.
  eapply lenWitness; [ | apply einConsLeft].
  unfold nextSinceStateEnt. apply lifpe. unfold nextSinceStateProt. apply lftOv.
  apply (nexsOvwSt _ m zeroTime zeroTime zeroTime). unfold ovWaitState.
  apply ProcEquiv.bisim_refl.
Qed.

(** ovWait with the pause timer at x+d (>0) cannot output on pause immediately,
whereas P0 can, so they are not bisimilar. *)
Lemma nextSince_del_ovWait_not_bisim (m m1 : Mode) (t1 x1 y1 : Time) (d : Delay) :
  ProcEquiv.bisimulation (nextSince_del_ovWait_P0 m) (ovWait m1 t1 (delToTime (x1 +dt+ d)) (delToTime (y1 +dt+ d))) ->
  False.
Proof.
  intro BS. destruct BS as [F _].
  assert (exists p', nextSince_del_ovWait_P0 m -P- (actDisc (chanPause *!)) -P> p') as [p' S].
  { eexists. apply stepPDisc. unfold nextSince_del_ovWait_P0, ovWait.
    apply stepDpChoiceR. apply stepDpTimeOut. apply stepDpOut. constructor.
    reflexivity. }
  destruct (F _ _ S) as [q' [S' _]].
  inversion S' as [a q'' SD | ]; subst. unfold ovWait in SD.
  inversion SD; subst.
  - match goal with H : stepDiscProc (sum _ _) _ _ |- _ => inversion H; subst end.
    + match goal with H : stepDiscProc (sum _ _) _ _ |- _ => inversion H; subst end;
      match goal with H : stepDiscProc (inPrefix _ _ _) _ _ |- _ => inversion H end.
    + match goal with H : stepDiscProc (del _ _) _ _ |- _ => inversion H; subst end.
      match goal with H : stepDiscProc (inPrefix _ _ _) _ _ |- _ => inversion H end.
  - match goal with H : stepDiscProc (del _ _) _ _ |- _ => inversion H; subst end.
    match goal with H : evalExpFunTime _ = Some zeroTime |- _ => rename H into E end.
    destruct x1 as [[x1 x1nn]]. destruct d as [[d dpos]].
    unfold evalExpFunTime in E. simpl in E. inversion E. lra.
Qed.

Lemma nextSince_del_ovWait_cex (m : Mode) (d1 : Delay) :
  ~ (forall (n n' : Network) (i : nat) (d : Delay),
     n -ND- d -ND> n' -> nextSinceStateNet i n ->
     exists m t x y, ovWaitStateNet m t (delToTime (x +dt+ d)) (delToTime (y +dt+ d)) i n).
Proof.
  intro H.
  destruct (nextSince_del_ovWait_net_del m d1) as [n' ND].
  destruct (H _ _ _ _ ND (nextSince_del_ovWait_net_nextSince m))
    as (m1 & t1 & x1 & y1 & OW).
  destruct OW as [e0 X EIN]. unfold nextSince_del_ovWait_net in EIN.
  inversion EIN; subst.
  unfold ovWaitStateEnt in X. inversion X as [p l h k Xp]; subst.
  unfold ovWaitStateProt in Xp. inversion Xp as [p1 p p3 BS]; subst.
  unfold ovWaitState in BS.
  exact (nextSince_del_ovWait_not_bisim _ _ _ _ _ _ BS).
Qed.


(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.nextSince_del_ovWait in exact T).
Lemma audit_nextSince_del_ovWait : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (nextSince_del_ovWait_cex m (mkDelay (mkposreal 1 Rlt_0_1)) H).
Qed.
Print Assumptions audit_nextSince_del_ovWait.
