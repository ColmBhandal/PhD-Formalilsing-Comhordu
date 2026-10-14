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

(* ===== helpers copied verbatim from work/w1b-15/NetAuxBasics.tfsCurrState_del_pres_net.v ===== *)

From Stdlib Require Import Lra.
Require Import ComhCoq.ProcEquiv.

Ltac tfsCurrState_del_pres_net_inv :=
  repeat match goal with
  | Y : stepDiscProc nilProc _ _ |- _ => inversion Y
  | Y : stepDiscProc (sum _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepDiscProc (inPrefix _ _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepDiscProc (outPrefix _ _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : evalExpLists [] _ |- _ => inversion Y; subst; clear Y
  end.

Lemma tfsCurrState_del_pres_net_acts a r :
  stepDiscProc tfsCurr a r ->
  a = chanAbort *? \/ a = chanBad *? \/ a = chanMCurr *!.
Proof.
  intro H. unfold tfsCurr in H. tfsCurrState_del_pres_net_inv;
  repeat match goal with L : length ?l = length (@nil Var) |- _ =>
    destruct l; [clear L | simpl in L; discriminate] end;
  auto.
Qed.

Lemma tfsCurrState_del_pres_net_tdel d x :
  stepTimedProc tfsCurr d x -> x = tfsCurr.
Proof.
  intro H. unfold tfsCurr in H.
  repeat match goal with
  | Y : stepTimedProc (sum _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepTimedProc (inPrefix _ _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepTimedProc (outPrefix _ _ _) _ _ |- _ => inversion Y; subst; clear Y
  end. reflexivity.
Qed.

Definition tfsCurrState_del_pres_net_mid (q : ProcTerm) : Prop :=
  q = tfsCurr \/ exists e, q = del e tfsCurr.

Lemma tfsCurrState_del_pres_net_actsP q a r :
  tfsCurrState_del_pres_net_mid q ->
  stepDiscProc (nilProc $||$ q $||$ nilProc) a r ->
  a = chanAbort *? \/ a = chanBad *? \/ a = chanMCurr *!.
Proof.
  intros M H. inversion H; subst.
  - inversion H4.
  - inversion H4; subst.
    + destruct M as [M | [e M]]; subst.
      * eapply tfsCurrState_del_pres_net_acts; eassumption.
      * inversion H5; subst. eapply tfsCurrState_del_pres_net_acts; eassumption.
    + inversion H5.
    + inversion H6.
    + inversion H6.
  - inversion H2.
  - inversion H2.
Qed.

Lemma tfsCurrState_del_pres_net_derP e d' p' :
  stepTimedProc (nilProc $||$ del e tfsCurr $||$ nilProc) d' p' ->
  exists q, tfsCurrState_del_pres_net_mid q /\ p' = nilProc $||$ q $||$ nilProc.
Proof.
  intro H.
  repeat match goal with
  | Y : stepTimedProc nilProc _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepTimedProc (parComp _ _) _ _ |- _ => inversion Y; subst; clear Y
  end.
  match goal with Y : stepTimedProc (del _ _) _ _ |- _ => inversion Y; subst; clear Y end.
  - match goal with Y : stepTimedProc tfsCurr _ _ |- _ =>
      apply tfsCurrState_del_pres_net_tdel in Y end. subst.
    exists tfsCurr. split; [left; reflexivity | reflexivity].
  - eexists. split; [right; eexists; reflexivity | reflexivity].
  - eexists. split; [right; eexists; reflexivity | reflexivity].
Qed.

Lemma tfsCurrState_del_pres_net_nosyncC a i' m :
  (a = chanAbort *? \/ a = chanBad *? \/ a = chanMCurr *!) ->
  ~discActEnabledInter (a^) i' /\ ~discActEnabledMState (a^) (sing m).
Proof.
  intros [A | [A | A]]; subst; simpl; split; intro X; inversion X; subst;
  try match goal with Y : _ -i- _ -i> _ |- _ => inversion Y end;
  try match goal with Y : _ -ms- _ -ms> _ |- _ => inversion Y end.
Qed.

(* The statement fails without reachability: a middle (overlap) component
   [del 1 tfsCurr] is not bisimilar to tfsCurr, but it delays (by 1 + 1)
   to tfsCurr itself. *)
Lemma tfsCurrState_del_pres_net_cex (m : Mode) :
  ~ (forall (n n' : Network) (d : Delay) (i : nat),
     n -ND- d -ND> n' -> (tfsCurrStateNet i n <-> tfsCurrStateNet i n')).
Proof.
  intro HC.
  pose (t1 := mkTime (mknonnegreal 1 (Rlt_le 0 1 Rlt_0_1))).
  pose (e1 := eBase (baseTime t1)).
  pose (d0 := mkDelay (mkposreal 1 Rlt_0_1)).
  pose (h0 := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  assert (EV : evalExpFunTime e1 = Some t1) by reflexivity.
  assert (TD : stepTimedProc (nilProc $||$ del e1 tfsCurr $||$ nilProc) (t1 +dt+ d0)
                 (nilProc $||$ tfsCurr $||$ nilProc)).
  { apply stepTpPar. apply stepTpNil. apply stepTpPar.
    apply stepTpDelAdd; [ | exact EV]. unfold tfsCurr. repeat constructor.
    apply stepTpNil.
    intros a S1 S2. inversion S2.
    intros a S1 S2. inversion S1. }
  assert (ID : h0 -i- (t1 +dt+ d0) -i> h0).
  { unfold h0. apply stepIntDel; constructor; constructor. }
  assert (NS : noSync (nilProc $||$ del e1 tfsCurr $||$ nilProc) h0 (sing m) (t1 +dt+ d0)).
  { intro a. split.
    - intro DA. destruct DA as [r ST].
      apply tfsCurrState_del_pres_net_nosyncC.
      eapply tfsCurrState_del_pres_net_actsP; [ | exact ST].
      right. eexists. reflexivity.
    - intros p' i' k' d' LT PD IDp KD DA. destruct DA as [r ST].
      apply tfsCurrState_del_pres_net_derP in PD. destruct PD as [q [MQ EQ]]. subst.
      inversion KD; subst.
      apply tfsCurrState_del_pres_net_nosyncC.
      eapply tfsCurrState_del_pres_net_actsP; eassumption. }
  assert (ED : [| nilProc $||$ del e1 tfsCurr $||$ nilProc, origin, h0, sing m |]
                 -ED- (t1 +dt+ d0) ->>
               [| nilProc $||$ tfsCurr $||$ nilProc, addPos origin origin, h0, sing m |]).
  { apply stepTeDel; try assumption. apply stepMsDelSing.
    unfold displacement. rewrite dist2D_refl. simpl.
    apply Rmult_le_pos; [apply cond_nonneg | lra]. }
  assert (ND : [ [| nilProc $||$ del e1 tfsCurr $||$ nilProc, origin, h0, sing m |] ]
                 -ND- (t1 +dt+ d0) -ND>
               [ [| nilProc $||$ tfsCurr $||$ nilProc, addPos origin origin, h0, sing m |] ]).
  { apply stepTnCons. exact ED. apply stepTnEmp. }
  destruct (HC _ _ _ 0%nat ND) as [_ BK].
  assert (T' : tfsCurrStateNet 0
      [ [| nilProc $||$ tfsCurr $||$ nilProc, addPos origin origin, h0, sing m |] ]).
  { econstructor; [ | apply einConsLeft]. constructor. constructor.
    unfold tfsCurrState. apply bisim_refl. }
  apply BK in T'. clear BK.
  inversion T' as [e X EIN]. inversion EIN; subst.
  inversion X as [pp ll hh kk TP]; subst.
  inversion TP as [q1 q2 q3 TS]; subst.
  unfold tfsCurrState in TS.
  destruct TS as [_ BW].
  assert (SC : tfsCurr -P- (chanMCurr *!) -P> tfsBcN).
  { apply stepPDisc. unfold tfsCurr. apply stepDpChoiceR. apply stepDpOut. constructor. }
  destruct (BW _ _ SC) as [p0 [SP0 _]].
  inversion SP0 as [a0 t0 SD EQa | ]; subst.
  inversion SD; subst.
  match goal with E : evalExpFunTime _ = Some zeroTime |- _ =>
    rewrite EV in E; inversion E; lra end.
Qed.
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsCurrState_del_pres_net in exact T).
Lemma audit_tfsCurrState_del_pres_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (tfsCurrState_del_pres_net_cex m H).
Qed.
Print Assumptions audit_tfsCurrState_del_pres_net.
