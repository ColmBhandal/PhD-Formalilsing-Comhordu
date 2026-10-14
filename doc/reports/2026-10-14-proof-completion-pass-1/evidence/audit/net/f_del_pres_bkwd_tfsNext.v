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

(* ===== helpers copied verbatim from work/w1b-10/NetAuxBasics.del_pres_bkwd_tfsStart.cex.v ===== *)

From Stdlib Require Import Lra.
Require Import ComhCoq.ProcEquiv.

(* A delay prefix whose guard is not zero has no discrete transition. *)
Lemma del_pres_bkwd_tfsStart_nodisc (e : Exp) (Q : ProcTerm) a q :
  evalExpFunTime e <> Some zeroTime -> ~ ($< e >$ Q) -PA- a -PA> q.
Proof. intros NZ H. inversion H; subst. contradiction. Qed.

(* nil || q || nil has no discrete transition if q has none. *)
Lemma del_pres_bkwd_tfsStart_tripN (q : ProcTerm) a q' :
  (forall a0 q0, ~ q -PA- a0 -PA> q0) ->
  ~ (nilProc $||$ q $||$ nilProc) -PA- a -PA> q'.
Proof.
  intros NQ S. inversion S; subst;
  repeat match goal with
  | H : nilProc -PA- _ -PA> _ |- _ => inversion H
  | H : (q $||$ nilProc) -PA- _ -PA> _ |- _ => inversion H; subst; clear H
  | H : q -PA- _ -PA> _ |- _ => exact (NQ _ _ H)
  end.
Qed.

(* A zero-guarded Q is bisimilar to Q, if Q only delays to itself. *)
Lemma del_pres_bkwd_tfsStart_bisimG (e : Exp) (Q : ProcTerm) :
  (forall d q, Q -PD- d -PD> q -> q = Q) -> (forall d, Q -PD- d -PD> Q) ->
  evalExpFunTime e = Some zeroTime -> ($< e >$ Q) ~p~ Q.
Proof.
  intros QD QDel EV. constructor.
  - intros a p' S. inversion S as [a0 t' SD | d0 t' ST]; subst.
    + inversion SD; subst. exists p'. split; [constructor; assumption | apply bisim_refl].
    + inversion ST; subst.
      * match goal with H : Q -PD- _ -PD> _ |- _ => apply QD in H; subst end.
        exists Q. split; [ | apply bisim_refl].
        apply stepPTimed. apply QDel.
      * exfalso.
        match goal with H : evalExpFunTime e = Some ?t |- _ =>
          rewrite EV in H; injection H; intro; subst end.
        match goal with H : (_ <= _)%R |- _ => clear S ST; revert H end.
        destruct d0 as [[x xp]]. unfold zeroTime, zeroNonneg. simpl. lra.
      * rewrite EV in *. discriminate.
  - intros a q' S. inversion S as [a0 t' SD | d0 t' ST]; subst.
    + exists q'. split; [ | apply bisim_refl]. apply stepPDisc.
      apply stepDpTimeOut; assumption.
    + apply QD in ST. subst.
      exists Q. split; [ | apply bisim_refl].
      apply stepPTimed. rewrite <- (timeDelAddZeroL d0).
      apply stepTpDelAdd; [apply QDel | exact EV].
Qed.

Lemma del_pres_bkwd_tfsStart_r1 : (0 <= 1)%R.
Proof. lra. Qed.

Definition del_pres_bkwd_tfsStart_t1 : Time :=
  mkTime (mknonnegreal 1 del_pres_bkwd_tfsStart_r1).
Definition del_pres_bkwd_tfsStart_d1 : Delay := mkDelay (mkposreal 1 Rlt_0_1).

Lemma del_pres_bkwd_tfsStart_le :
  (pos (delay del_pres_bkwd_tfsStart_d1) <= nonneg (time del_pres_bkwd_tfsStart_t1))%R.
Proof. simpl. lra. Qed.

Lemma del_pres_bkwd_tfsStart_nz :
  evalExpFunTime (liftTimeExp del_pres_bkwd_tfsStart_t1) <> Some zeroTime.
Proof.
  intro H. simpl in H.
  apply (f_equal (fun o => match o with Some t => nonneg (time t) | None => 0%R end)) in H.
  simpl in H. lra.
Qed.

Lemma del_pres_bkwd_tfsStart_z :
  evalExpFunTime (liftTimeExp (minusTime _ _ del_pres_bkwd_tfsStart_le)) = Some zeroTime.
Proof. cbn. f_equal. apply timeEqR. simpl. lra. Qed.

(* Strictly before the guard expires, the guarded term can do nothing. *)
Lemma del_pres_bkwd_tfsStart_mid (Q : ProcTerm) d' q :
  (pos (delay d') < 1)%R ->
  ($< liftTimeExp del_pres_bkwd_tfsStart_t1 >$ Q) -PD- d' -PD> q ->
  forall a q', ~ q -PA- a -PA> q'.
Proof.
  intros LT D a q' S. inversion D; subst.
  - match goal with H : evalExpFunTime _ = Some _ |- _ =>
      simpl in H; injection H; intro; subst end.
    match goal with d0 : Delay |- _ => destruct d0 as [[x xp]] end.
    simpl in LT. lra.
  - match goal with H : evalExpFunTime (liftTimeExp del_pres_bkwd_tfsStart_t1) = Some _ |- _ =>
      simpl in H; injection H; intro; subst end.
    inversion S; subst.
    match goal with H : evalExpFunTime _ = Some zeroTime |- _ =>
      simpl in H;
      apply (f_equal (fun o => match o with Some t => nonneg (time t) | None => 0%R end)) in H;
      simpl in H end.
    lra.
  - match goal with H : evalExpFunTime _ = None |- _ => simpl in H; discriminate end.
Qed.

Definition del_pres_bkwd_tfsStart_if :=
  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []).

Lemma del_pres_bkwd_tfsStart_step (m : Mode) (Q : ProcTerm) :
  [ [| nilProc $||$ ($< liftTimeExp del_pres_bkwd_tfsStart_t1 >$ Q) $||$ nilProc,
       origin, del_pres_bkwd_tfsStart_if, sing m |] ]
  -ND- del_pres_bkwd_tfsStart_d1 -ND>
  [ [| nilProc $||$ ($< liftTimeExp (minusTime _ _ del_pres_bkwd_tfsStart_le) >$ Q)
       $||$ nilProc, addPos origin origin, del_pres_bkwd_tfsStart_if, sing m |] ].
Proof.
  apply stepTnCons; [ | apply stepTnEmp].
  apply stepTeDel.
  - apply stepTpPar.
    + apply stepTpNil.
    + apply stepTpPar.
      * apply stepTpDelSub. reflexivity.
      * apply stepTpNil.
      * intros a S1 S2. inversion S2.
    + intros a S1 S2. inversion S1.
  - apply stepIntDel.
    + apply stepIlDel.
    + apply stepOlLift. apply stepTlDelEmp.
    + apply stepNlLift. apply stepTlDelEmp.
  - apply stepMsDelSing.
  - unfold displacement. rewrite dist2D_refl. simpl.
    apply Rmult_le_pos; [apply cond_nonneg | lra].
  - intro a. split.
    + intros [q' S]. exfalso. revert S. apply del_pres_bkwd_tfsStart_tripN.
      intros a0 q0. apply del_pres_bkwd_tfsStart_nodisc. exact del_pres_bkwd_tfsStart_nz.
    + intros p'' i' k' d' LT PD _ _ [q' S]. exfalso.
      inversion PD; subst.
      match goal with H : nilProc -PD- _ -PD> _ |- _ => inversion H; subst end.
      match goal with H : (_ $||$ nilProc) -PD- _ -PD> _ |- _ =>
        inversion H; subst end.
      match goal with H : nilProc -PD- _ -PD> _ |- _ => inversion H; subst end.
      match goal with H : ($< _ >$ Q) -PD- _ -PD> _ |- _ =>
        rename H into DM end.
      revert S. apply del_pres_bkwd_tfsStart_tripN.
      eapply (del_pres_bkwd_tfsStart_mid Q); [ | exact DM].
      simpl in LT. exact LT.
Qed.

(* The target statement is refuted, for any mode m. *)
Lemma del_pres_bkwd_tfsStart_refuted (m : Mode) :
  ~ (forall i n n' d,
     n -ND- d -ND> n' -> tfsStartStateNet i n' -> tfsStartStateNet i n).
Proof.
  intro HS. pose proof (del_pres_bkwd_tfsStart_step m tfsStart) as ND.
  match type of ND with _ -ND- _ -ND> (?e' :: []) =>
    assert (tfsStartStateNet 0 (e' :: [])) as T' end.
  { econstructor; [ | apply einConsLeft]. econstructor. econstructor.
    unfold tfsStartState. apply del_pres_bkwd_tfsStart_bisimG;
    [ intros d0 q0 D0; unfold tfsStart in *; inversion D0; reflexivity
    | intro d0; unfold tfsStart; apply stepTpIn
    | exact del_pres_bkwd_tfsStart_z ]. }
  apply (HS _ _ _ _ ND) in T'. inversion T' as [e X EIN]. inversion EIN; subst.
  inversion X as [p l h k TP Hpe]; subst.
  inversion TP as [p1 p2 p3 TS Hp]; subst.
  unfold tfsStartState in TS. apply bisim_symm in TS.
  assert (exists q, tfsStart -PA- (chanMCurr ;? [baseTime zeroTime]) -PA> q) as [q T].
  { eexists. unfold tfsStart. apply stepDpIn. reflexivity. }
  destruct (bisim_disc_match _ _ _ _ TS T) as [q' T2].
  exact (del_pres_bkwd_tfsStart_nodisc _ _ _ _ del_pres_bkwd_tfsStart_nz T2).
Qed.

(* Same construction refutes the sibling NetAuxBasics.del_pres_bkwd_tfsNext. *)
Lemma del_pres_bkwd_tfsStart_tfsNext_refuted (m : Mode) :
  ~ (forall m0 i n n' d,
     n -ND- d -ND> n' -> tfsNextStateNet m0 i n' -> tfsNextStateNet m0 i n).
Proof.
  intro HS. pose proof (del_pres_bkwd_tfsStart_step m (tfsNext m)) as ND.
  match type of ND with _ -ND- _ -ND> (?e' :: []) =>
    assert (tfsNextStateNet m 0 (e' :: [])) as T' end.
  { econstructor; [ | apply einConsLeft]. econstructor. econstructor.
    unfold tfsNextState. apply del_pres_bkwd_tfsStart_bisimG;
    [ intros d0 q0 D0; unfold tfsNext in *;
      repeat match goal with H : _ -PD- _ -PD> _ |- _ => inversion H; subst; clear H end;
      reflexivity
    | intro d0; unfold tfsNext; apply stepTpSum; apply stepTpOut
    | exact del_pres_bkwd_tfsStart_z ]. }
  apply (HS _ _ _ _ _ ND) in T'. inversion T' as [e X EIN]. inversion EIN; subst.
  inversion X as [p l h k TP Hpe]; subst.
  inversion TP as [p1 p2 p3 TS Hp]; subst.
  unfold tfsNextState in TS. apply bisim_symm in TS.
  assert (exists q, tfsNext m -PA- chanMStable *! -PA> q) as [q T].
  { eexists. unfold tfsNext. apply stepDpChoiceR; constructor; constructor. }
  destruct (bisim_disc_match _ _ _ _ TS T) as [q' T2].
  exact (del_pres_bkwd_tfsStart_nodisc _ _ _ _ del_pres_bkwd_tfsStart_nz T2).
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions del_pres_bkwd_tfsStart_tfsNext_refuted.
