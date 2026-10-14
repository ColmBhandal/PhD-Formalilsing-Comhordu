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

(* ===== helpers copied verbatim from work/w1b-20/NetAuxBasics.tfsStart_prev_net.cex.v ===== *)

(** The name tfsStartN applied to no arguments is bisimilar to tfsStart.*)
Lemma tfsStart_prev_net_cex_aux1 : ProcEquiv.bisimulation (liftNameProc tfsStartN) tfsStart.
Proof.
  constructor.
  - intros a p' T. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion T; subst.
    + match goal with [H : _ -PA- _ -PA> _ |- _] => inversion H; subst end.
      match goal with [H : def _ = _ |- _] => simpl in H; inversion H; subst end.
      match goal with [H : subProcTerm _ _ -PA- _ -PA> _ |- _] =>
        change (listsToSub [] []) with idSubst in H; rewrite subProc_id_eq in H end.
      apply stepPDisc. assumption.
    + match goal with [H : _ -PD- _ -PD> _ |- _] => inversion H; subst end.
      match goal with [H : def _ = _ |- _] => simpl in H; inversion H; subst end.
      match goal with [H : subProcTerm _ _ -PD- _ -PD> _ |- _] =>
        change (listsToSub [] []) with idSubst in H; rewrite subProc_id_eq in H end.
      apply stepPTimed. assumption.
  - intros a q' T. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion T; subst.
    + apply stepPDisc. eapply stepDpApp; [reflexivity | ].
      change (listsToSub [] []) with idSubst. rewrite subProc_id_eq. assumption.
    + apply stepPTimed. eapply stepTpApp; [reflexivity | ].
      change (listsToSub [] []) with idSubst. rewrite subProc_id_eq. assumption.
Qed.

(** Counterexample: the statement of tfsStart_prev_net is false. The overlap
component dormant inputs on bad (synchronising with the listener in badOvlp) and
becomes tfsStart, but dormant is neither tfsStart nor ovWait.*)
Lemma tfsStart_prev_net_cex (l : Position) (h : Interface) (k : ModeState) :
  ~ (forall i n n' a, tfsStartStateNet i n' -> n -NA- a -NA> n' ->
     tfsStartStateNet i n \/ exists m t x y, ovWaitStateNet m t x y i n).
Proof.
  intro STMT.
  set (e := [|sleeping $||$ dormant $||$ badOvlp, l, h, k|]).
  set (e' := [|sleeping $||$ liftNameProc tfsStartN $||$ liftNameProc listeningN, l, h, k|]).
  assert (ST : [e] -NA- anTau -NA> [e']).
  { apply stepDnTauHead. apply stepDeProcTau. apply stepDpParR.
    eapply (stepDpSyncRL _ _ _ _ chanBad []).
    - unfold dormant. apply stepDpChoiceR. apply stepDpIn. reflexivity.
    - unfold badOvlp. apply stepDpOut. constructor. }
  assert (TS : tfsStartStateNet 0%nat [e']).
  { apply (lenWitness _ _ _ e'); [ | constructor].
    constructor. constructor. apply tfsStart_prev_net_cex_aux1. }
  destruct (STMT 0%nat [e] [e'] anTau TS ST) as [TS0 | [m [t [x [y OW]]]]].
  - inversion TS0 as [e0 X Ein]. inversion Ein; subst.
    inversion X; subst.
    match goal with [H : tfsStartStateProt _ |- _] => inversion H; subst end.
    match goal with [H : tfsStartState _ |- _] => rename H into B end.
    lets D : dormant_abort_in (ProcEquiv.bisim_refl dormant).
    lets D2 : bisim_dae B D. inversion D2 as [q T].
    unfold tfsStart in T. inversion T.
  - inversion OW as [e0 X Ein]. inversion Ein; subst.
    inversion X; subst.
    match goal with [H : ovWaitStateProt _ _ _ _ _ |- _] => inversion H; subst end.
    match goal with [H : ovWaitState _ _ _ _ _ |- _] => rename H into B end.
    lets D : dormant_mNext_in m (ProcEquiv.bisim_refl dormant).
    lets D2 : bisim_dae B D. inversion D2 as [q T].
    unfold ovWait in T.
    repeat match goal with [H : _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H end.
Qed.
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsStart_prev_net in exact T).
Lemma audit_tfsStart_prev_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (tfsStart_prev_net_cex origin (mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])) (sing m) H).
Qed.
Print Assumptions audit_tfsStart_prev_net.
