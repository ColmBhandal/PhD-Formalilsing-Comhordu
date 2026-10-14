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

(* ===== helpers copied verbatim from work/w1b-09/NetAuxBasics.tfsCurrStateNet_bktrk_net.v ===== *)

(* Counterexample (explore only): without reachability the overlap slot may hold
   an arbitrary term that steps into tfsCurr, here  chanPos<vL>? tfsCurr. *)
Lemma tfsCurrStateNet_bktrk_net_cex (m : Mode) :
  ~ (forall (n n' : Network) (i : nat) (a : ActDiscNet),
  tfsCurrStateNet i n' -> n -NA- a -NA> n' ->
  tfsCurrStateNet i n \/
  (exists m mF, exists p,
  tfsNextStateNet m i n /\ failSafe mF /\
  mState_in_net (<| m, mF, modeTransTime m mF p |>) i n')).
Proof.
  intro H.
  pose (l := mkPosition 0%R 0%R).
  pose (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  assert (PT : nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc
     -PA- chanPos ;? [basePosition l] -PA> nilProc $||$ tfsCurr $||$ nilProc).
  { change (nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc
     -PA- chanPos ;? [basePosition l] -PA> nilProc $||$
     (subProcTerm (listsToSub [vL] (listBaselistExp [basePosition l])) tfsCurr)
     $||$ nilProc).
    apply stepDpParR. apply stepDpParL. apply stepDpIn. reflexivity. }
  assert (ST : [[|nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc, l, h, sing m|]]
     -NA- anTau -NA> [[|nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m|]]).
  { apply stepDnTauHead. apply stepDePosRead. exact PT. }
  assert (TC : tfsCurrStateNet 0 [[|nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m|]]).
  { eapply lenWitness; [ | apply einConsLeft]. apply lifpe. apply lftOv.
    unfold tfsCurrState. apply ComhCoq.ProcEquiv.bisim_refl. }
  destruct (H _ _ _ _ TC ST) as [A | [m' [mF [pr [A _]]]]];
  destruct A as [e X E]; inversion E; subst;
  inversion X as [p0 l0 h0 k0 Y]; subst;
  inversion Y as [q1 q2 q3 Z]; subst.
  - lets D : tfsCurr_mCurr_out Z. destruct D as [q T]. inversion T.
  - lets D : tfsNext_mStable_out Z. destruct D as [q T]. inversion T.
Qed.
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsCurrStateNet_bktrk_net in exact T).
Lemma audit_tfsCurrStateNet_bktrk_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (tfsCurrStateNet_bktrk_net_cex m H).
Qed.
Print Assumptions audit_tfsCurrStateNet_bktrk_net.
