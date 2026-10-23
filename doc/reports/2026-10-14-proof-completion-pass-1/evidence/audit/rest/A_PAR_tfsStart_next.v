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

Lemma tfsStart_next_cex :
  ~ (forall (p p' : ProcTerm) (a : DiscAct),
     p -PA- a -PA> p' -> tfsStartState p -> exists m, tfsNextState m p').
Proof.
  intro H.
  assert (TR : tfsStart -PA- chanMCurr ;? [baseTime zeroTime] -PA>
     subProcTerm (listsToSub [vM] (listBaselistExp [baseTime zeroTime])) (tfsNextN $(eVar vM)$)).
  { unfold tfsStart. apply stepDpIn. reflexivity. }
  destruct (H _ _ _ TR (bisim_refl _)) as [m B].
  assert (DA : discActEnabled (tfsNext m) (chanMNext ;! [baseMode (failSafeSucc m)])).
  { apply tfsNext_mNext_out. apply bisim_refl. }
  destruct DA as [q ST].
  destruct B as [_ BW].
  destruct (BW _ _ (stepPDisc _ _ _ ST)) as [r [SR _]].
  inversion SR as [a0 r0 SD EQ | ]; subst.
  clean_proc_hyp SD.
  invert_app_trans.
  repeat match goal with
  | Y : stepDiscProc (sum _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : stepDiscProc (outPrefix _ _ _) _ _ |- _ => inversion Y; subst; clear Y
  | Y : evalExpLists (_ :: _) _ |- _ => inversion Y; subst; clear Y
  | Y : evalExp (eFailSafeSucc _) _ |- _ => inversion Y; subst; clear Y
  | Y : evalExp (eBase _) _ |- _ => inversion Y; subst; clear Y
  end.
Qed.

(** An application process is bisimilar to its (substituted) definition body
(copied from ProtAuxResults-1's currOK_next_app_bisim). *)
Lemma tfsStart_next_app_bisim n l :
  n $( l )$ ~p~ subProcTerm (listsToSub (fst (def n)) l) (snd (def n)).
Proof.
  constructor; intros a q T.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + constructor. apply stepDpApp_alt. assumption.
    + constructor. remember (def n) as dn. destruct dn as [l1 b].
      eapply stepTpApp. symmetry. eassumption. assumption.
Qed.

(** Corrected statement: restricted to the only action a tfsStart-state
process can take inside a well-formed entity (reading a mode on mCurr). *)
Lemma tfsStart_next_fixed (p p' : ProcTerm) (m : Mode) :
  p -PA- chanMCurr ;? [baseMode m] -PA> p' -> tfsStartState p ->
  tfsNextState m p'.
Proof.
  intros TR TS. unfold tfsStartState in TS. unfold tfsNextState.
  destruct TS as [FW _].
  destruct (FW _ _ (stepPDisc _ _ _ TR)) as [q [SQ BQ]].
  inversion SQ as [a0 q0 SD EQ | ]; subst.
  unfold tfsStart in SD. inversion SD; subst.
  eapply bisim_trans; [exact BQ | ].
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp].
  remove_updates.
  eapply bisim_trans; [apply tfsStart_next_app_bisim | ].
  cbn [def fst snd listsToSub liftVarList liftExpList listBaselistExp map subProcTerm
    listSub liftNameProc subExp tfsNext].
  remove_updates.
  apply bisim_refl.
Qed.


Print Assumptions tfsStart_next_cex.

Print Assumptions tfsStart_next_fixed.
