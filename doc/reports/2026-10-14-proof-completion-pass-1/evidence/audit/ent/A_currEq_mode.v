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

(* ===== HELPERS copied verbatim from w1b-18/EntAuxResults.currEq_mode.v ===== *)

(* The statement, for arbitrary (unreachable) entities, forces Mode to be a subsingleton. *)
Lemma currEq_mode_cex :
  (forall m m'' e, currEqStateEnt m m'' e -> m = currModeEnt e) ->
  forall m1 m2 : Mode, m1 = m2.
Proof.
  intros H m1 m2.
  apply (H m1 m1 ([| nilProc $||$ nilProc $||$ currEq m1 m1,
                     mkPosition 0%R 0%R, mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil), sing m2 |])).
  unfold currEqStateEnt, currEqStateProt. constructor. constructor.
  unfold currEqState. apply ProcEquiv.bisim_refl.
Qed.

(* ===== end of copied helpers ===== *)

Lemma audit_currEq_mode_subsingleton : forall m1 m2 : Mode, m1 = m2.
Proof. exact (currEq_mode_cex currEq_mode). Qed.

Print Assumptions currEq_mode_cex.
Print Assumptions audit_currEq_mode_subsingleton.
