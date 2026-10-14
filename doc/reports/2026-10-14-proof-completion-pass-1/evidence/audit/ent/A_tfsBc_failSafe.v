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

(* ===== HELPERS copied verbatim from EntAuxResults-1/EntAuxResults.tfsBc_failSafe.v ===== *)

(* The statement forces every mode to be fail-safe. *)
Lemma tfsBc_failSafe_cex :
  (forall e, tfsBcStateEnt e -> failSafe (currModeEnt e)) ->
  Position -> Interface -> forall m : Mode, failSafe m.
Proof.
  intros H l h m.
  apply (H ([| nilProc $||$ tfsBc $||$ nilProc, l, h, sing m |])).
  unfold tfsBcStateEnt, tfsBcStateProt. constructor. constructor.
  unfold tfsBcState. apply ProcEquiv.bisim_refl.
Qed.

Lemma tfsBc_failSafe_cex2 :
  (exists m, ~ failSafe m) -> Position -> Interface ->
  ~ (forall e, tfsBcStateEnt e -> failSafe (currModeEnt e)).
Proof.
  intros [m NF] l h H. apply NF. exact (tfsBc_failSafe_cex H l h m).
Qed.

(* ===== end of copied helpers ===== *)

(* Audit: the admitted lemma forces every mode to be fail-safe. *)
Lemma audit_tfsBc_failSafe_allFS : forall m : Mode, failSafe m.
Proof.
  exact (tfsBc_failSafe_cex tfsBc_failSafe (mkPosition 0%R 0%R)
    (mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil))).
Qed.

(* Hence (minDistCompFS) every minDistComp is 0. *)
Lemma audit_tfsBc_failSafe_minDist0 : forall m1 m2 : Mode, minDistComp m1 m2 = mkDistance zeroNonneg.
Proof. intros. apply minDistCompFS. apply audit_tfsBc_failSafe_allFS. Qed.

Print Assumptions tfsBc_failSafe_cex.
Print Assumptions tfsBc_failSafe_cex2.
Print Assumptions audit_tfsBc_failSafe_allFS.
Print Assumptions audit_tfsBc_failSafe_minDist0.
