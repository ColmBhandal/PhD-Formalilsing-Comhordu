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

(* Copied from w1b-17/EntAuxResults.tfsNext_prev_ent.v (same as EntAuxResults-1). *)
Lemma tfsNext_prev_ent_cex :
  (forall m e e' a, tfsNextStateEnt m e' ->
     e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e) ->
  forall (m : Mode) (l : Position) (h : Interface), False.
Proof.
  intros H m l h.
  pose (q := nilProc $||$ tfsNext m $||$ nilProc).
  assert (S : [| outPrefix chanMCurr [] q, l, h, <|m, m, zeroTime|> |] -EA- aeTau ->>
              [| q, l, h, sing m |]).
  { apply (stepDeCurrWrite _ _ _ _ _ _ m). constructor. constructor. constructor. }
  assert (T : tfsNextStateEnt m ([| q, l, h, sing m |])).
  { unfold tfsNextStateEnt, tfsNextStateProt. constructor. unfold q. constructor.
    unfold tfsNextState. apply ProcEquiv.bisim_refl. }
  destruct (H _ _ _ _ T S) as [X | X];
  unfold tfsNextStateEnt, tfsNextStateProt, tfsStartStateEnt, tfsStartStateProt in X;
  inversion X as [p0 l0 h0 k0 Y]; inversion Y.
Qed.

(* Audit: the admitted lemma refutes every inhabitant of Mode. *)
Lemma audit_tfsNext_prev_ent_Mode_False : Mode -> False.
Proof.
  intro m. apply (tfsNext_prev_ent_cex tfsNext_prev_ent m (mkPosition 0%R 0%R)
    (mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil))).
Qed.

Print Assumptions tfsNext_prev_ent_cex.
Print Assumptions audit_tfsNext_prev_ent_Mode_False.
