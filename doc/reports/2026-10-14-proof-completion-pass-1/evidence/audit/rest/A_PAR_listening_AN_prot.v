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

Lemma listening_AN_prot_counterexample :
  listeningStateProt procProtocol /\ ~ discActEnabled procProtocol (chanAN ;? []).
Proof.
  split.
  - unfold listeningStateProt, procProtocol. constructor. unfold listeningState.
    apply bisim_refl.
  - intro D. inversion D as [q TR]. clear D. unfold procProtocol in TR.
    repeat invert_trans;
    try match goal with [H : length _ = length _ |- _] => simpl in H; inversion H end.
Qed.

Lemma listening_AN_prot_fixed p v :
  length v = 2%nat -> listeningStateProt p -> discActEnabled p (chanAN ;? v).
Proof.
  intros L LS. inversion LS as [p1 p2 p3 Q]; subst.
  apply daeParR; apply daeParR.
  eapply bisim_dae; [apply bisim_symm; apply Q | ]. unfold listening.
  apply daeSumL; apply daeSumL; apply daeSumL. apply dae_inPfx. simpl. rewrite L. reflexivity.
Qed.


Print Assumptions listening_AN_prot_counterexample.

Print Assumptions listening_AN_prot_fixed.

Lemma listening_AN_prot_refuted :
  ~ (forall p v, listeningStateProt p -> discActEnabled p (chanAN ;? v)).
Proof.
  intro H. destruct listening_AN_prot_counterexample as [L N]. exact (N (H _ _ L)).
Qed.
Print Assumptions listening_AN_prot_refuted.
