Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.ProcEquiv.

(* ===== audit evidence ===== *)
Lemma evalBoolExpFalseTot_refuted :
  ~ (forall (e : BoolExp), evalBoolExp e false <-> evalBoolExpFunTot e = false).
Proof.
  intro H. specialize (H (bEqual (eVar (var 0)) (eVar (var 0)))).
  destruct H as [_ H]. specialize (H eq_refl).
  inversion H; subst.
  match goal with [E : evalExp (eVar _) _ |- _] => inversion E end.
Qed.

(* The forward direction alone, as the existing script already shows. *)
Lemma evalBoolExpFalseTot_fwd : forall (e : BoolExp),
  evalBoolExp e false -> evalBoolExpFunTot e = false.
Proof.
  intros e H. apply evalBoolExpRelFun in H.
  unfold evalBoolExpFunTot. rewrite H. reflexivity.
Qed.


Print Assumptions evalBoolExpFalseTot_refuted.

Print Assumptions evalBoolExpFalseTot_fwd.
