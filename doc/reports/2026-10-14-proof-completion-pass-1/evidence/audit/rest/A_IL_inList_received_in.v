Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.InterfaceLanguage.

(* ===== audit evidence ===== *)

From Stdlib Require Import Lra.
(* Counterexample: the statement is refutable. *)
Lemma inList_received_in_false :
  ~ (forall (l l' : InputList) (v : list BaseType),
       l -il- v ?? -il> l' -> <(v, msgLatency)> _: inList l').
Proof.
  intro H.
  specialize (H (mkInputList []) _ [] (stepIlBuff [] [])).
  simpl in H. destruct H as [H | H]; [| exact H].
  injection H as Ht.
  apply (f_equal (fun x : Time => nonneg (time x))) in Ht. simpl in Ht.
  pose proof msgLatency_positive. lra.
Qed.
(* The corrected statement is provable. *)
Lemma inList_received_in_fixed : forall (l l' : InputList) (v : list BaseType),
  l -il- v ?? -il> l' -> <(v, zeroTime)> _: inList l'.
Proof.
  intros l l' v H. inversion H; subst.
  - simpl. left. reflexivity.
  - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
Qed.


Print Assumptions inList_received_in_false.

Print Assumptions inList_received_in_fixed.
