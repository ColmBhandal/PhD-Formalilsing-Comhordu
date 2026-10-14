Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.InterfaceLanguage.

(* ===== audit evidence ===== *)

(* The statement is equivalent to msgLatency = adaptNotif, which the model axioms
   (only positivity of both) do not entail. *)
Lemma notifList_received_in_iff :
  (forall (l l' : NotifList) (v : list BaseType),
     l -nl- v ?? -nl> l' -> <(v, msgLatency)> _: notifList l')
  <-> msgLatency = adaptNotif.
Proof.
  split.
  - intro H.
    specialize (H (mkNotifList []) _ [] (stepNlBuff [] [])).
    simpl in H. destruct H as [H | H]; [| destruct H].
    injection H as Ht. symmetry. exact Ht.
  - intros E l l' v H. inversion H; subst.
    + simpl. left. rewrite E. reflexivity.
    + match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
Qed.
(* The corrected statement is provable. *)
Lemma notifList_received_in_fixed : forall (l l' : NotifList) (v : list BaseType),
  l -nl- v ?? -nl> l' -> <(v, adaptNotif)> _: notifList l'.
Proof.
  intros l l' v H. inversion H; subst.
  - simpl. left. reflexivity.
  - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
Qed.


Print Assumptions notifList_received_in_iff.

Print Assumptions notifList_received_in_fixed.
