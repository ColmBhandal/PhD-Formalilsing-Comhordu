Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.InterfaceLanguage.

(* ===== audit evidence ===== *)

From Stdlib Require Import Lra.
(* Counterexample: stepIlDel lets any input list delay to the empty list. *)
Lemma inList_pres_input_false :
  ~ (forall v l l' a,
       <( v, zeroTime )> _: inList l -> l -il- a -il> l' ->
       <( v, zeroTime )> _: inList l' \/ a = v !!).
Proof.
  intro H.
  set (d1 := mkDelay (mkposreal 1 Rlt_0_1)).
  destruct (H [] (mkInputList [<([], zeroTime)>]) (mkInputList []) (atlDel d1))
    as [Hin | Ha].
  - simpl. left. reflexivity.
  - apply stepIlDel.
  - exact Hin.
  - discriminate Ha.
Qed.
(* Generic preservation lemma for outputs on timed lists. *)
Lemma inList_pres_input_tl_out : forall l a l', l -tl- a -tl> l' ->
  forall u x, a = atlOut u -> x _: l -> x _: l' \/ x = <(u, zeroTime)>.
Proof.
  intros l a l' H.
  induction H as [v1 l1 | l1 l1' v1 e Hs IH | d1 | l1 l1' d1 v1 t1 t1' Hs IH Ht];
    intros u x Ea Hin; try discriminate.
  - injection Ea as Eu. subst. destruct Hin as [Hx | Hx].
    + right. subst. reflexivity.
    + left. assumption.
  - destruct Hin as [Hx | Hx].
    + left. left. assumption.
    + destruct (IH u x Ea Hx) as [Hy | Hy].
      * left. right. assumption.
      * right. assumption.
Qed.
(* A timed-out element blocks any timed-list delay. *)
Lemma inList_pres_input_tl_del : forall l a l', l -tl- a -tl> l' ->
  forall (d : Delay) v, a = atlDel d -> <(v, zeroTime)> _: l -> False.
Proof.
  intros l a l' H.
  induction H as [v1 l1 | l1 l1' v1 e Hs IH | d1 | l1 l1' d1 v1 t1 t1' Hs IH Ht];
    intros d v Ea Hin; try discriminate.
  - destruct Hin.
  - destruct Hin as [Hx | Hx].
    + injection Hx as Hv Ht1. rewrite Ht1 in Ht.
      apply (f_equal (fun x : Time => nonneg (time x))) in Ht. simpl in Ht.
      pose proof (cond_nonneg (time t1')). pose proof (cond_pos (delay d1)). lra.
    + eapply IH; eassumption.
Qed.
(* The corrected statement (non-delay actions) is provable. *)
Lemma inList_pres_input_fixed v l l' a :
  (forall d, a <> atlDel d) ->
  <( v, zeroTime )> _: inList l -> l -il- a -il> l' ->
  <( v, zeroTime )> _: inList l' \/ a = v !!.
Proof.
  intros Hnd Hin H. inversion H; subst.
  - left. simpl. right. exact Hin.
  - exfalso. eapply Hnd. reflexivity.
  - simpl in Hin. destruct a.
    + exfalso. eapply Hnd. reflexivity.
    + match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
    + match goal with [Htl : stepTimedList _ _ _ |- _] =>
        destruct (inList_pres_input_tl_out _ _ _ Htl _ _ eq_refl Hin) as [Hy | Hy] end.
      * left. assumption.
      * right. injection Hy as Hv. subst. reflexivity.
Qed.
(* Sanity check: the only user, inList_inter_pres_input, still goes through
   with the corrected statement. *)
Lemma inList_pres_input_user_check v lix lox lnx lix' lox' lnx' a :
  (forall d, a <> aiDel d) -> <(v, zeroTime )> _: inList lix ->
  mkInterface lix lox lnx -i- a -i> mkInterface lix' lox' lnx' ->
  <(v, zeroTime )> _: inList lix' \/ a = chanInProc{! v.
Proof.
  intros Hnd Hin H. inversion H; subst; try (left; assumption).
  - exfalso. eapply Hnd. reflexivity.
  - match goal with [Hs : stepInputList _ ?act _ |- _] =>
      assert (ND : forall d, act <> atlDel d) by (intros dd EE; discriminate EE);
      destruct (inList_pres_input_fixed _ _ _ _ ND Hin Hs) as [Hy|Hy] end;
    [left; assumption | discriminate Hy].
  - match goal with [Hs : stepInputList _ ?act _ |- _] =>
      assert (ND : forall d, act <> atlDel d) by (intros dd EE; discriminate EE);
      destruct (inList_pres_input_fixed _ _ _ _ ND Hin Hs) as [Hy|Hy] end;
    [left; assumption | right; injection Hy as Hv; subst; reflexivity].
Qed.


Print Assumptions inList_pres_input_false.

Print Assumptions inList_pres_input_fixed.

Print Assumptions inList_pres_input_user_check.
