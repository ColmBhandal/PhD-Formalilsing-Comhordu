(* HELPERS *)
(* PROOF *)
Proof.
  intros RN W CM CM' NEQ.
  apply currMode_ent_ex in CM. apply currMode_ent_ex in CM'.
  destruct CM as [e [EIN CE]]. destruct CM' as [e' [EIN' CE']].
  destruct e as [p l h k]. destruct e' as [p' l' h' k'].
  assert (k <> k') as KNE.
  { intro EQ. subst k'. apply NEQ. rewrite <- CE, <- CE'. reflexivity. }
  destruct (mState_switch_states n n' i a k k' RN KNE W
    (minet k i n p l h EIN) (minet k' i n' p' l' h' EIN')) as [[A B] | [A B]].
  - right; split; assumption.
  - left; split; assumption.
Qed.
