(* HELPERS *)
(* PROOF *)
Proof.
  intros H T.
  destruct e as [p l h k], e' as [p' l' h' k'].
  unfold tfsStartStateEnt in T. inversion T as [p0 l0 h0 k0 TP]; subst.
  unfold tfsStartStateProt in TP. inversion TP as [p1 p2 p3 TS]; subst.
  lets LES : link_ent_soft_disc H.
  destruct LES as [EQ | [b TR]].
  - subst. left. constructor. constructor. assumption.
  - lets EX : link_par_triple_discEx TR.
    destruct EX as [p1' [p2' [p3' EQ]]]. subst.
    lets W : link_par_triple_discW_2 TR.
    destruct W as [EQ2 | [a' TR2]].
    + subst. left. constructor. constructor. assumption.
    + lets TN : tfsStart_next TR2 TS. destruct TN as [m TN].
      right. exists m. constructor. constructor. assumption.
Qed.
