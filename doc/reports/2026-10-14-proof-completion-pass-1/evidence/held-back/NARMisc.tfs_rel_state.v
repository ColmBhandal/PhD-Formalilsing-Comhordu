(* HELPERS *)
(* PROOF *)
Proof.
  intros H. induction H.
  - apply tfsStart_tfs_net; assumption.
  - assumption.
  - match goal with W : _ -ND- _ -ND> _ |- _ =>
      apply (proj1 (tfsState_del_pres_net _ _ _ _ W)) end; assumption.
Qed.
