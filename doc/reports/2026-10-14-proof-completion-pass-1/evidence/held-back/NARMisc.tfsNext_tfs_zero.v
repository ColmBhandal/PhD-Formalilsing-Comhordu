(* HELPERS *)
(* PROOF *)
Proof.
  intros n t i m p H. induction H; intros TN.
  - reflexivity.
  - match goal with W : _ -NA- _ -NA> _ |- _ =>
      lets PR : tfsNext_prev_net TN W end.
    destruct PR as [TN' | TS].
    + apply IHtfs; assumption.
    + eapply tfsStart_tfs_zero; eassumption.
  - exfalso. match goal with W : _ -ND- _ -ND> _ |- _ =>
      eapply tfsNext_urgent_net;
      [eapply del_pres_bkwd_tfsNext; [exact W | exact TN] | exact W] end.
Qed.
