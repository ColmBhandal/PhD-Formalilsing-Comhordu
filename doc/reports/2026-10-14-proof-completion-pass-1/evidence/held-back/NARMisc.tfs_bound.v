(* HELPERS *)
From Stdlib Require Import Lra.
(* PROOF *)
Proof.
  intros H.
  induction H as [i0 n0 p0 TS0 CM0 | a0 t0 i0 n0 n0' p0 w0 H0 IH0 TSn
    | d0 t0 i0 n0 n0' p0 w0 H0 IH0].
  - simpl. apply cond_nonneg.
  - exact IH0.
  - lets TS : tfs_rel_state H0. apply tfsState_elim_net in TS.
    destruct TS as [S | [[m2 S] | [S | [S | S]]]].
    + exfalso. eapply tfsStart_urgent_net; eassumption.
    + exfalso. eapply tfsNext_urgent_net; eassumption.
    + assert (TC' : tfsCurrStateNet i0 n0')
        by (apply (proj1 (tfsCurrState_del_pres_net _ _ _ _ w0)); exact S).
      lets TG : tfs_transGuard TC' (tfsDel m d0 t0 i0 n0 n0' p0 w0 H0).
      destruct TG as [t' [_ LE]].
      assert (0 <= nonneg (time t')) by apply cond_nonneg.
      simpl in LE |- *. lra.
    + exfalso. destruct S as [e SE EIN].
      destruct (del_net_ent e i0 n0 n0' d0 EIN w0) as [e' ED].
      eapply tfsBc_urgent; [eapply reachable_net_ent; eassumption | exact SE | exact ED].
    + exfalso. destruct S as [e SE EIN].
      destruct (del_net_ent e i0 n0 n0' d0 EIN w0) as [e' ED].
      eapply tfsListen_urgent; [eapply reachable_net_ent; eassumption | exact SE | exact ED].
Qed.
