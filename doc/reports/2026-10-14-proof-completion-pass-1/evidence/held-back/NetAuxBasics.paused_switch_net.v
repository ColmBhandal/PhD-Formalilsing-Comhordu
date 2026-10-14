(* HELPERS *)
(* PROOF *)
Proof.
  intro R. split; intro H; destruct H as [e He Ein]; destruct He as [p l h k Hp];
  (econstructor; [ | exact Ein]); constructor;
  (assert (reachableProt p) as RP by (eapply link_net_prot_reach; eassumption));
  apply (paused_switch p RP); exact Hp.
Qed.
