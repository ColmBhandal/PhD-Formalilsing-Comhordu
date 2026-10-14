(* HELPERS *)
(* PROOF *)
Proof.
  intros RE DEL. destruct e as [p l h k].
  lets RP : reachable_ent_prot RE. apply reachableProt_triple in RP.
  inversion RP; subst.
  (*Case analysis on the state of the overlap component.*)
  match goal with [OV : overlapState _ |- _] => inversion OV end.
  - left. constructor. constructor. assumption.
  - right. right. do 4 eexists. constructor. constructor. eassumption.
Qed.
