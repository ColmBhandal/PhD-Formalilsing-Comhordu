(* HELPERS *)
(** A process in the abortOvlp state can output on abort.*)
Lemma abortOvlpStateEnt_urgent_aux1 (p : ProcTerm) :
  abortOvlpState p -> discActEnabled p (chanAbort *!).
  activation_tac. Qed.

(** A process in the ovWait state can input on abort.*)
Lemma abortOvlpStateEnt_urgent_aux2 (p : ProcTerm) (m : Mode) (t x y : Time) :
  ovWaitState m t x y p -> discActEnabled p (chanAbort *?).
  activation_tac. Qed.
(* PROOF *)
Proof.
  intros RE AS DEL. destruct e as [p l h k].
  apply reachable_ent_prot in RE. apply reachableProt_triple in RE.
  inversion AS; subst.
  match goal with [H : abortOvlpStateProt _ |- _] => inversion H; subst end.
  inversion RE; subst.
  inversion DEL; subst.
  match goal with [PD : _ -PD- _ -PD> _ |- _] =>
    let SRT := fresh "SRT" in lets SRT : del_triple_sort PD;
    destruct SRT as [_ [_ S23]] end.
  (*The listener outputs on abort, while the overlap component (dormant or ovWait)
  inputs on abort, so the triple cannot delay.*)
  apply (S23 (chanAbort *?)).
  - apply enabledInSort_in.
    match goal with [OV : overlapState _ |- _] => inversion OV end.
    + apply dormant_abort_in. assumption.
    + eapply abortOvlpStateEnt_urgent_aux2. eassumption.
  - simpl. apply enabledInSort_out. apply abortOvlpStateEnt_urgent_aux1. assumption.
Qed.
