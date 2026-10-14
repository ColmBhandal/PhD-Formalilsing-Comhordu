(* HELPERS *)
(** A process in the badOvlp state can output on bad.*)
Lemma del_listening_aux1 (p : ProcTerm) :
  badOvlpState p -> discActEnabled p (chanBad *!).
  activation_tac. Qed.

(** A process in the ovWait state can input on bad.*)
Lemma del_listening_aux2 (p : ProcTerm) (m : Mode) (t x y : Time) :
  ovWaitState m t x y p -> discActEnabled p (chanBad *?).
  activation_tac. Qed.
(* PROOF *)
Proof.
  intros RE DEL.
  lets DLP : del_listening_pre RE DEL.
  lets DO : del_ovlp RE DEL.
  destruct e as [p l h k].
  destruct DLP as [AO | [BO | [LS | PA]]].
  (*abortOvlp: urgent.*)
  - exfalso. eapply abortOvlpStateEnt_urgent; eassumption.
  (*badOvlp: the listener outputs on bad, and each of the possible overlap states
  (dormant, tfsCurr, ovWait) inputs on bad, so the software cannot delay.*)
  - exfalso.
    inversion BO; subst.
    match goal with [H : badOvlpStateProt _ |- _] => inversion H; subst end.
    inversion DEL; subst.
    match goal with [PD : _ -PD- _ -PD> _ |- _] =>
      let SRT := fresh "SRT" in lets SRT : del_triple_sort PD;
      destruct SRT as [_ [_ S23]] end.
    apply (S23 (chanBad *?)).
    + apply enabledInSort_in.
      destruct DO as [DO | [DO | DO]].
      * inversion DO; subst.
        match goal with [H : dormantStateProt _ |- _] => inversion H; subst end.
        apply dormant_bad_in. assumption.
      * inversion DO; subst.
        match goal with [H : tfsCurrStateProt _ |- _] => inversion H; subst end.
        apply tfsCurr_bad_in. assumption.
      * destruct DO as [m [t [x [y DO]]]]. inversion DO; subst.
        match goal with [H : ovWaitStateProt _ _ _ _ _ |- _] => inversion H; subst end.
        eapply del_listening_aux2. eassumption.
    + simpl. apply enabledInSort_out. apply del_listening_aux1. assumption.
  (*listening*)
  - assumption.
  (*paused: then by paused_switch the overlap component is in a switch state, each of
  which is urgent.*)
  - exfalso.
    lets RP : reachable_ent_prot RE.
    assert (SW : switchStateProt p).
    { destruct (paused_switch p RP) as [PS _]. apply PS.
      inversion PA; subst. assumption. }
    inversion SW; subst.
    match goal with [H : switchState _ |- _] => inversion H end.
    + eapply switchBc_urgent; [eassumption | | eassumption].
      constructor. constructor. eassumption.
    + eapply (swithcCurr_urgent (currModeMState k)); [eassumption | | eassumption].
      constructor. constructor. eassumption.
    + eapply switchListen_urgent; [eassumption | | eassumption].
      constructor. constructor. eassumption.
Qed.
