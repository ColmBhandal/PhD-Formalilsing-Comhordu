Lemma gotMsg_state_cex m l : ~ (forall p p',
  p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p').
Proof.
  intro H.
  assert (TR : (chanInProc $<[vM'', vL']>$? nilProc) -PA-
    chanInProc;? [baseMode m, basePosition l] -PA> nilProc).
  { change nilProc with (subProcTerm (listsToSub [vM'', vL']
      (listBaselistExp [baseMode m, basePosition l])) nilProc) at 2.
    constructor. reflexivity. }
  specialize (H _ _ TR). inversion H.
Qed.

Lemma gotMsg_state_implies_no_mode :
  (forall p p' m l,
    p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p') ->
  Mode -> False.
Proof.
  intros H m. set (l := mkPosition 0%R 0%R). apply (gotMsg_state_cex m l). intros. eapply H; eauto.
Qed.
