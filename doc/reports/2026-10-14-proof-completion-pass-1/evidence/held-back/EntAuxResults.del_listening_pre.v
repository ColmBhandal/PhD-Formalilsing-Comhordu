(* HELPERS *)
(** A process in the rangeBad state can read any mode on mCurr.*)
Lemma del_listening_pre_aux1 (p : ProcTerm) (m m0 : Mode) :
  rangeBadState m p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
  activation_tac. Qed.

(** A process in the currOK state can input on mStable.*)
Lemma del_listening_pre_aux2 (p : ProcTerm) (m : Mode) :
  currOKState m p -> discActEnabled p (chanMStable *?).
  activation_tac. Qed.

(** A process in the currOK state can input any mode on mNext.*)
Lemma del_listening_pre_aux3 (p : ProcTerm) (m m0 : Mode) :
  currOKState m p -> discActEnabled p (chanMNext ;? [baseMode m0]).
  activation_tac. Qed.
(* PROOF *)
Proof.
  intros RE DEL. destruct e as [p l h k].
  lets RP : reachable_ent_prot RE. apply reachableProt_triple in RP.
  inversion RP; subst.
  (*Case analysis on the state of the listener component.*)
  match goal with [LI : listenerState _ |- _] => inversion LI end.
  (*listening*)
  - right. right. left. constructor. constructor. assumption.
  (*rangeBad: urgent via a read of the current mode from the mode state.*)
  - exfalso. eapply gotRangeStateEnt_urgent_aux2; [ | eassumption].
    intro m0. apply parTriple_dae_intro3.
    eapply del_listening_pre_aux1. eassumption.
  (*currOK: urgent via mStable or mNext with the mode state.*)
  - exfalso. eapply currCompStateEnt_urgent_aux3; [ | | eassumption].
    + apply parTriple_dae_intro3. eapply del_listening_pre_aux2. eassumption.
    + intro m0. apply parTriple_dae_intro3.
      eapply del_listening_pre_aux3. eassumption.
  (*abortOvlp*)
  - left. constructor. constructor. assumption.
  (*badOvlp*)
  - right. left. constructor. constructor. assumption.
  (*currComp: urgent.*)
  - exfalso. eapply currCompStateEnt_urgent; [eassumption | | eassumption].
    constructor. constructor. eassumption.
Qed.
