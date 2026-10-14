(* HELPERS *)
(** A process in the rangeBad state can read any mode on mCurr.*)
Lemma del_listening_net_aux1 (p : ProcTerm) (m m0 : Mode) :
  rangeBadState m p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
  activation_tac. Qed.

(** A process in the currOK state can input on mStable.*)
Lemma del_listening_net_aux2 (p : ProcTerm) (m : Mode) :
  currOKState m p -> discActEnabled p (chanMStable *?).
  activation_tac. Qed.

(** A process in the currOK state can input any mode on mNext.*)
Lemma del_listening_net_aux3 (p : ProcTerm) (m m0 : Mode) :
  currOKState m p -> discActEnabled p (chanMNext ;? [baseMode m0]).
  activation_tac. Qed.

(** A process in the currComp state can input on mStable.*)
Lemma del_listening_net_aux4 (p : ProcTerm) (m : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMStable *?).
  activation_tac. Qed.

(** A process in the currComp state can input any mode on mNext.*)
Lemma del_listening_net_aux5 (p : ProcTerm) (m m0 : Mode) (r : Distance) :
  currCompState m r p -> discActEnabled p (chanMNext ;? [baseMode m0]).
  activation_tac. Qed.

(** A process in the abortOvlp state can output on abort.*)
Lemma del_listening_net_aux6 (p : ProcTerm) :
  abortOvlpState p -> discActEnabled p (chanAbort *!).
  activation_tac. Qed.

(** A process in the ovWait state can input on abort.*)
Lemma del_listening_net_aux7 (p : ProcTerm) (m : Mode) (t x y : Time) :
  ovWaitState m t x y p -> discActEnabled p (chanAbort *?).
  activation_tac. Qed.

(** A process in the badOvlp state can output on bad.*)
Lemma del_listening_net_aux8 (p : ProcTerm) :
  badOvlpState p -> discActEnabled p (chanBad *!).
  activation_tac. Qed.

(** A process in the ovWait state can input on bad.*)
Lemma del_listening_net_aux9 (p : ProcTerm) (m : Mode) (t x y : Time) :
  ovWaitState m t x y p -> discActEnabled p (chanBad *?).
  activation_tac. Qed.

(** If the software component of an entity can read any mode on mCurr, then the
entity cannot delay: the mode state can always output its current mode on mCurr.*)
Lemma del_listening_net_aux10 (p : ProcTerm) (l : Position) (h : Interface)
  (k : ModeState) (e' : Entity) (d : Delay) :
  (forall m0, discActEnabled p (chanMCurr ;? [baseMode m0])) ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DA DEL. noSyncNow_tac.
  destruct (NS _ (DA (currModeMState k))) as [_ NM].
  apply NM. simpl. apply modeState_curr_enabled.
Qed.

(** If the software component of an entity can input on mStable and any mode on
mNext, then the entity cannot delay: a stable mode state can always output on
mStable, and an unstable one can always output its next mode on mNext.*)
Lemma del_listening_net_aux11 (p : ProcTerm) (l : Position) (h : Interface)
  (k : ModeState) (e' : Entity) (d : Delay) :
  discActEnabled p (chanMStable *?) ->
  (forall m0, discActEnabled p (chanMNext ;? [baseMode m0])) ->
  [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros DS DN DEL. noSyncNow_tac. destruct k as [m1 | m1 m2 t].
  - destruct (NS _ DS) as [_ NM]. apply NM. simpl.
    econstructor. apply stepMsOutStable.
  - destruct (NS _ (DN m2)) as [_ NM]. apply NM. simpl.
    econstructor. apply stepMsOutNext.
Qed.

(** If the overlap component can input on an empty channel c and the listener can
output on it, then the triple (and hence the entity) cannot delay.*)
Lemma del_listening_net_aux12 (p1 p2 p3 : ProcTerm) (l : Position) (h : Interface)
  (k : ModeState) (e' : Entity) (d : Delay) (c : Channel) :
  discActEnabled p2 (c *?) -> discActEnabled p3 (c *!) ->
  [|p1 $||$ p2 $||$ p3, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros D2 D3 DEL. inversion DEL; subst.
  match goal with [PD : _ -PD- _ -PD> _ |- _] =>
    let SRT := fresh "SRT" in lets SRT : del_triple_sort PD;
    destruct SRT as [_ [_ S23]] end.
  apply (S23 (c *?)).
  - apply enabledInSort_in. assumption.
  - simpl. apply enabledInSort_out. assumption.
Qed.
(* PROOF *)
Proof.
  intros U D E.
  (*The entity e must itself be able to delay.*)
  destruct (link_net_ent_del_fwd n n' e i d D E) as [e' [E' DEL]].
  destruct e as [p l h k].
  (*The software component is a reachable protocol process, hence a triple.*)
  lets RP : link_net_prot_reach U E. apply reachableProt_triple in RP.
  inversion RP as [p1 p2 p3 BS OS LS]; subst.
  (*Case analysis on the state of the listener component.*)
  inversion LS.
  (*listening*)
  - apply (lenWitness _ _ _ ([|p1 $||$ p2 $||$ p3, l, h, k|])).
    + constructor. constructor. assumption.
    + assumption.
  (*rangeBad: urgent via a read of the current mode from the mode state.*)
  - exfalso. eapply del_listening_net_aux10; [ | eassumption].
    intro m0. apply parTriple_dae_intro3.
    eapply del_listening_net_aux1. eassumption.
  (*currOK: urgent via mStable or mNext with the mode state.*)
  - exfalso. eapply del_listening_net_aux11; [ | | eassumption].
    + apply parTriple_dae_intro3. eapply del_listening_net_aux2. eassumption.
    + intro m0. apply parTriple_dae_intro3.
      eapply del_listening_net_aux3. eassumption.
  (*abortOvlp: the overlap component (dormant or ovWait) inputs on abort.*)
  - exfalso. eapply (del_listening_net_aux12 _ _ _ _ _ _ _ _ chanAbort);
      [ | | eassumption].
    + inversion OS.
      * apply dormant_abort_in. assumption.
      * eapply del_listening_net_aux7. eassumption.
    + apply del_listening_net_aux6. assumption.
  (*badOvlp: the overlap component (dormant or ovWait) inputs on bad.*)
  - exfalso. eapply (del_listening_net_aux12 _ _ _ _ _ _ _ _ chanBad);
      [ | | eassumption].
    + inversion OS.
      * apply dormant_bad_in. assumption.
      * eapply del_listening_net_aux9. eassumption.
    + apply del_listening_net_aux8. assumption.
  (*currComp: urgent via mStable or mNext with the mode state.*)
  - exfalso. eapply del_listening_net_aux11; [ | | eassumption].
    + apply parTriple_dae_intro3. eapply del_listening_net_aux4. eassumption.
    + intro m0. apply parTriple_dae_intro3.
      eapply del_listening_net_aux5. eassumption.
Qed.
