(* HELPERS *)
Require Import ComhCoq.ProcEquiv.
(** Urgency of tfsStart at the network level (local copy; the public
    version tfsStart_urgent_net comes later in the file). *)
Lemma del_pres_bkwd_tfsNext_urgS i n n' d :
  tfsStartStateNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros U V.
  inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  inversion ED as [d0 q q' l0 delta h0 h' k0 k' PD ID KD DISP NS]; subst.
  lets DA : tfsStart_mCurr_in (currModeMState k) TS.
  assert (discActEnabled (p1 $||$ p2 $||$ p3)
    (chanMCurr ;? [baseMode (currModeMState k)])) as DA2.
  { apply parTriple_dae_intro2. exact DA. }
  destruct (NS (chanMCurr ;? [baseMode (currModeMState k)])) as [NSN _].
  destruct (NSN DA2) as [_ NM]. apply NM. apply modeState_curr_enabled.
Qed.

(** Urgency of tfsNext at the network level (local copy; the public
    version tfsNext_urgent_net comes later in the file). *)
Lemma del_pres_bkwd_tfsNext_urgN m i n n' d :
  tfsNextStateNet m i n -> n -ND- d -ND> n' -> False.
Proof.
  intros U V.
  inversion U as [e SE EIN].
  destruct (del_net_ent e i n n' d EIN V) as [e' ED].
  inversion SE as [p l h k TP Hpe]. subst e.
  inversion TP as [p1 p2 p3 TS Hp]. subst p.
  inversion ED as [d0 q q' l0 delta h0 h' k0 k' PD ID KD DISP NS]; subst.
  assert (currModeNet (currModeEnt ([|p1 $||$ p2 $||$ p3, l, h, k|])) i n) as CM.
  { eapply currMode_intro; [reflexivity | exact EIN]. }
  lets EQ : tfsNext_currModeNet_eq CM U.
  assert (currModeMState k -mtr-> failSafeSucc m) as FS2.
  { simpl in EQ. rewrite EQ. apply failSafeSucc_successor. }
  lets MS : mState_stable_next_enabled FS2.
  destruct MS as [MS1 | MS2].
  - lets DA : tfsNext_mStable_out TS.
    assert (discActEnabled (p1 $||$ p2 $||$ p3) (chanMStable *!)) as DA2.
    { apply parTriple_dae_intro2. exact DA. }
    destruct (NS (chanMStable *!)) as [NSN _].
    destruct (NSN DA2) as [_ NM]. apply NM. exact MS1.
  - lets DA : tfsNext_mNext_out TS.
    assert (discActEnabled (p1 $||$ p2 $||$ p3)
      (chanMNext ;! ([baseMode (failSafeSucc m)]))) as DA2.
    { apply parTriple_dae_intro2. exact DA. }
    destruct (NS (chanMNext ;! ([baseMode (failSafeSucc m)]))) as [NSN _].
    destruct (NSN DA2) as [_ NM]. apply NM. exact MS2.
Qed.

(** Exhaustively inverts process transitions (discrete and timed). *)
Ltac del_pres_bkwd_tfsNext_inv :=
  repeat match goal with
  | [H : _ -PD- _ -PD> _ |- _] => inversion H; subst; clear H
  | [H : _ -PA- _ -PA> _ |- _] => inversion H; subst; clear H
  end.

(** The tfsCurr, tfsBc and tfsListen terms only delay to themselves. *)
Lemma del_pres_bkwd_tfsNext_dC d q : tfsCurr -PD- d -PD> q -> q = tfsCurr.
Proof. intro H. unfold tfsCurr in *. del_pres_bkwd_tfsNext_inv. reflexivity. Qed.

Lemma del_pres_bkwd_tfsNext_dB d q : tfsBc -PD- d -PD> q -> q = tfsBc.
Proof. intro H. unfold tfsBc in *. del_pres_bkwd_tfsNext_inv. reflexivity. Qed.

Lemma del_pres_bkwd_tfsNext_dL d q : tfsListen -PD- d -PD> q -> q = tfsListen.
Proof. intro H. unfold tfsListen in *. del_pres_bkwd_tfsNext_inv. reflexivity. Qed.

(** tfsNext m is not bisimilar to tfsCurr, tfsBc or tfsListen: it can output
    on mStable, which none of these can. *)
Ltac del_pres_bkwd_tfsNext_nbN_tac m :=
  let B := fresh "B" in let q := fresh "q" in let T := fresh "T" in
  let q' := fresh "q'" in let T' := fresh "T'" in
  intro B;
  assert (exists q, tfsNext m -PA- chanMStable *! -PA> q) as [q T];
  [eexists; unfold tfsNext; apply stepDpChoiceR; constructor; constructor | ];
  destruct (bisim_disc_match _ _ _ _ B T) as [q' T'];
  clear - T'; unfold tfsCurr, tfsBc, tfsListen in T'; del_pres_bkwd_tfsNext_inv.

Lemma del_pres_bkwd_tfsNext_nbNC m : ~ (tfsNext m ~p~ tfsCurr).
Proof. del_pres_bkwd_tfsNext_nbN_tac m. Qed.

Lemma del_pres_bkwd_tfsNext_nbNB m : ~ (tfsNext m ~p~ tfsBc).
Proof. del_pres_bkwd_tfsNext_nbN_tac m. Qed.

Lemma del_pres_bkwd_tfsNext_nbNL m : ~ (tfsNext m ~p~ tfsListen).
Proof. del_pres_bkwd_tfsNext_nbN_tac m. Qed.

(** Generic backward step: if the overlap component of entity i is
    bisimilar to a term X that only delays to itself, and after a network
    delay it is bisimilar to Y, then X and Y are bisimilar. *)
Lemma del_pres_bkwd_tfsNext_net (Y X : ProcTerm) i n n' d :
  (forall q, X -PD- d -PD> q -> q = X) -> ~ (Y ~p~ X) ->
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ X))) i n ->
  n -ND- d -ND> n' ->
  liftEntNet (liftProcEnt (liftOverlap (fun p => p ~p~ Y))) i n' -> False.
Proof.
  intros XD NB HX V HY.
  inversion HX as [e SE EIN]. inversion HY as [e' SE' EIN'].
  lets ED : link_net_ent_delW V EIN' EIN.
  inversion SE as [p l h k TP Hpe]; subst e.
  inversion SE' as [p' l' h' k' TP' Hpe']; subst e'.
  inversion TP as [p1 p2 p3 TS Hp]; subst p.
  inversion TP' as [p1' p2' p3' TS' Hp']; subst p'.
  apply link_ent_soft_del in ED.
  apply link_par_triple_del in ED. destruct ED as [_ [D2 _]].
  cbv beta in TS, TS'.
  apply stepPTimed in D2. destruct TS as [F _].
  destruct (F _ _ D2) as [q [Tq Bq]].
  inversion Tq as [ | d1 q1 Dq]; subst.
  apply XD in Dq. subst q.
  apply NB. eapply bisim_trans; [apply bisim_symm; exact TS' | exact Bq].
Qed.
(* PROOF *)
Proof.
  intros V U.
  assert (tfsStateNet i n') as TS by (eapply tfsNext_tfs_net; exact U).
  apply (proj2 (tfsState_del_pres_net n n' i d V)) in TS.
  apply tfsState_elim_net in TS.
  destruct TS as [S | [[m0 S] | [S | [S | S]]]].
  - exfalso. eapply del_pres_bkwd_tfsNext_urgS; eassumption.
  - exfalso. eapply del_pres_bkwd_tfsNext_urgN; eassumption.
  - exfalso. apply (del_pres_bkwd_tfsNext_net (tfsNext m) tfsCurr i n n' d
      (del_pres_bkwd_tfsNext_dC d) (del_pres_bkwd_tfsNext_nbNC m) S V U).
  - exfalso. apply (del_pres_bkwd_tfsNext_net (tfsNext m) tfsBc i n n' d
      (del_pres_bkwd_tfsNext_dB d) (del_pres_bkwd_tfsNext_nbNB m) S V U).
  - exfalso. apply (del_pres_bkwd_tfsNext_net (tfsNext m) tfsListen i n n' d
      (del_pres_bkwd_tfsNext_dL d) (del_pres_bkwd_tfsNext_nbNL m) S V U).
Qed.
