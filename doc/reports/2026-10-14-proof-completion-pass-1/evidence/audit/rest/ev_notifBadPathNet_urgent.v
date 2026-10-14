(* HELPERS *)
(** The "stuck" software process used in the counterexample: the listener sits
in badOvlp, the other two components are nilProc, so nothing can synchronise
with the output on bad.*)
Definition notifBadPathNet_urgent_P : ProcTerm :=
  nilProc $||$ nilProc $||$ badOvlp.

Definition notifBadPathNet_urgent_H : Interface :=
  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []).

Lemma notifBadPathNet_urgent_P_del d q :
  notifBadPathNet_urgent_P -PD- d -PD> q -> q = notifBadPathNet_urgent_P.
Proof.
  unfold notifBadPathNet_urgent_P. cbv [badOvlp]. intro T.
  inversion T; subst. 
  match goal with T1 : nilProc -PD- _ -PD> _ |- _ => inversion T1; subst end.
  match goal with T2 : (nilProc $||$ _) -PD- _ -PD> _ |- _ => inversion T2; subst end.
  match goal with T3 : nilProc -PD- _ -PD> _ |- _ => inversion T3; subst end.
  match goal with T4 : outPrefix _ _ _ -PD- _ -PD> _ |- _ => inversion T4; subst end.
  reflexivity.
Qed.

Lemma notifBadPathNet_urgent_P_noSyncNow a i k :
  noSyncNow a notifBadPathNet_urgent_P i k.
Proof.
  unfold noSyncNow, notifBadPathNet_urgent_P. cbv [badOvlp].
  intros [q T].
  repeat match goal with
  | T0 : _ -PA- _ -PA> _ |- _ => inversion T0; subst; clear T0
  end.
  match goal with E : evalExpLists [] _ |- _ => inversion E; subst end.
  simpl. split.
  - intro DI. inversion DI; subst.
    match goal with S : _ -i- _ -i> _ |- _ => inversion S end.
  - intro DM. inversion DM; subst.
    match goal with S : _ -ms- _ -ms> _ |- _ => inversion S end.
Qed.

(** Counterexample to notifBadPathNet_urgent as stated: given any mode m
(the model leaves Mode abstract), a one-entity network on the notifBad path
that can delay by any d.*)
Lemma notifBadPathNet_urgent_cex (m : Mode) (d : Delay) :
  let e := [| notifBadPathNet_urgent_P, origin, notifBadPathNet_urgent_H, sing m |] in
  notifBadPathNet 0 [e] /\ exists n', [e] -ND- d -ND> n'.
Proof.
  intro e. split.
  - apply lenWitness with (e := e); [ | constructor].
    unfold e, notifBadPathNet_urgent_P. apply nbpBad.
    constructor. apply ComhCoq.ProcEquiv.bisim_refl.
  - eexists. apply stepTnCons; [ | apply stepTnEmp].
    unfold e. apply stepTeDel with (delta := origin).
    + unfold notifBadPathNet_urgent_P. cbv [badOvlp].
      apply stepTpPar.
      * apply stepTpNil.
      * apply stepTpPar; [apply stepTpNil | apply stepTpOut | ].
        intros a S. inversion S.
      * intros a S. inversion S.
    + unfold notifBadPathNet_urgent_H. apply stepIntDel.
      * apply stepIlDel.
      * apply stepOlLift. apply stepTlDelEmp.
      * apply stepNlLift. apply stepTlDelEmp.
    + apply stepMsDelSing.
    + unfold displacement. rewrite dist2D_refl. simpl.
      apply Rmult_le_pos; [apply cond_nonneg | left; apply cond_pos].
    + intro a. split.
      * apply notifBadPathNet_urgent_P_noSyncNow.
      * intros p' i' k' d' _ PD _ _.
        apply notifBadPathNet_urgent_P_del in PD. subst.
        apply notifBadPathNet_urgent_P_noSyncNow.
Qed.

(** Hence the statement as given is refutable whenever Mode is inhabited.*)
Lemma notifBadPathNet_urgent_refuted (m : Mode) (d : Delay) :
  ~ (forall i n n' d, notifBadPathNet i n -> n -ND- d -ND> n' -> False).
Proof.
  intro STMT. destruct (notifBadPathNet_urgent_cex m d) as [NB [n' W]].
  exact (STMT _ _ _ _ NB W).
Qed.

Lemma notifBadPathNet_urgent_rangeBad_in m m0 p :
  rangeBadState m p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
Proof. activation_tac. Qed.

(** Copy of NARMisc-2's notifAbortPathNet_urgent_rangeBad_ent (renamed).*)
Lemma notifBadPathNet_urgent_rangeBad_ent m p l h k e' d :
  rangeBadStateProt m p -> [|p, l, h, k|] -ED- d ->> e' -> False.
Proof.
  intros RB ED. inversion RB as [p1 p2 p3 RB3 EQ]; subst.
  noSyncNow_tac.
  destruct (NS (chanMCurr ;? [baseMode (currModeMState k)])) as [_ DM].
  - apply parTriple_dae_intro3.
    exact (notifBadPathNet_urgent_rangeBad_in m (currModeMState k) p3 RB3).
  - apply DM. exact (modeState_curr_enabled k).
Qed.

Lemma notifBadPathNet_urgent_badOvlp_out p :
  badOvlpState p -> discActEnabled p (chanBad *!).
Proof. activation_tac. Qed.

(** The corrected statement (with reachability) is provable.*)
Lemma notifBadPathNet_urgent_fixed i n n' d :
  reachableNet n -> notifBadPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros RN NB W. destruct NB as [e NE EIN].
  destruct (del_net_ent e i n n' d EIN W) as [e' ED].
  assert (RE : reachableEnt e) by (eapply reachable_net_ent; eassumption).
  inversion NE as [p l h k m RB CM | p l h k BO]; subst.
  - eapply notifBadPathNet_urgent_rangeBad_ent; eassumption.
  - lets LS : del_listening RE ED.
    inversion LS as [p0 l0 h0 k0 LP EQ]; subst.
    inversion BO as [p1 p2 p3 B3 EQ1]; subst.
    inversion LP as [q1 q2 q3 L3 EQ2]; subst.
    match goal with B3' : badOvlpState ?x, L3' : listeningState ?x |- _ =>
      pose proof (notifBadPathNet_urgent_badOvlp_out x B3') as D;
      eapply bisim_dae in D; [ | exact L3'] end.
    destruct D as [q' T]. cbv [listening] in T.
    repeat match goal with
    | T0 : _ -PA- _ -PA> _ |- _ => inversion T0; subst; clear T0
    end.
Qed.
(* PROOF *)
Proof.
Admitted.
