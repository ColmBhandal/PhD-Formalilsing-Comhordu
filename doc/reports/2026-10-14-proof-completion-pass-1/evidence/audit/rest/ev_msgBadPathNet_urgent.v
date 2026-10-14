(* HELPERS *)
From Stdlib Require Import Lra.

Lemma msgBadPathNet_urgent_cex_steps a q :
  stepDiscProc (nilProc $||$ nilProc $||$ badOvlp) a q -> a = chanBad *!.
Proof.
  unfold badOvlp. intro H.
  repeat match goal with
  | [ H : stepDiscProc nilProc _ _ |- _ ] => inversion H
  | [ H : stepDiscProc (parComp _ _) _ _ |- _ ] => inversion H; subst; clear H
  | [ H : stepDiscProc (outPrefix _ _ _) _ _ |- _ ] => inversion H; subst; clear H
  | [ H : evalExpLists [] _ |- _ ] => inversion H; subst; clear H
  end; reflexivity.
Qed.

Lemma msgBadPathNet_urgent_cex_del d q :
  stepTimedProc (nilProc $||$ nilProc $||$ badOvlp) d q ->
  q = nilProc $||$ nilProc $||$ badOvlp.
Proof.
  unfold badOvlp. intro H.
  repeat match goal with
  | [ H : stepTimedProc nilProc _ _ |- _ ] => inversion H; subst; clear H
  | [ H : stepTimedProc (parComp _ _) _ _ |- _ ] => inversion H; subst; clear H
  | [ H : stepTimedProc (outPrefix _ _ _) _ _ |- _ ] => inversion H; subst; clear H
  end; reflexivity.
Qed.

Lemma msgBadPathNet_urgent_cex_nosync a i k :
  noSyncNow a (nilProc $||$ nilProc $||$ badOvlp) i k.
Proof.
  unfold noSyncNow. intros [q Hst]. apply msgBadPathNet_urgent_cex_steps in Hst.
  subst a. simpl. split; intro Hc; inversion Hc; subst;
  match goal with
  | [ H : stepInter _ _ _ |- _ ] => inversion H
  | [ H : stepModeState _ _ _ |- _ ] => inversion H
  end.
Qed.

(* A one-entity network that is on the msgBadPath (listener in badOvlp) yet can delay. *)
Lemma msgBadPathNet_urgent_cex (m : Mode) (d : Delay) :
  exists n n', msgBadPathNet 0 n /\ n -ND- d -ND> n'.
Proof.
  set (e := [| nilProc $||$ nilProc $||$ badOvlp, origin,
              mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |]).
  exists [e]. eexists. split.
  - apply lenWitness with (e := e); [ | constructor].
    apply mbpBad. constructor. unfold badOvlpState. apply ProcEquiv.bisim_refl.
  - apply stepTnCons; [ | apply stepTnEmp].
    unfold e. eapply stepTeDel with (delta := origin).
    + apply stepTpPar; [constructor | | intros a Hs; inversion Hs].
      apply stepTpPar; [constructor | unfold badOvlp; constructor | intros a Hs; inversion Hs].
    + apply stepIntDel; [apply stepIlDel | apply stepOlLift; apply stepTlDelEmp
                        | apply stepNlLift; apply stepTlDelEmp].
    + apply stepMsDelSing.
    + unfold displacement. rewrite dist2D_refl. simpl.
      pose proof speedMax_nonneg as SN. destruct d as [[r rpos]]. simpl. nra.
    + unfold noSync. intro a. split.
      * apply msgBadPathNet_urgent_cex_nosync.
      * intros p' i' k' d' _ Hp _ _. apply msgBadPathNet_urgent_cex_del in Hp. subst p'.
        apply msgBadPathNet_urgent_cex_nosync.
Qed.

(* The statement as given implies that Mode is empty. *)
Lemma msgBadPathNet_urgent_refute :
  (forall (n n' : Network) (d : Delay) (i : nat),
     msgBadPathNet i n -> n -ND- d -ND> n' -> False) -> Mode -> False.
Proof.
  intros H m.
  destruct (msgBadPathNet_urgent_cex m (mkDelay (mkposreal 1 Rlt_0_1))) as [n [n' [H1 H2]]].
  exact (H n n' _ 0%nat H1 H2).
Qed.

Lemma msgBadPathNet_urgent_gotMsg_in m l p l0 :
  gotMsgState m l p -> discActEnabled p (chanPos ;? [basePosition l0]).
Proof. activation_tac. Qed.

Lemma msgBadPathNet_urgent_gotRange_in m r p m0 :
  gotRangeState m r p -> discActEnabled p (chanMCurr ;? [baseMode m0]).
Proof. activation_tac. Qed.

Lemma msgBadPathNet_urgent_badOvlp_out p :
  badOvlpState p -> discActEnabled p (chanBad *!).
Proof. activation_tac. Qed.

Lemma msgBadPathNet_urgent_listening_not x a :
  listeningState x -> discActEnabled x a ->
  (a = chanBad *! \/ (exists l0, a = chanPos ;? [basePosition l0]) \/
   (exists m0, a = chanMCurr ;? [baseMode m0])) -> False.
Proof.
  intros L D Ha. lets DB : bisim_dae L D. destruct DB as [q' T].
  unfold listening in T.
  destruct Ha as [Ha | [[l0 Ha] | [m0 Ha]]]; subst a;
  repeat match goal with T0 : _ -PA- _ -PA> _ |- _ => inversion T0; subst; clear T0 end.
Qed.

(* The corrected statement (with reachability) follows from del_listening. *)
Lemma msgBadPathNet_urgent_fixed (n n' : Network) (d : Delay) (i : nat) :
  reachableNet n -> msgBadPathNet i n -> n -ND- d -ND> n' -> False.
Proof.
  intros RN MB W. destruct MB as [e ME EIN].
  destruct (del_net_ent e i n n' d EIN W) as [e' ED].
  assert (RE : reachableEnt e) by (eapply reachable_net_ent; eassumption).
  lets LS : del_listening RE ED.
  inversion LS as [p0 l0 h0 k0 LP EQ]; subst.
  inversion LP as [q1 q2 q3 L3 EQ2]; subst.
  inversion ME; subst.
  - match goal with G : gotMsgStateProt _ _ _ |- _ => inversion G; subst end.
    match goal with G : gotMsgState _ _ q3 |- _ =>
      apply (msgBadPathNet_urgent_listening_not q3 (chanPos ;? [basePosition origin]) L3);
      [ eapply msgBadPathNet_urgent_gotMsg_in; exact G
      | right; left; eexists; reflexivity ] end.
  - match goal with G : gotRangeStateProt _ _ _ |- _ => inversion G; subst end.
    match goal with G : gotRangeState ?mm _ q3 |- _ =>
      apply (msgBadPathNet_urgent_listening_not q3 (chanMCurr ;? [baseMode mm]) L3);
      [ eapply msgBadPathNet_urgent_gotRange_in; exact G
      | right; right; eexists; reflexivity ] end.
  - match goal with G : badOvlpStateProt _ |- _ => inversion G; subst end.
    match goal with G : badOvlpState q3 |- _ =>
      apply (msgBadPathNet_urgent_listening_not q3 (chanBad *!) L3);
      [ apply msgBadPathNet_urgent_badOvlp_out; exact G | left; reflexivity ] end.
Qed.
(* PROOF *)
Proof.
  intros. Show.
Admitted.
