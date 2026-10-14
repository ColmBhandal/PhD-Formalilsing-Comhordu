Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxDefs.
From Stdlib Require Import Bool.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProcEquiv.
Require Import ComhCoq.ProtAuxResults.

(* ===== audit evidence ===== *)

(* After inputting a non-mode value on chanMNext, the nextPincCheck derivative is stuck. *)
Lemma currComp_next_stuck (m'' : Mode) (r : Distance) a q :
  nextPincCheckN $( [eBase (baseTime zeroTime), eBase (baseMode m''), eBase (baseDistance r)] )$
    -PA- a -PA> q -> False.
Proof.
  intro T. invert_app_trans.
  match goal with H : _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H end;
  match goal with H : _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H end;
  match goal with H : evalBoolExpFunTot _ = true |- _ => simpl in H; discriminate H end.
Qed.

(* A process bisimilar to a process with some discrete action has a discrete action. *)
Lemma currComp_next_bisim_act X Y a q :
  X ~p~ Y -> Y -PA- a -PA> q -> exists q', X -PA- a -PA> q'.
Proof.
  intros B T. inversion B as [F G]. apply stepPDisc in T. apply G in T.
  destruct T as [p' [T _]]. inversion T; subst. eexists. eassumption.
Qed.

Lemma currComp_next_listening_act :
  exists q, liftNameProc listeningN -PA- chanPause ;? [] -PA> q.
Proof.
  eexists. apply stepDpApp_alt. cbn [def fst snd listsToSub liftNameProc]. rewrite subProc_id_eq. unfold listening.
  apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpIn. reflexivity.
Qed.

Lemma currComp_next_cex (m'' : Mode) (r : Distance) :
  (forall p p' a, p -PA- a -PA> p' -> currCompState m'' r p ->
     (exists m, nextPincCheckState m m'' r p') \/ listeningState p') -> False.
Proof.
  intro H.
  assert (TR : exists p', currComp m'' r -PA- chanMNext ;? [baseTime zeroTime] -PA> p').
  { eexists. unfold currComp. apply stepDpChoiceR. apply stepDpIn. reflexivity. }
  destruct TR as [p' TR].
  assert (CS : currCompState m'' r (currComp m'' r)) by apply bisim_refl.
  destruct (H _ _ _ TR CS) as [[m NP] | LS];
  unfold currComp in TR; inversion TR; subst;
  try match goal with H4 : chanMStable ? _ -PA- _ -PA> _ |- _ => inversion H4 end;
  match goal with H4 : chanMNext $< _ >$ ? _ -PA- _ -PA> _ |- _ => inversion H4; subst end.
  - clean_proc_hyp NP. unfold nextPincCheckState, nextPincCheck in NP.
    remember (possIncBool m m'' r) as PB eqn:EPB. destruct PB.
    + assert (A : exists q, (!~ bPossInc m m'' r $> listeningN $+$ bPossInc m m'' r $> abortOvlpN)
                     -PA- chanAbort *! -PA> q).
      { eexists. apply stepDpChoiceR. apply stepDpThen.
        - apply stepDpApp_alt. simpl. apply stepDpOut. constructor.
        - unfold evalBoolExpFunTot. simpl. rewrite <- EPB. reflexivity. }
      destruct A as [q A]. destruct (currComp_next_bisim_act _ _ _ _ NP A) as [q' A'].
      eapply currComp_next_stuck. exact A'.
    + destruct currComp_next_listening_act as [q0 L0].
      assert (A : exists q, (!~ bPossInc m m'' r $> listeningN $+$ bPossInc m m'' r $> abortOvlpN)
                     -PA- chanPause ;? [] -PA> q).
      { eexists. apply stepDpChoiceL. apply stepDpThen.
        - exact L0.
        - unfold evalBoolExpFunTot. simpl. rewrite <- EPB. reflexivity. }
      destruct A as [q A]. destruct (currComp_next_bisim_act _ _ _ _ NP A) as [q' A'].
      eapply currComp_next_stuck. exact A'.
  - clean_proc_hyp LS. unfold listeningState in LS.
    assert (A : exists q, listening -PA- chanPause ;? [] -PA> q).
    { eexists. unfold listening. apply stepDpChoiceL. apply stepDpChoiceR. apply stepDpIn. reflexivity. }
    destruct A as [q A]. destruct (currComp_next_bisim_act _ _ _ _ LS A) as [q' A'].
    eapply currComp_next_stuck. exact A'.
Qed.


Print Assumptions currComp_next_cex.
