From Stdlib Require Import Program.Equality.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs. 
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults. 
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.NARMisc.

(* ===== audit evidence ===== *)

(* Demonstration helpers for the .fail.md (not a proof of the target). *)

(* The derivative of the overlap's chanBad? branch in tfsListen is bisimilar to tfsListen. *)
Lemma msgBad_disc_net_tfsListen_unfold :
  ProcEquiv.bisimulation (subProcTerm (listsToSub [] []) (liftNameProc tfsListenN)) tfsListen.
Proof.
  assert (E0 : subProcTerm (listsToSub [] []) (liftNameProc tfsListenN) = liftNameProc tfsListenN).
  { change (listsToSub [] []) with idSubst. apply subProc_id_eq. }
  rewrite E0.
  assert (E : subProcTerm (listsToSub [] []) tfsListen = tfsListen).
  { change (listsToSub [] []) with idSubst. apply subProc_id_eq. }
  constructor.
  - intros a p' S. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S as [a0 t' D | d t' D]; subst.
    + constructor. inversion D; subst.
      match goal with Hd : def _ = (_, _), Hs : _ -PA- _ -PA> _ |- _ =>
        cbv [def] in Hd; inversion Hd; subst; rewrite E in Hs; exact Hs end.
    + apply stepPTimed. inversion D; subst.
      match goal with Hd : def _ = (_, _), Hs : _ -PD- _ -PD> _ |- _ =>
        cbv [def] in Hd; inversion Hd; subst; rewrite E in Hs; exact Hs end.
  - intros a q' S. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S as [a0 t' D | d t' D]; subst.
    + constructor. eapply stepDpApp. reflexivity. rewrite E. exact D.
    + apply stepPTimed. eapply stepTpApp. reflexivity. rewrite E. exact D.
Qed.

(* The listening state can do none of: chanPos input, chanMCurr input, chanBad output. *)
Lemma msgBad_disc_net_listen_no_pos v :
  ~ discActEnabled (liftNameProc listeningN) (chanPos ;? v).
Proof.
  intros [q TR]. invert_app_trans. unfold listening in *.
  repeat invert_trans.
Qed.

Lemma msgBad_disc_net_listen_no_curr v :
  ~ discActEnabled (liftNameProc listeningN) (chanMCurr ;? v).
Proof.
  intros [q TR]. invert_app_trans. unfold listening in *.
  repeat invert_trans.
Qed.

Lemma msgBad_disc_net_listen_no_bad :
  ~ discActEnabled (liftNameProc listeningN) (chanBad *!).
Proof.
  intros [q TR]. invert_app_trans. unfold listening in *.
  repeat invert_trans.
Qed.

(* An entity whose listener component is `listening` is not on the msgBadPath. *)
Lemma msgBad_disc_net_tgt_not P1 q l h k :
  ~ msgBadPathEnt ([| P1 $||$ q $||$ liftNameProc listeningN, l, h, k |]).
Proof.
  intro M. inversion M; subst.
  - match goal with [X : gotMsgStateProt _ _ _ |- _] => inversion X; subst end.
    match goal with [X : gotMsgState ?m ?l0 _ |- _] =>
      unfold gotMsgState in X; apply ProcEquiv.bisim_symm in X;
      apply (msgBad_disc_net_listen_no_pos [basePosition l]);
      eapply bisim_dae; [apply X | unfold gotMsg; apply dae_inPfx; reflexivity] end.
  - match goal with [X : gotRangeStateProt _ _ _ |- _] => inversion X; subst end.
    match goal with [X : gotRangeState ?m ?r _ |- _] =>
      unfold gotRangeState in X; apply ProcEquiv.bisim_symm in X;
      apply (msgBad_disc_net_listen_no_curr [baseMode m]);
      eapply bisim_dae; [apply X | unfold gotRange; apply dae_inPfx; reflexivity] end.
  - match goal with [X : badOvlpStateProt _ |- _] => inversion X; subst end.
    match goal with [X : badOvlpState _ |- _] =>
      unfold badOvlpState in X; apply ProcEquiv.bisim_symm in X;
      apply msgBad_disc_net_listen_no_bad;
      eapply bisim_dae; [apply X | unfold badOvlp; apply dae_outPfx; constructor] end.
Qed.

(* One-step demonstration at network level: entity 0 has its overlap in tfsListen and its
   listener in badOvlp (so it is on the msgBadPath). The listener's chanBad! is absorbed by
   tfsListen's chanBad? (internal tau). Afterwards the listener is `listening`, so the entity is
   off the msgBadPath, while the overlap is still in tfsListen and the mode state is unchanged.
   Hence the only way to satisfy the target's conclusion is tfs m zeroTime 0 n' _, which needs
   the last tfsStart of this overlap to have been at zero elapsed time and in the current mode. *)
Lemma msgBad_disc_net_onestep (P1 : ProcTerm) l h k :
  msgBadPathNet 0 [ [| P1 $||$ tfsListen $||$ badOvlp, l, h, k |] ] /\
  tfsListenStateNet 0 [ [| P1 $||$ tfsListen $||$ badOvlp, l, h, k |] ] /\
  [ [| P1 $||$ tfsListen $||$ badOvlp, l, h, k |] ] -NA- anTau -NA>
  [ [| P1 $||$ subProcTerm (listsToSub [] []) (liftNameProc tfsListenN)
       $||$ liftNameProc listeningN, l, h, k |] ] /\
  ~ msgBadPathNet 0 [ [| P1 $||$ subProcTerm (listsToSub [] []) (liftNameProc tfsListenN)
       $||$ liftNameProc listeningN, l, h, k |] ] /\
  tfsListenStateNet 0 [ [| P1 $||$ subProcTerm (listsToSub [] []) (liftNameProc tfsListenN)
       $||$ liftNameProc listeningN, l, h, k |] ].
Proof.
  splits.
  - econstructor; [ | constructor]. apply mbpBad. constructor.
    apply ProcEquiv.bisim_refl.
  - econstructor; [ | constructor]. constructor. constructor.
    apply ProcEquiv.bisim_refl.
  - apply stepDnTauHead. apply stepDeProcTau. apply stepDpParR.
    apply stepDpSyncRL with (c := chanBad) (l := []);
    [ unfold tfsListen;
      first [ apply stepDpChoiceL; apply stepDpChoiceR; apply stepDpIn; reflexivity
            | apply stepDpChoiceR; apply stepDpChoiceL; apply stepDpIn; reflexivity ]
    | unfold badOvlp; apply stepDpOut; constructor ].
  - intro M. inversion M as [e0 M1 M2]; subst.
    inversion M2; subst.
    eapply msgBad_disc_net_tgt_not. apply M1.
  - econstructor; [ | constructor]. constructor. constructor.
    apply msgBad_disc_net_tfsListen_unfold.
Qed.


Print Assumptions msgBad_disc_net_onestep.
