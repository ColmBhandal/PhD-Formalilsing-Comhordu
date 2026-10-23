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

(** An application process is bisimilar to its (substituted) definition body
  (same proof as currOK_next_app_bisim, accepted for ProtAuxResults-1). *)
Lemma rangeBad_next_app_bisim n l :
  n $( l )$ ~p~ subProcTerm (listsToSub (fst (def n)) l) (snd (def n)).
Proof.
  constructor; intros a q T.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
    + inversion D; subst. constructor. match goal with [E : def n = _ |- _] =>
        rewrite E end. simpl. assumption.
  - exists q. split; [ | apply bisim_refl]. inversion T as [a' q' D | d q' D]; subst.
    + constructor. apply stepDpApp_alt. assumption.
    + constructor. remember (def n) as dn. destruct dn as [l1 b].
      eapply stepTpApp. symmetry. eassumption. assumption.
Qed.

(** Necessity: the target forces Mode to have, for every m'', a mode distinct
  from m''.  Reading a non-mode value on chanMCurr leaves rangeBad in a process
  bisimilar to currOK m'', which is currEq m m'' only when m <> m''. *)
Lemma rangeBad_next_needs_two_modes :
  (forall (p p' : ProcTerm) (a : DiscAct) (m'' : Mode),
    p -PA- a -PA> p' -> rangeBadState m'' p ->
    (exists m, currEqState m m'' p')) ->
  forall m'' : Mode, exists m, m <> m''.
Proof.
  intros F m''.
  eassert (S : rangeBad (eBase (baseMode m'')) -PA- chanMCurr ;? [baseTime zeroTime] -PA> _)
    by (apply stepDpIn; reflexivity).
  destruct (F _ _ _ m'' S (bisim_refl _)) as [m B]. clear S.
  destruct (eqDecMode m m'') as [E | NE]; [ | exists m; exact NE].
  subst m. exfalso.
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp] in B.
  unfold currEqState in B. remove_updates_hyp B.
  assert (Q : discActEnabled (currEq (eBase (baseMode m'')) (eBase (baseMode m''))) (chanBad *!)).
  { econstructor. apply stepDpChoiceL. apply stepDpThen.
    - apply stepDpApp_alt. cbn. apply stepDpOut. constructor.
    - apply evalBoolExpTrueTot. eapply bevalEqualTrue; apply evalBase. }
  match type of B with ?X ~p~ _ =>
    assert (C : X ~p~ currOKN $([eBase (baseMode m'')])$) end.
  { eapply bisim_trans; [apply rangeBad_next_app_bisim | ].
    cbn [def fst snd listsToSub liftVarList liftExpList subProcTerm subExp subBoolExp
      listSub map liftNameProc listBaselistExp currEq]. remove_updates.
    apply if_then_bisim_false. eapply bevalEqualFalse;
      [apply evalBase | apply evalBase | discriminate]. }
  apply bisim_symm in B. pose proof (bisim_trans _ _ _ B C) as D.
  destruct (bisim_dae _ _ _ D Q) as [q S].
  inversion S; subst.
  match goal with H : def currOKN = _ |- _ => cbn in H; inversion H; subst end.
  match goal with H : subProcTerm _ _ -PA- _ -PA> _ |- _ => cbn in H end.
  repeat match goal with
    | H : sum _ _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H
    | H : inPrefix _ _ _ -PA- _ -PA> _ |- _ => inversion H
    end.
Qed.

(** Every discrete step of rangeBad m'' is an mCurr read of a single base
  value b, after which the listener is (bisimilar to) currEq b m''. *)
Lemma rangeBad_next_inv m'' a q :
  rangeBad (eBase (baseMode m'')) -PA- a -PA> q ->
  exists b, a = chanMCurr ;? [b] /\ q ~p~ currEq (eBase b) (eBase (baseMode m'')).
Proof.
  intro S. unfold rangeBad in S. inversion S; subst.
  match goal with [H : length ?l = length _ |- _] =>
    destruct l as [ | b [ | b' l]]; simpl in H; try discriminate H end.
  exists b. split; [reflexivity | ].
  cbn [listsToSub liftVarList liftExpList listBaselistExp map subProcTerm listSub
    liftNameProc subExp].
  remove_updates.
  eapply bisim_trans; [apply rangeBad_next_app_bisim | ].
  cbn [def fst snd listsToSub liftVarList liftExpList subProcTerm subExp subBoolExp
    listSub map liftNameProc listBaselistExp currEq].
  remove_updates. apply bisim_refl.
Qed.

(** Corrected statement 1 (tracking): reading mode m gives currEq m m''. *)
Lemma rangeBad_next_track (p p' : ProcTerm) (m m'' : Mode) :
  p -PA- chanMCurr ;? [baseMode m] -PA> p' -> rangeBadState m'' p ->
  currEqState m m'' p'.
Proof.
  intros S U. destruct U as [U1 U2]. apply stepPDisc in S. apply U1 in S.
  destruct S as [q [W B]]. inversion W; subst.
  match goal with H : rangeBad _ -PA- _ -PA> _ |- _ =>
    apply rangeBad_next_inv in H; destruct H as [b [E C]] end.
  inversion E; subst. unfold currEqState.
  eapply bisim_trans; [exact B | exact C].
Qed.

Lemma rangeBad_next_isMode (b : BaseType) :
  (exists m, b = baseMode m) \/ (forall m, b <> baseMode m).
Proof.
  destruct b as [m|t|l|d|d|r];
  first [left; exists m; reflexivity | right; intros m0 X; discriminate X].
Qed.

(** A non-mode read and a read of any mode other than m'' behave alike. *)
Lemma rangeBad_next_currOK (b : BaseType) (m'' : Mode) :
  b <> baseMode m'' ->
  currEq (eBase b) (eBase (baseMode m'')) ~p~ currOKN $([eBase (baseMode m'')])$.
Proof.
  intro N. unfold currEq. apply if_then_bisim_false.
  eapply bevalEqualFalse; [apply evalBase | apply evalBase | exact N].
Qed.

Lemma rangeBad_next_nonmode (b : BaseType) (m0 m'' : Mode) :
  (forall m, b <> baseMode m) -> m0 <> m'' ->
  currEq (eBase b) (eBase (baseMode m'')) ~p~ currEq (eBase (baseMode m0)) (eBase (baseMode m'')).
Proof.
  intros N NE. eapply bisim_trans.
  - apply rangeBad_next_currOK. apply N.
  - apply bisim_symm. apply rangeBad_next_currOK.
    intro X. inversion X. contradiction.
Qed.

(** Corrected statement 2: the original conclusion, given a mode other than m''. *)
Lemma rangeBad_next_two_modes (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) :
  (exists m0, m0 <> m'') ->
  p -PA- a -PA> p' -> rangeBadState m'' p ->
  (exists m, currEqState m m'' p').
Proof.
  intros [m0 NE] S U. destruct U as [U1 U2]. apply stepPDisc in S. apply U1 in S.
  destruct S as [q [W B]]. inversion W; subst.
  match goal with H : rangeBad _ -PA- _ -PA> _ |- _ =>
    apply rangeBad_next_inv in H; destruct H as [b [E C]] end.
  pose proof (bisim_trans _ _ _ B C) as D. clear B C.
  destruct (rangeBad_next_isMode b) as [[m Eb] | N].
  - subst b. exists m. exact D.
  - exists m0. unfold currEqState. eapply bisim_trans.
    + exact D.
    + apply rangeBad_next_nonmode; assumption.
Qed.


Print Assumptions rangeBad_next_needs_two_modes.

Print Assumptions rangeBad_next_track.

Print Assumptions rangeBad_next_two_modes.
