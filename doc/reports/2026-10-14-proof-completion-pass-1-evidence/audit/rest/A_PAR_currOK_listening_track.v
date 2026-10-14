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

(* Demonstration helpers for a counterexample (see the .fail.md). *)

(** An application process is bisimilar to its unfolded body. *)
Lemma currOK_listening_track_app_bisim n l2 :
  app n l2 ~p~ subProcTerm (listsToSub (fst (def n)) l2) (snd (def n)).
Proof.
  destruct (def n) as [l1 b] eqn:D. simpl. constructor.
  - intros a p' H. exists p'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc.
      match goal with [V : app n l2 -PA- _ -PA> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
    + apply stepPTimed.
      match goal with [V : app n l2 -PD- _ -PD> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
  - intros a q' H. exists q'. split; [ | apply bisim_refl].
    inversion H; subst.
    + apply stepPDisc. eapply stepDpApp; eassumption.
    + apply stepPTimed. eapply stepTpApp; eassumption.
Qed.

Lemma currOK_listening_track_listening_bisim : listeningN ~p~ listening.
Proof.
  eapply bisim_trans; [apply currOK_listening_track_app_bisim | ].
  cbn [def fst snd listsToSub]. rewrite subProc_id_eq. apply bisim_refl.
Qed.

(** From currOK m, reading on chanMNext any value other than m itself leads to
nextEq v m, whose guard is false, so it is bisimilar to listening. *)
Lemma currOK_listening_track_cex_gen (m : Mode) (v : BaseType) :
  v <> baseMode m ->
  exists p p', currOKState m p /\ listeningState p' /\
    p -PA- chanMNext ;? [v] -PA> p'.
Proof.
  intro NE.
  assert (ST : currOK m -PA- chanMNext ;? [v] -PA>
    subProcTerm (listsToSub [vM'] (listBaselistExp [v]))
      (nextEqN $([eVar vM', eBase (baseMode m)])$)).
  { unfold currOK. apply stepDpChoiceR. apply stepDpIn. reflexivity. }
  eexists. eexists. split; [apply bisim_refl | split; [ | exact ST]].
  unfold listeningState. clean_proc.
  eapply bisim_trans; [apply currOK_listening_track_app_bisim | ].
  clean_proc.
  eapply bisim_trans; [apply if_then_bisim_false | apply currOK_listening_track_listening_bisim].
  eapply bevalEqualFalse; [apply evalBase | apply evalBase | exact NE].
Qed.

(** The natural protocol instance: the next mode m' differs from m. *)
Lemma currOK_listening_track_cex_modes (m m' : Mode) : m' <> m ->
  exists p p', currOKState m p /\ listeningState p' /\
    p -PA- chanMNext ;? [baseMode m'] -PA> p'.
Proof.
  intro NE. apply currOK_listening_track_cex_gen. intro E. apply NE. inversion E. reflexivity.
Qed.

(** The target statement is refuted by any Mode. *)
Lemma currOK_listening_track_cex (m : Mode) :
  ~ (forall m p p' a, currOKState m p -> listeningState p' ->
       p -PA- a -PA> p' -> a = (chanMStable *?)).
Proof.
  intro H. destruct (currOK_listening_track_cex_gen m (baseTime zeroTime)) as [p [p' [C [L S]]]].
  - discriminate.
  - specialize (H m p p' _ C L S). discriminate H.
Qed.

(** The listening process never outputs on chanAbort. *)
Lemma currOK_listening_track_listening_no_abort q :
  ~ listening -PA- chanAbort ;! [] -PA> q.
Proof. intro H. unfold listening in H. repeat invert_trans. Qed.

(** Suggested corrected statement, proved here as a demonstration: a step from
currOK m into listening is either the stable read, or a next-mode read of a value
other than m. *)
Lemma currOK_listening_track_fixed m p p' a : currOKState m p ->
  listeningState p' -> p -PA- a -PA> p' ->
  a = (chanMStable *?) \/ exists v, a = chanMNext ;? [v] /\ v <> baseMode m.
Proof.
  intros C L S. unfold currOKState in C.
  apply stepPDisc in S. destruct C as [C1 _]. apply C1 in S. clear C1.
  destruct S as [q' [S B]].
  inversion S as [a0 q0 D | ]; subst. clear S.
  unfold currOK in D. inversion D; subst.
  - match goal with [V : _ $< _ >$ ? _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    left. match goal with [l1 : list BaseType |- _] => destruct l1 end.
    + reflexivity.
    + simpl in *. discriminate.
  - match goal with [V : _ $< _ >$ ? _ -PA- _ -PA> _ |- _] => inversion V; subst end.
    right. match goal with [l1 : list BaseType |- _] => destruct l1 as [ | v [ | ? ?]] end;
      simpl in *; try discriminate.
    exists v. split; [reflexivity | ]. intro E. subst v.
    match goal with [B : p' ~p~ ?Q |- _] =>
      assert (DA : discActEnabled Q (chanAbort ;! [])) end.
    { clean_proc. econstructor. apply stepDpApp_alt. clean_proc.
      apply stepDpChoiceL. apply stepDpThen.
      - apply stepDpApp_alt. clean_proc. apply stepDpOut. constructor.
      - unfold evalBoolExpFunTot. simpl.
        destruct (eqDecBase (baseMode m) (baseMode m)); [reflexivity | congruence]. }
    apply bisim_symm in B. lets DA2 : bisim_dae B DA. lets DA3 : bisim_dae L DA2.
    inversion DA3. eapply currOK_listening_track_listening_no_abort. eassumption.
Qed.


Print Assumptions currOK_listening_track_cex.

Print Assumptions currOK_listening_track_fixed.
