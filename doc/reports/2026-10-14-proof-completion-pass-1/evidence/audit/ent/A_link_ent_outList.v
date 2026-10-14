Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxResults.

(* ===== HELPERS copied verbatim from EntAuxResults-3/EntAuxResults.link_ent_outList.v ===== *)

(** Counterexample: a process output on outProc buffered by the interface
grows the output list, which is not a timed-list step in either direction.*)
Lemma link_ent_outList_cex (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
  [|chanOutProc $<[]>$! nilProc, l, {| li := li; lo := mkOutputList []; ln := ln |}, k|]
    -EA- aeTau ->>
  [|nilProc, l, {| li := li; lo := mkOutputList [<([], msgLatency)>]; ln := ln |}, k|] /\
  ~ (mkOutputList [] = mkOutputList [<([], msgLatency)>] \/ exists v,
     outList (mkOutputList []) -tl- v ?? -tl> outList (mkOutputList [<([], msgLatency)>])
  \/ outList (mkOutputList []) -tl- v !! -tl> outList (mkOutputList [<([], msgLatency)>])).
Proof.
  split.
  - eapply stepDeIOProcInter with (v := []).
    + constructor. constructor.
    + constructor. constructor.
  - intros [E | [v [T | T]]].
    + inversion E.
    + inversion T.
    + inversion T.
Qed.

(** Hence the statement of link_ent_outList is refutable.*)
Lemma link_ent_outList_false (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
  ~ (forall p p' l l' k k' li li' lo lo' ln ln' b,
  [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
  [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
  lo = lo' \/ exists v, outList lo -tl- v ?? -tl> outList lo'
  \/ outList lo -tl- v !! -tl> outList lo').
Proof.
  intros H. destruct (link_ent_outList_cex l k li ln) as [S N].
  apply N. eapply H. exact S.
Qed.

(** The corrected statement (input disjunct at the output-list level) is provable.*)
Lemma link_ent_outList_fixed p p' l l' k k' li li' lo lo' ln ln' b :
  [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
  [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
  lo = lo' \/ exists v, lo -ol- v ?? -ol> lo'
  \/ outList lo -tl- v !! -tl> outList lo'.
Proof.
  intros S. inversion S; subst; try (left; reflexivity).
  - right. match goal with [V : _ -i- chanOutProc {? _ -i> _ |- _] =>
      inversion V; subst end. eexists. left. eassumption.
  - match goal with [V : _ -i- chanInProc {! _ -i> _ |- _] =>
      inversion V; subst end. left; reflexivity.
  - match goal with [V : _ -i- chanAN {! _ -i> _ |- _] =>
      inversion V; subst end. left; reflexivity.
  - match goal with [V : _ -i- chanIOEnv {? _ -i> _ |- _] =>
      inversion V; subst end. left; reflexivity.
  - right. match goal with [V : _ -i- chanIOEnv _! _ !_ _ -i> _ |- _] =>
      inversion V; subst end.
    match goal with [V : _ -ol- _ !! -ol> _ |- _] => inversion V; subst end.
    eexists. right. eassumption.
Qed.

(** The matching fix for the user's support lemma outList_in_input_pres
(InterfaceLanguage.v), restated at the output-list level, is provable.*)
Lemma link_ent_outList_input_pres_fixed v u t lo lo' :
  <( v, t )> _: outList lo -> lo -ol- u ?? -ol> lo' ->
  <( v, t )> _: outList lo'.
Proof.
  intros I S. inversion S; subst.
  - simpl. right. exact I.
  - match goal with [V : _ -tl- _ ?? -tl> _ |- _] => inversion V end.
Qed.


(* ===== end of copied helpers ===== *)

Lemma audit_link_ent_outList_Mode_False : Mode -> False.
Proof.
  intro m. apply (link_ent_outList_false (mkPosition 0%R 0%R) (sing m)
    (mkInputList nil) (mkNotifList nil)).
  exact link_ent_outList.
Qed.

Print Assumptions link_ent_outList_false.
Print Assumptions audit_link_ent_outList_Mode_False.
Print Assumptions link_ent_outList_fixed.
Print Assumptions link_ent_outList_input_pres_fixed.
