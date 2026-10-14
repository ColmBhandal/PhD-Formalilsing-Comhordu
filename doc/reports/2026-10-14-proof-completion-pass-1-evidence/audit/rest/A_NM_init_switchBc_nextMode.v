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
Lemma init_nextMode_net_refute (m m0 : Mode) (h : Interface) :
  (forall m i n, initStateNet m i n -> nextModeNet m i n) -> False.
Proof.
  intro H.
  set (e := [| nilProc $||$ init m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
  assert (initStateNet m 0 [e]) as IS.
  { econstructor; [ | apply einConsLeft]. constructor. constructor.
    apply ComhCoq.ProcEquiv.bisim_refl. }
  apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
  inversion EIN; subst. unfold e in NM.
  apply nextMode_ent_mState in NM. simpl in NM. discriminate.
Qed.

Lemma switchBc_nextMode_net_refute (m m0 : Mode) (h : Interface) :
  (forall m i n, switchBcStateNet m i n -> nextModeNet m i n) -> False.
Proof.
  intro H.
  set (e := [| nilProc $||$ switchBc m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
  assert (switchBcStateNet m 0 [e]) as IS.
  { econstructor; [ | apply einConsLeft]. constructor. constructor.
    apply ComhCoq.ProcEquiv.bisim_refl. }
  apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
  inversion EIN; subst. unfold e in NM.
  apply nextMode_ent_mState in NM. simpl in NM. discriminate.
Qed.


Print Assumptions init_nextMode_net_refute.

Print Assumptions switchBc_nextMode_net_refute.
