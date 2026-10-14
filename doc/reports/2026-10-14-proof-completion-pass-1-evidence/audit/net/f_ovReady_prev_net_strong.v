From Stdlib Require Import Reals Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lra.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.NetAuxBasics.

(* ===== helpers copied verbatim from work/w1b-04/NetAuxBasics.ovReady_prev_net_strong.v ===== *)

(* Counterexample (explore only): without reachability, the overlap slot of
   entity i may hold an arbitrary term, e.g. a bare position-read prefix that
   steps (entity rule stepDePosRead) to the literal term ovReady m t l. *)
Lemma ovReady_prev_net_strong_cex (m : Mode) (t : Time) (l : Position) :
  ~ (forall n n' i a,
     ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
     ovReadyStateNet m t l i n \/
     (exists x0 y0, ovWaitStateNet m t x0 y0 i n)).
Proof.
  intro H.
  pose (q := inPrefix chanPos [vL] (ovReady m t l)).
  pose (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
  pose (e := [| nilProc $||$ q $||$ nilProc, l, h, sing m |]).
  pose (e' := [| nilProc $||$ ovReady m t l $||$ nilProc, l, h, sing m |]).
  assert (QS : q -PA- chanPos ;? [basePosition l] -PA> ovReady m t l).
  { unfold q. apply stepDpIn. reflexivity. }
  assert (ST : [e] -NA- anTau -NA> [e']).
  { apply stepDnTauHead. unfold e, e'. apply stepDePosRead.
    apply stepDpParR. apply stepDpParL. exact QS. }
  assert (R' : ovReadyStateNet m t l 0 [e']).
  { eapply lenWitness; [ | apply einConsLeft]. unfold e'.
    apply lifpe. apply lftOv. apply ComhCoq.ProcEquiv.bisim_refl. }
  destruct (H _ _ _ _ R' ST) as [A | [x0 [y0 A]]];
  destruct A as [e0 X E]; inversion E; subst;
  inversion X as [p0 l0 h0 k0 Y]; subst;
  inversion Y as [q1 q2 q3 Z]; subst.
  - (* q ~ ovReady m t l: ovReady cannot read chanPos *)
    destruct (bisim_disc_match _ _ _ _ Z QS) as [r TR].
    unfold ovReady in TR. inversion TR.
  - (* q ~ ovWait m t x0 y0: ovWait can read chanAbort, q cannot *)
    assert (AB : exists r, ovWait m t x0 y0 -PA- chanAbort *? -PA> r).
    { eexists. unfold ovWait. repeat apply stepDpChoiceL.
      apply stepDpIn. reflexivity. }
    destruct AB as [r AB].
    destruct (bisim_disc_match _ _ _ _ (ComhCoq.ProcEquiv.bisim_symm _ _ Z) AB) as [r' TR].
    unfold q in TR. inversion TR.
Qed.
(* Suggested fix (explore only): add reachableNet n. Proved relative to the
   admitted (not banned) lemmas link_net_prot_reach, reachableProt_triple,
   ovReady_prev. *)
Lemma ovReady_prev_net_strong_mid p1 p2 p3 q1 q2 q3 b :
  p1 $||$ p2 $||$ p3 -PA- b -PA> q1 $||$ q2 $||$ q3 ->
  q2 = p2 \/ exists b', p2 -PA- b' -PA> q2.
Proof.
  intro T. inversion T; clear T; subst; try (left; reflexivity);
  match goal with H : _ $||$ _ -PA- _ -PA> _ $||$ _ |- _ =>
    inversion H; clear H; subst end;
  first [left; reflexivity | right; eexists; eassumption].
Qed.

Lemma ovReady_prev_net_strong_fixed m t l n n' i a :
  reachableNet n -> ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
  ovReadyStateNet m t l i n \/ (exists x0 y0, ovWaitStateNet m t x0 y0 i n).
Proof.
  intros RN R ST.
  destruct R as [e' X E'].
  inversion X as [p' l' h' k' Y]; subst.
  inversion Y as [p1' p2' p3' Z]; subst.
  destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST E') as [e0 [E0 [EQ | [a' S]]]].
  - subst e0. left. eapply lenWitness; [ | exact E0]. apply lifpe. apply lftOv. exact Z.
  - destruct e0 as [p l0 h0 k0].
    lets RP : link_net_prot_reach RN E0.
    lets PS : reachableProt_triple RP.
    inversion PS as [p1 p2 p3 B O L]; subst.
    inversion S; subst;
    first [
      (left; eapply lenWitness; [ | exact E0]; apply lifpe; apply lftOv; exact Z)
    | (match goal with H : _ $||$ _ $||$ _ -PA- _ -PA> _ $||$ _ $||$ _ |- _ =>
         destruct (ovReady_prev_net_strong_mid _ _ _ _ _ _ _ H) as [EQ | [b' T2]];
         [ subst; left; eapply lenWitness; [ | exact E0]; apply lifpe; apply lftOv; exact Z
         | destruct (ovReady_prev _ _ _ _ _ _ T2 O Z) as [x W];
           right; exists x; exists zeroTime; eapply lenWitness; [ | exact E0];
           apply lifpe; apply lftOv; exact W ]
       end) ].
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions ovReady_prev_net_strong_fixed.
