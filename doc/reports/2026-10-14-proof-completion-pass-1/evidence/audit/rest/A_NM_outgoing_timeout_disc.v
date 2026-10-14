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

From Stdlib Require Import Lra.

(* Inversion helper: what a [delivered] judgement says about the last step of
   the reachability witness. *)
Lemma outgoing_timeout_disc_cex_inv msg t j n (q : reachableNet n) :
  delivered msg t j n q ->
  match q with
  | reachNetInit _ _ => False
  | reachNetDisc _ _ a q' _ => a = anOut msg j \/ delivered msg t j _ q'
  | reachNetDel _ _ _ _ _ => True
  end.
Proof. intros H; destruct H; [left; reflexivity | right; assumption | exact I]. Qed.

(* Counterexample: the statement, with [l] universally quantified, is false
   as soon as there is any mode at all. *)
Lemma outgoing_timeout_disc_cex (m0 : Mode) :
  ~ (forall (n n' : Network) (a : ActDiscNet) (i : nat)
       (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) (l : Position),
       outgoing v zeroTime i n ->
       outgoing v zeroTime i n' \/
       exists r, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w)).
Proof.
  intro STMT.
  set (l0 := mkPosition 0 0). set (l1 := mkPosition 1 0).
  set (r := distFun l0 l0).
  set (k := sing (failSafeSucc m0)).
  set (h0 := mkInterface (mkInputList []) (mkOutputList [<([], zeroTime)>]) (mkNotifList [])).
  set (h1 := mkInterface (mkInputList []) (mkOutputList [])
               (mkNotifList [<((baseDistance r) :: [], adaptNotif)>])).
  set (e0 := [|procProtocol, l0, h0, k|]).
  set (e1 := [|procProtocol, l0, h1, k|]).
  assert (I0 : initialNet [e0]).
  { constructor; [ | constructor]. constructor. constructor. apply failSafeSuccFS. }
  set (p := reachNetInit [e0] I0).
  assert (w : [e0] -NA- anOut ([-[], l0, r-]) 0 -NA> [e1]).
  { apply stepDnOutHead.
    - apply stepDeOut. apply stepIntFwdOut.
      + apply stepOlLift. apply stepTlFwdHd.
      + apply stepNlBuff.
    - apply stepDnAccIg. apply stepDnEmpIg. }
  assert (OG : outgoing [] zeroTime 0 [e0]).
  { econstructor. constructor. simpl. left. reflexivity. }
  destruct (STMT [e0] [e1] _ 0%nat p w [] l1 OG) as [OG' | [r' DL]].
  - inversion OG' as [p' l' li' lo' ln' k' IN INL].
    assert (E : [|p', l', mkInterface li' lo' ln', k'|] = e1)
      by (eapply entInNetUnique; [exact IN | constructor]).
    unfold e1, h1 in E. inversion E; subst. simpl in INL. exact INL.
  - apply outgoing_timeout_disc_cex_inv in DL. simpl in DL.
    destruct DL as [EQ | DL].
    + inversion EQ. lra.
    + apply outgoing_timeout_disc_cex_inv in DL. simpl in DL. exact DL.
Qed.


(* ---------- Proof of the corrected statement(s) ---------- *)

Lemma outgoing_timeout_disc_tl_out (l l' : TimedList) u x :
  l -tl- u !! -tl> l' -> In x l -> x = <(u, zeroTime)> \/ In x l'.
Proof.
  intros H. remember (u !!) as b. revert Heqb.
  induction H; intros Hb IN; try discriminate.
  - inversion Hb; subst. destruct IN as [<- | IN]; [left; reflexivity | right; exact IN].
  - destruct IN as [<- | IN]; [right; left; reflexivity | ].
    destruct (IHstepTimedList Hb IN) as [EQ | IN']; [left; exact EQ | right; right; exact IN'].
Qed.

Lemma outgoing_timeout_disc_ent_out e m e' x :
  e -EA- aeTagOut m ->> e' -> In x (outList (lo (interEnt e))) ->
  msgPos m = posEnt e /\ (x = <(msgPayload m, zeroTime)> \/ In x (outList (lo (interEnt e')))).
Proof.
  intros H IN. inversion H; subst. simpl in *. split; [reflexivity | ].
  match goal with Hi : _ -i- _ -i> _ |- _ => inversion Hi; subst end. simpl in *.
  match goal with Ho : _ -ol- _ -ol> _ |- _ => inversion Ho; subst end. simpl in *.
  eapply outgoing_timeout_disc_tl_out; eassumption.
Qed.

Lemma outgoing_timeout_disc_ent_nonout e a' e' x :
  e -EA- a' ->> e' -> (forall m, a' <> aeTagOut m) ->
  In x (outList (lo (interEnt e))) -> In x (outList (lo (interEnt e'))).
Proof.
  intros H; destruct H; intros NO IN; simpl in *; try assumption;
  try (exfalso; eapply NO; reflexivity);
  match goal with Hi : _ -i- _ -i> _ |- _ => inversion Hi; subst end; simpl in *; try assumption.
  match goal with Ho : _ -ol- _ -ol> _ |- _ => inversion Ho; subst end; simpl in *;
  first [ right; assumption
        | match goal with Ht : _ -tl- _ -tl> _ |- _ => inversion Ht end ].
Qed.

Lemma outgoing_timeout_disc_mk e v t i n :
  e @ i .: n -> In (<(v, t)>) (outList (lo (interEnt e))) -> outgoing v t i n.
Proof.
  destruct e as [q l h k]; destruct h as [li0 lo0 ln0]; simpl; intros; econstructor; eassumption.
Qed.

Lemma outgoing_timeout_disc_fwd n a n' :
  n -NA- a -NA> n' -> forall e i, e @ i .: n -> exists e', e' @ i .: n'.
Proof.
  induction 1; intros e0 j M; try (eapply IHstepDiscNet; eassumption; fail);
  inversion M; subst; try (eexists; constructor; fail);
  try (match goal with Hm : ?x @ ?k .: ?m |- exists _, _ @ S ?k .: (_ :: ?m) =>
         exists x; constructor; exact Hm end);
  try (match goal with Hm : _ @ ?k .: _ |- exists _, _ @ S ?k .: _ =>
         destruct (IHstepDiscNet _ _ Hm) as [e1 M1]; exists e1; constructor; exact M1 end).
Qed.

(* Core: if v is outgoing with stamp 0 at entity e = entity i of n, then after any
   discrete step either v is still outgoing with stamp 0, or the step was entity i
   broadcasting v from its own position. *)
Lemma outgoing_timeout_disc_core n n' a i (w : n -NA- a -NA> n') v e :
  e @ i .: n -> In (<(v, zeroTime)>) (outList (lo (interEnt e))) ->
  outgoing v zeroTime i n' \/ exists r, a = anOut ([-v, posEnt e, r-]) i.
Proof.
  intros E0 IN0.
  destruct (outgoing_timeout_disc_fwd _ _ _ w _ _ E0) as [e' E'].
  destruct a as [m j | m | m | m | ].
  - destruct (Nat.eq_dec j i) as [EQj | NE]; [subst j | ].
    + destruct (outputMatch _ _ _ _ w) as [e1 [e1' [M1 [M1' S1]]]].
      assert (e1 = e) by (eapply entInNetUnique; eassumption). subst e1.
      destruct (outgoing_timeout_disc_ent_out _ _ _ _ S1 IN0) as [POS [EQ | IN1]].
      * right. destruct m as [v' l' r']. simpl in EQ, POS. inversion EQ; subst.
        exists r'. reflexivity.
      * left. eapply outgoing_timeout_disc_mk; eassumption.
    + destruct (outputMismatch _ _ _ _ _ _ w E' NE) as [e1 [M1 S1]].
      assert (e1 = e) by (eapply entInNetUnique; eassumption). subst e1.
      left. eapply outgoing_timeout_disc_mk; [exact E' | ].
      destruct S1 as [S1 | S1];
        (eapply outgoing_timeout_disc_ent_nonout; [exact S1 | intros mm Hm; inversion Hm | exact IN0]).
  - pose proof (stepDnAccIn _ _ _ w) as wA.
    destruct (acceptLink _ _ _ _ _ wA E') as [e1 [M1 S1]].
    assert (e1 = e) by (eapply entInNetUnique; eassumption). subst e1.
    left. eapply outgoing_timeout_disc_mk; [exact E' | ].
    destruct S1 as [S1 | S1];
      (eapply outgoing_timeout_disc_ent_nonout; [exact S1 | intros mm Hm; inversion Hm | exact IN0]).
  - pose proof (ignoreEqNet _ _ _ w) as EQ. left. rewrite <- EQ.
    eapply outgoing_timeout_disc_mk; eassumption.
  - destruct (acceptLink _ _ _ _ _ w E') as [e1 [M1 S1]].
    assert (e1 = e) by (eapply entInNetUnique; eassumption). subst e1.
    left. eapply outgoing_timeout_disc_mk; [exact E' | ].
    destruct S1 as [S1 | S1];
      (eapply outgoing_timeout_disc_ent_nonout; [exact S1 | intros mm Hm; inversion Hm | exact IN0]).
  - destruct (tauLink _ _ w) as [j [e1 [e1' [M1 [M1' [S1 OTH]]]]]].
    destruct (Nat.eq_dec j i) as [EQj | NE]; [subst j | ].
    + assert (e1 = e) by (eapply entInNetUnique; eassumption). subst e1.
      left. eapply outgoing_timeout_disc_mk; [exact M1' | ].
      eapply outgoing_timeout_disc_ent_nonout; [exact S1 | intros mm Hm; inversion Hm | exact IN0].
    + pose proof (OTH i e' NE E') as M2.
      assert (e' = e) by (eapply entInNetUnique; [exact M2 | exact E0]). subst e'.
      left. eapply outgoing_timeout_disc_mk; eassumption.
Qed.

(* Suggested fix A: the position is existentially quantified. *)
Lemma outgoing_timeout_disc_fixed (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) :
  outgoing v zeroTime i n ->
  outgoing v zeroTime i n' \/
  exists r l, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
Proof.
  intros U. inversion U as [q0 l0 li0 lo0 ln0 k0 E0 IN0].
  destruct (outgoing_timeout_disc_core _ _ _ _ w v _ E0 IN0) as [OG | [r EQ]].
  - left; exact OG.
  - right. subst a. exists r. eexists. apply deliveredBase with (t := zeroTime).
Qed.

(* Suggested fix B: keep l, but tie it to the position of entity i. *)
Lemma outgoing_timeout_disc_fixedB (n n' : Network) (a : ActDiscNet) (i : nat)
  (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) (l : Position) :
  inPosNet l i n -> outgoing v zeroTime i n ->
  outgoing v zeroTime i n' \/
  exists r, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
Proof.
  intros IP U. inversion U as [q0 l0 li0 lo0 ln0 k0 E0 IN0].
  inversion IP as [q1 h1 k1 E1].
  assert (EE : [|q1, l, h1, k1|] = [|q0, l0, {| li := li0; lo := lo0; ln := ln0 |}, k0|])
    by (eapply entInNetUnique; eassumption).
  inversion EE; subst.
  destruct (outgoing_timeout_disc_core _ _ _ _ w v _ E0 IN0) as [OG | [r EQ]].
  - left; exact OG.
  - right. subst a. exists r. apply deliveredBase with (t := zeroTime).
Qed.

(* What the only user (NARMsgPosition.sent_out_del, discrete case) needs, from fix A. *)
Lemma outgoing_timeout_disc_user_step n n' a i (p : reachableNet n) (w : n -NA- a -NA> n') v :
  (outgoing v zeroTime i n \/ exists r l, delivered ([-v, l, r-]) zeroTime i n p) ->
  outgoing v zeroTime i n' \/
  exists r l, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
Proof.
  intros [OZ | [r [l D]]].
  - exact (outgoing_timeout_disc_fixed n n' a i p w v OZ).
  - right. exists r l. apply deliveredDisc. exact D.
Qed.



Print Assumptions outgoing_timeout_disc_cex.

Print Assumptions outgoing_timeout_disc_fixed.

Print Assumptions outgoing_timeout_disc_fixedB.
