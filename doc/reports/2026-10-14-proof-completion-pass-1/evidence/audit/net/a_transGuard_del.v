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

(* ===== helpers copied verbatim from work/NetAuxBasics-5/NetAuxBasics.transGuard_del.v ===== *)

(* Refutation: the conjecture implies that Mode is empty. *)
Lemma transGuard_del_refute :
  (forall (n n' : Network) (d : Delay) (t : Time) (i : nat),
    n -ND- d -ND> n' -> transGuard t i n ->
    exists p, transGuard (minusTime t d p) i n') ->
  Mode -> False.
Proof.
  intros TD m.
  assert (ED : [| nilProc, origin,
                  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []),
                  <| m, m, zeroTime |> |] -ED- mkDelay (mkposreal 1 Rlt_0_1) ->>
               [| nilProc, addPos origin origin,
                  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []),
                  <| m, m, zeroTime |> |]).
  { apply stepTeDel.
    - apply stepTpNil.
    - apply stepIntDel; [apply stepIlDel | apply stepOlLift; apply stepTlDelEmp
                        | apply stepNlLift; apply stepTlDelEmp].
    - apply stepMsDelTout.
    - unfold displacement, dist2d. cbn [nonneg xCoord yCoord origin delay pos].
      rewrite distance_refl. pose proof speedMax_nonneg. lra.
    - unfold noSync. intro a. split.
      + intro DAE. destruct DAE as [p'' STP]. inversion STP.
      + intros p' i' k' d' LT PD ID KD. inversion PD; subst.
        intro DAE. destruct DAE as [p'' STP]. inversion STP. }
  assert (EX : exists n n', (n -ND- mkDelay (mkposreal 1 Rlt_0_1) -ND> n') /\ transGuard zeroTime 0 n).
  { eexists; eexists; split.
    - apply stepTnCons; [exact ED | apply stepTnEmp].
    - econstructor. apply einConsLeft. }
  destruct EX as [n [n' [ND TG]]].
  destruct (TD _ _ _ _ _ ND TG) as [P _]. simpl in P. lra.
Qed.

(* A corrected (weakened) statement that holds for arbitrary networks. *)
Lemma transGuard_del_weak : forall (n n' : Network) (d : Delay) (t : Time) (i : nat),
  n -ND- d -ND> n' -> transGuard t i n ->
  exists t', transGuard t' i n' /\ ((t' = zeroTime /\ t < d) \/ t = t' +dt+ d).
Proof.
  intros n n' d t i ND TG. destruct TG as [p l h m m' E].
  destruct (link_net_ent_del_fwd n n' _ i d ND E) as [e' [E' D]].
  inversion D; subst.
  match goal with K : <| _, _, _ |> -ms- _ -ms> ?k' |- _ =>
    destruct (delMStatePresTrans _ _ _ _ _ K) as [t' Ek]; subst k';
    exists t'; split; [econstructor; exact E' | apply (delMStateTrans _ _ _ _ _ _ _ K)] end.
Qed.
(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.transGuard_del in exact T).
Lemma audit_transGuard_del : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m. exact (transGuard_del_refute H m).
Qed.
Print Assumptions audit_transGuard_del.
Print Assumptions transGuard_del_refute.
