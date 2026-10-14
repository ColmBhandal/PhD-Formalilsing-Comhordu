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

(* ===== helpers copied verbatim from work/NetAuxBasics-4/stub_validation.currModeNet_reachableEnt.v ===== *)

(* Validation only: the proposed definition of the currModeNet stub. *)
Definition currMode_pres_bkwd_cmn (m : Mode) (i : nat) (n : Network) : Prop :=
  exists e, e @ i .: n /\ currModeEnt e = m.

Lemma currMode_pres_bkwd_stub (n n' : Network) (a : ActDiscNet) (m' : Mode) (i : nat) :
  n -NA- a -NA> n' -> currMode_pres_bkwd_cmn m' i n' ->
  exists m, currMode_pres_bkwd_cmn m i n.
Proof.
  intros ST [e' [EIN _]].
  destruct (link_net_ent_disc_bkwdW n n' e' i a ST EIN) as [e EIN0].
  exists (currModeEnt e). exists e. split; [assumption | reflexivity].
Qed.

Lemma currMode_pres_fwd_stub (n n' : Network) (a : ActDiscNet) (m : Mode) (i : nat) :
  n -NA- a -NA> n' -> currMode_pres_bkwd_cmn m i n ->
  exists m', currMode_pres_bkwd_cmn m' i n'.
Proof.
  intros ST [e [EIN _]].
  destruct (link_net_ent_disc_fwd n n' e i a ST EIN) as [e' [EIN' _]].
  exists (currModeEnt e'). exists e'. split; [assumption | reflexivity].
Qed.

Lemma currMode_intro_stub : forall (m : Mode) (e : Entity) (i : nat) (n : Network),
  m = currModeEnt e -> e @ i .: n -> currMode_pres_bkwd_cmn m i n.
Proof. intros m e i n EQ EIN. exists e. split; [assumption | symmetry; assumption]. Qed.

Inductive reachable_net_ent_RE : Entity -> Prop :=
  | reachable_net_ent_RE_init e : initialEnt e -> reachable_net_ent_RE e
  | reachable_net_ent_RE_disc e e' a :
    reachable_net_ent_RE e -> e -EA- a ->> e' -> reachable_net_ent_RE e'
  | reachable_net_ent_RE_del e e' d :
    reachable_net_ent_RE e -> e -ED- d ->> e' -> reachable_net_ent_RE e'.

Lemma reachable_net_ent_stub (n : Network) (e : Entity) (i : nat) :
  reachableNet n -> e @ i .: n -> reachable_net_ent_RE e.
Proof.
  intros RN. revert e i.
  induction RN as [n0 INIT | n0 n1 a0 RN0 IH ST | n0 n1 d0 RN0 IH ST]; intros e1 i1 EIN.
  - apply reachable_net_ent_RE_init. eapply initialNet_ent; eassumption.
  - destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST EIN) as [e0 [EIN0 [EQ | [a' STE]]]].
    + subst. eapply IH; eassumption.
    + eapply reachable_net_ent_RE_disc; [eapply IH; eassumption | eassumption].
  - destruct (link_net_ent_del_bkwd _ _ _ _ _ ST EIN) as [e0 [EIN0 STE]].
    eapply reachable_net_ent_RE_del; [eapply IH; eassumption | eassumption].
Qed.

(* ===== audit wrapper ===== *)
Print Assumptions currMode_pres_bkwd_stub.
Print Assumptions currMode_pres_fwd_stub.
Print Assumptions currMode_intro_stub.
Print Assumptions reachable_net_ent_stub.
