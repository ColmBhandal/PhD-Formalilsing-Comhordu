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
(* ===== HELPERS copied verbatim from w1b-11/EntAuxResults.reachable_ent_prot.v ===== *)

(* Demonstration only: the proposed definition of the reachableEnt stub, under a
   prefixed local name, and a proof of the target statement for it. *)
Inductive reachable_ent_prot_reachableEnt : Entity -> Prop :=
  | reachable_ent_prot_rInit e : initialEnt e -> reachable_ent_prot_reachableEnt e
  | reachable_ent_prot_rDisc e e' a : reachable_ent_prot_reachableEnt e ->
      e -EA- a ->> e' -> reachable_ent_prot_reachableEnt e'
  | reachable_ent_prot_rDel e e' d : reachable_ent_prot_reachableEnt e ->
      e -ED- d ->> e' -> reachable_ent_prot_reachableEnt e'.

Lemma reachable_ent_prot_demo_aux e :
  reachable_ent_prot_reachableEnt e -> reachableProt (procEnt e).
Proof.
  induction 1 as [e I | e e' a R IH S | e e' d R IH S].
  - inversion I as [p l h k IP FS]; subst. inversion IP; subst. simpl. constructor.
  - inversion S; subst; simpl in *; try assumption; eapply reachprDisc; eassumption.
  - inversion S; subst; simpl in *. eapply reachprDel; eassumption.
Qed.

Lemma reachable_ent_prot_demo p l h k :
  reachable_ent_prot_reachableEnt ([| p, l, h, k |]) -> reachableProt p.
Proof. intro R. apply (reachable_ent_prot_demo_aux _ R). Qed.

(* ===== HELPERS copied verbatim from w1b-09/EntAuxResults.ovAbort_unstable.v ===== *)

(* Counter-model witness: with reachableEnt read as fun _ => True, the
   statement fails for any entity whose overlap component is ovAbort and whose
   mode state is stable. *)
Lemma ovAbort_unstable_cm (m : Mode) (p1 p3 : ProcTerm) (l : Position) (h : Interface) :
  ovAbortStateEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |]) /\
  ~ unstable (mstEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |])).
Proof.
  split.
  - unfold ovAbortStateEnt, ovAbortStateProt. constructor. constructor.
    unfold ovAbortState. apply ComhCoq.ProcEquiv.bisim_refl.
  - simpl. intro U. inversion U.
Qed.

(* ===== Audit additions: counter-models of the opaque stubs (each target alone is
   not provable while the stub is a Parameter). These are interpretations, shown
   as statements about candidate predicates. ===== *)

(* bcReady_pos / ovReady_pos fail for inPosEnt := fun _ _ => False, reachableEnt := fun _ => True,
   because bcReady/ovReady entities exist. *)
Lemma audit_bcReady_inhabited (m : Mode) (l : Position) (h : Interface) :
  bcReadyStateEnt m l ([| bcReady m l $||$ nilProc $||$ nilProc, l, h, sing m |]).
Proof. constructor. constructor. unfold bcReadyState. apply ProcEquiv.bisim_refl. Qed.

Lemma audit_ovReady_inhabited (m : Mode) (t : Time) (l : Position) (h : Interface) :
  ovReadyStateEnt m t l ([| nilProc $||$ ovReady m t l $||$ nilProc, l, h, sing m |]).
Proof. constructor. constructor. unfold ovReadyState. apply ProcEquiv.bisim_refl. Qed.

Print Assumptions reachable_ent_prot_demo.
Print Assumptions ovAbort_unstable_cm.
Print Assumptions audit_bcReady_inhabited.
Print Assumptions audit_ovReady_inhabited.
