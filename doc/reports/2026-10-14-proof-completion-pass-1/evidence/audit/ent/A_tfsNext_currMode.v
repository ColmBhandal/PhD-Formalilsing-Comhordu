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

(* Generic coinduction principle for bisimulation (audit helper). *)
Lemma audit_bisim_coind (R : ProcTerm -> ProcTerm -> Prop) :
  (forall p q, R p q ->
     (forall a p', p -P- a -P> p' -> exists q', q -P- a -P> q' /\ (R p' q' \/ ProcEquiv.bisimulation p' q')) /\
     (forall a q', q -P- a -P> q' -> exists p', p -P- a -P> p' /\ (R p' q' \/ ProcEquiv.bisimulation p' q'))) ->
  forall p q, R p q -> ProcEquiv.bisimulation p q.
Proof.
  intros H. cofix CIH. intros p q Rpq. destruct (H p q Rpq) as [H1 H2]. constructor.
  - intros a p' S. destruct (H1 a p' S) as [q' [S' [R' | B]]].
    + exists q'. split; [exact S' | exact (CIH _ _ R')].
    + exists q'. split; [exact S' | exact B].
  - intros a q' S. destruct (H2 a q' S) as [p' [S' [R' | B]]].
    + exists p'. split; [exact S' | exact (CIH _ _ R')].
    + exists p'. split; [exact S' | exact B].
Qed.

Ltac audit_vareq :=
  repeat (unfold varEq; simpl;
    match goal with
    | |- context [varEqDec ?x ?y] =>
      let E := fresh "E" in
      destruct (varEqDec x y) as [E|E];
      [ try (inversion E; fail) | try (exfalso; apply E; reflexivity) ]
    end).

Lemma audit_tfsNext_unfold (m : Mode) :
  subProcTerm (listsToSub [vM] [eBase (baseMode m)]) (tfsNext (eVar vM)) = tfsNext m.
Proof. unfold tfsNext. simpl. unfold update, varEq, resetSub. simpl. audit_vareq. reflexivity. Qed.

Definition audit_R (p q : ProcTerm) : Prop :=
  exists (m1 : Mode) (m2 : Mode), failSafeSucc m1 = failSafeSucc m2 /\
   ((p = tfsNext m1 /\ q = tfsNext m2) \/
    (p = app tfsNextN [eBase (baseMode m1)] /\ q = app tfsNextN [eBase (baseMode m2)])).

Lemma audit_R_sym p q : audit_R p q -> audit_R q p.
Proof.
  intros [m1 [m2 [E [[A B] | [A B]]]]]; exists m2 m1; split; [symmetry; exact E | | symmetry; exact E | ];
  [left | right]; split; assumption.
Qed.

Lemma audit_sim_tfsNext (m1 m2 : Mode) : failSafeSucc m1 = failSafeSucc m2 ->
  forall a p', tfsNext m1 -P- a -P> p' ->
  exists q', tfsNext m2 -P- a -P> q' /\ (audit_R p' q' \/ ProcEquiv.bisimulation p' q').
Proof.
  intros E a p' S. inversion S as [a0 t' D | d t' D]; subst.
  - unfold tfsNext in D. inversion D; subst.
    + match goal with V : stepDiscProc (outPrefix _ _ _) _ _ |- _ => inversion V; subst end.
      match goal with V : evalExpLists _ _ |- _ => inversion V; subst end.
      match goal with V : evalExpLists [] _ |- _ => inversion V; subst end.
      match goal with V : evalExp (eFailSafeSucc _) _ |- _ => inversion V; subst end.
      match goal with V : evalExp (eBase _) _ |- _ => inversion V; subst end.
      eexists. split.
      * apply stepPDisc. unfold tfsNext. apply stepDpChoiceL. rewrite E. apply stepDpOut.
        repeat constructor.
      * right. apply ProcEquiv.bisim_refl.
    + match goal with V : stepDiscProc (outPrefix _ _ _) _ _ |- _ => inversion V; subst end.
      match goal with V : evalExpLists _ _ |- _ => inversion V; subst end.
      eexists. split.
      * apply stepPDisc. unfold tfsNext. apply stepDpChoiceR. apply stepDpOut. constructor.
      * left. exists m1 m2. split; [exact E | right; split; reflexivity].
  - unfold tfsNext in D. inversion D; subst.
    match goal with V : stepTimedProc (outPrefix chanMNext _ _) _ _ |- _ => inversion V; subst end.
    match goal with V : stepTimedProc (outPrefix chanMStable _ _) _ _ |- _ => inversion V; subst end.
    exists (tfsNext m2). split.
    + apply stepPTimed. unfold tfsNext. apply stepTpSum; constructor.
    + left. exists m1 m2. split; [exact E | left; split; reflexivity].
Qed.

Lemma audit_sim_app (m1 m2 : Mode) : failSafeSucc m1 = failSafeSucc m2 ->
  forall a p', app tfsNextN [eBase (baseMode m1)] -P- a -P> p' ->
  exists q', app tfsNextN [eBase (baseMode m2)] -P- a -P> q' /\ (audit_R p' q' \/ ProcEquiv.bisimulation p' q').
Proof.
  intros E a p' S. inversion S as [a0 t' D | d t' D]; subst.
  - inversion D; subst.
    match goal with V : def _ = (_, _) |- _ => simpl in V; inversion V; subst end.
    match goal with V : stepDiscProc (subProcTerm _ _) _ _ |- _ => rewrite audit_tfsNext_unfold in V end.
    destruct (audit_sim_tfsNext m1 m2 E a0 p') as [q' [S' R']].
    + apply stepPDisc. assumption.
    + exists q'. split; [ | exact R'].
      inversion S'; subst. apply stepPDisc. eapply stepDpApp; [reflexivity | ].
      rewrite audit_tfsNext_unfold. assumption.
  - inversion D; subst.
    match goal with V : def _ = (_, _) |- _ => simpl in V; inversion V; subst end.
    match goal with V : stepTimedProc (subProcTerm _ _) _ _ |- _ => rewrite audit_tfsNext_unfold in V end.
    destruct (audit_sim_tfsNext m1 m2 E d p') as [q' [S' R']].
    + apply stepPTimed. assumption.
    + exists q'. split; [ | exact R'].
      inversion S'; subst. apply stepPTimed. eapply stepTpApp; [reflexivity | ].
      rewrite audit_tfsNext_unfold. assumption.
Qed.

Lemma audit_sim (p q : ProcTerm) : audit_R p q ->
  forall a p', p -P- a -P> p' ->
  exists q', q -P- a -P> q' /\ (audit_R p' q' \/ ProcEquiv.bisimulation p' q').
Proof.
  intros [m1 [m2 [E [[A B] | [A B]]]]]; subst.
  - apply audit_sim_tfsNext; assumption.
  - apply audit_sim_app; assumption.
Qed.

(* Key fact: tfsNext m1 and tfsNext m2 are bisimilar whenever m1, m2 share a fail-safe successor. *)
Lemma audit_tfsNext_bisim (m1 m2 : Mode) :
  failSafeSucc m1 = failSafeSucc m2 -> ProcEquiv.bisimulation (tfsNext m1) (tfsNext m2).
Proof.
  intro E. apply (audit_bisim_coind audit_R).
  - intros p q Rpq. split.
    + apply audit_sim. exact Rpq.
    + intros a q' S. destruct (audit_sim q p (audit_R_sym _ _ Rpq) a q' S) as [p' [S' [R' | B]]].
      * exists p'. split; [exact S' | left; apply audit_R_sym; exact R'].
      * exists p'. split; [exact S' | right; apply ProcEquiv.bisim_symm; exact B].
  - exists m1 m2. split; [exact E | left; split; reflexivity].
Qed.

(* Refutation in any model with two distinct modes sharing a fail-safe successor,
   given one reachable entity whose overlap is literally in tfsNext m1 with current
   mode m1 (the protocol's normal fail-safe path). *)
Lemma audit_tfsNext_currMode_cex (m1 m2 : Mode) (e : Entity) :
  (forall e m, reachableEnt e -> tfsNextStateEnt m e -> currModeEnt e = m) ->
  m1 <> m2 -> failSafeSucc m1 = failSafeSucc m2 ->
  reachableEnt e -> tfsNextStateEnt m1 e -> currModeEnt e = m1 -> False.
Proof.
  intros H NE E R T C.
  assert (T2 : tfsNextStateEnt m2 e).
  { inversion T as [p l h k TP]; subst. constructor.
    inversion TP as [p1 p2 p3 X]; subst. constructor.
    unfold tfsNextState in *. eapply ProcEquiv.bisim_trans; [exact X | ].
    apply audit_tfsNext_bisim. exact E. }
  apply NE. rewrite <- C. apply (H e m2 R T2).
Qed.

(* Same with the unconditional entity: no reachability needed to show the
   parameter is not determined by the state predicate. *)
Lemma audit_tfsNext_param_undetermined (m1 m2 : Mode) (l : Position) (h : Interface) :
  failSafeSucc m1 = failSafeSucc m2 ->
  tfsNextStateEnt m2 ([| nilProc $||$ tfsNext m1 $||$ nilProc, l, h, sing m1 |]).
Proof.
  intro E. constructor. constructor. unfold tfsNextState.
  apply audit_tfsNext_bisim. exact E.
Qed.

Print Assumptions audit_tfsNext_bisim.
Print Assumptions audit_tfsNext_currMode_cex.
Print Assumptions audit_tfsNext_param_undetermined.
