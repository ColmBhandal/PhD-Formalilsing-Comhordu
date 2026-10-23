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

(* ===== HELPERS copied verbatim from w1b-05/EntAuxResults.currComp_nextPincCheck_track_ent.v ===== *)

Require Import ComhCoq.ProcEquiv.
Ltac ccnp_varEq_tac :=
  unfold update, varEq, resetSub, inVarList, varEq;
  repeat match goal with
  | |- context [varEqDec ?a ?b] => destruct (varEqDec a b); try congruence
  end; try reflexivity.

Lemma ccnp_app_bisim n l1 q l : def n = (l1, q) ->
  bisimulation (app n l) (subProcTerm (listsToSub l1 l) q).
  intro D. constructor.
  - intros a p' S. exists p'. split; [ | apply bisim_refl].
    inversion S; subst.
    + constructor. inversion H; subst. rewrite D in H2. inversion H2; subst. assumption.
    + apply stepPTimed. inversion H; subst. rewrite D in H2. inversion H2; subst. assumption.
  - intros a q' S. exists q'. split; [ | apply bisim_refl].
    inversion S; subst.
    + constructor. econstructor; eassumption.
    + apply stepPTimed. econstructor; eassumption.
Qed.

(** Counterexample: the overlap's chanMNext output synchronises internally
with the listener's chanMNext input, so the mode state is never consulted. *)
Lemma ccnp_counterexample :
  (forall (m2 m1' m2' : Mode) (l l' : Position)
  (r r' : Distance) (p p' : ProcTerm) h h' k k' a,
  currCompStateEnt m2 r ([|p, l, h, k|]) ->
  nextPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  m2 = m2' /\ r = r' /\ nextModeMState k = Some m1') ->
  forall (m0 : Mode) (r : Distance) (l : Position) (h : Interface), False.
  intros ST m0 r l h.
  set (L := currComp (eBase (baseMode m0)) (eBase (baseDistance r))).
  set (L' := app nextPincCheckN [eBase (baseMode m0), eBase (baseMode m0), eBase (baseDistance r)]).
  set (O := outPrefix chanMNext [eBase (baseMode m0)] nilProc).
  assert (S : L -PA- inAct chanMNext [baseMode m0] -PA> L').
  { unfold L, currComp. apply stepDpChoiceR.
    match goal with |- stepDiscProc (inPrefix ?c ?vs ?P) _ _ =>
      assert (E : L' = subProcTerm (listsToSub vs (listBaselistExp [baseMode m0])) P) end.
    { unfold L'. simpl. unfold vM'. ccnp_varEq_tac. }
    rewrite E. apply stepDpIn. reflexivity. }
  assert (SO : O -PA- outAct chanMNext [baseMode m0] -PA> nilProc).
  { unfold O. apply stepDpOut. repeat constructor. }
  set (p := nilProc $||$ O $||$ L).
  set (p' := nilProc $||$ nilProc $||$ L').
  assert (SP : p -PA- tauAct -PA> p').
  { unfold p, p'. apply stepDpParR. eapply stepDpSyncLR; eassumption. }
  assert (SE : [|p, l, h, sing m0|] -EA- aeTau ->> [|p', l, h, sing m0|]).
  { apply stepDeProcTau. exact SP. }
  assert (C1 : currCompStateEnt m0 r ([|p, l, h, sing m0|])).
  { constructor. unfold p. constructor. unfold currCompState. apply bisim_refl. }
  assert (C2 : nextPincCheckStateEnt m0 m0 r ([|p', l, h, sing m0|])).
  { constructor. unfold p'. constructor. unfold nextPincCheckState, L'.
    eapply bisim_trans. apply ccnp_app_bisim. reflexivity.
    match goal with |- bisimulation ?A ?B => replace A with B; [apply bisim_refl | ] end.
    unfold nextPincCheck. simpl. unfold vM', vM'', vR. ccnp_varEq_tac. }
  destruct (ST _ _ _ _ _ _ _ _ _ _ _ _ _ _ C1 C2 SE) as [_ [_ N]].
  simpl in N. discriminate N.
Qed.
(** Hence the statement forces Mode to be empty. *)
Lemma ccnp_inconsistent :
  (forall (m2 m1' m2' : Mode) (l l' : Position)
  (r r' : Distance) (p p' : ProcTerm) h h' k k' a,
  currCompStateEnt m2 r ([|p, l, h, k|]) ->
  nextPincCheckStateEnt m1' m2' r' ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  m2 = m2' /\ r = r' /\ nextModeMState k = Some m1') -> Mode -> False.
  intros ST m0. exact (ccnp_counterexample ST m0 (mkDistance zeroNonneg) origin
    (mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []))).
Qed.

(* ===== end of copied helpers ===== *)

Lemma audit_ccnp_Mode_False : Mode -> False.
Proof. exact (ccnp_inconsistent currComp_nextPincCheck_track_ent). Qed.

Print Assumptions ccnp_counterexample.
Print Assumptions ccnp_inconsistent.
Print Assumptions audit_ccnp_Mode_False.
