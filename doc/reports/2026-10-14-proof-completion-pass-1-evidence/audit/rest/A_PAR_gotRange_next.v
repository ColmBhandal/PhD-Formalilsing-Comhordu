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

(* VALIDATION ONLY (explore mode): refutation of gotRange_next as stated. *)
(** With an ill-typed input value (a time instead of a mode), both guards of
currPincCheck evaluate to false, so the derivative is inert. *)
Lemma gotRange_next_inert m'' (r : Distance) t : forall a q,
  ~ (app currPincCheckN [eBase (baseTime t), eBase (baseMode m''), eBase (baseDistance r)])
    -PA- a -PA> q.
Proof.
  intros a q H. inversion H; subst.
  match goal with [E : def _ = _ |- _] => cbn in E; inversion E; subst end.
  match goal with [H' : stepDiscProc (subProcTerm _ _) _ _ |- _] =>
    cbn [listsToSub liftVarList liftExpList subProcTerm subExp subBoolExp
      listSub map liftNameProc currPincCheck] in H';
    remove_updates_hyp H'; inversion H'; subst end;
  match goal with [H' : stepDiscProc (ifThen _ _) _ _ |- _] =>
    inversion H'; subst end;
  match goal with [E : evalBoolExpFunTot _ = true |- _] =>
    cbv in E; discriminate E end.
Qed.

(** For a genuine mode m, currPincCheck m m'' r always has a discrete step. *)
Lemma gotRange_next_step (m m'' : Mode) (r : Distance) :
  exists a q, currPincCheck m m'' r -PA- a -PA> q.
Proof.
  unfold currPincCheck. destruct (possIncBool m m'' r) eqn:E.
  - do 2 eexists. apply stepDpChoiceR. apply stepDpThen.
    + eapply stepDpApp; [reflexivity | ]. cbn. apply stepDpOut. constructor.
    + unfold evalBoolExpFunTot. cbn -[possIncBool]. rewrite E. reflexivity.
  - do 2 eexists. apply stepDpChoiceL. apply stepDpThen.
    + eapply stepDpApp; [reflexivity | ]. cbn. apply stepDpChoiceL.
      apply stepDpIn with (l1 := []). reflexivity.
    + unfold evalBoolExpFunTot. cbn -[possIncBool]. rewrite E. reflexivity.
Qed.

Lemma gotRange_next_refuted :
  (forall (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (r : Distance),
   p -PA- a -PA> p' -> gotRangeState m'' r p ->
   (exists m, currPincCheckState m m'' r p')) -> Mode -> False.
Proof.
  intros S m''. set (r := mkDistance zeroNonneg).
  assert (T : gotRange m'' r -PA- inAct chanMCurr [baseTime zeroTime] -PA>
    app currPincCheckN [eBase (baseTime zeroTime), eBase (baseMode m''), eBase (baseDistance r)]).
  { unfold gotRange. match goal with |- stepDiscProc (inPrefix ?c ?vs ?P) _ ?Q =>
      replace Q with (subProcTerm (listsToSub vs (listBaselistExp [baseTime zeroTime])) P) end.
    - apply stepDpIn. reflexivity.
    - cbn [listsToSub liftVarList liftExpList subProcTerm subExp listSub map
        listBaselistExp]. remove_updates. reflexivity. }
  destruct (S _ _ _ _ _ T (bisim_refl _)) as [m B]. unfold currPincCheckState in B.
  destruct (gotRange_next_step m m'' r) as [a [q St]].
  destruct B as [_ B2]. destruct (B2 a q (stepPDisc _ _ _ St)) as [p'' [St' _]].
  inversion St'; subst. eapply gotRange_next_inert; eassumption.
Qed.



Print Assumptions gotRange_next_refuted.
