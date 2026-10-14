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
From Stdlib Require Import Lra.

(* Audit: in the frozen semantics the hypotheses of gotMsg_gotRange_track_ent are
   jointly unsatisfiable, because the range expression built by gotMsg is an
   eSubtract, which evaluates to a baseNonneg (never a baseDistance), so the
   bPossInc guards of the resulting currPincCheck never evaluate and the listener
   is stuck, whereas gotRange m' r (r a Distance) always has a move. *)

Ltac audit_vareq :=
  repeat (unfold update, resetSub, varEq in *; simpl in *;
    match goal with
    | |- context [varEqDec ?x ?y] =>
      let E := fresh "E" in
      destruct (varEqDec x y) as [E|E];
      [ try (inversion E; fail) | try (exfalso; apply E; reflexivity) ]
    | H : context [varEqDec ?x ?y] |- _ =>
      let E := fresh "E" in
      destruct (varEqDec x y) as [E|E];
      [ try (inversion E; fail) | try (exfalso; apply E; reflexivity) ]
    end).

(* The range expression never evaluates to a Distance. *)
Lemma audit_sub_not_distance (e1 e2 : Exp) d :
  evalExpFun (eSubtract e1 e2) <> Some (baseDistance d).
Proof.
  simpl. destruct (evalExpFun e1) as [b1 | ]; [ | discriminate].
  destruct (evalExpFun e2) as [b2 | ]; [ | discriminate].
  destruct (evalBaseNonnegFun b1); [ | discriminate].
  destruct (evalBaseNonnegFun b2); discriminate.
Qed.

Lemma audit_possInc_sub_none (x y e1 e2 : Exp) :
  evalBoolExpFun (bPossInc x y (eSubtract e1 e2)) = None.
Proof.
  pose proof (audit_sub_not_distance e1 e2) as ND.
  cbn [evalBoolExpFun].
  destruct (evalExpFun (eSubtract e1 e2)) as [b | ] eqn:EE.
  - destruct b as [ | | | d | | ];
    try (exfalso; apply (ND d); reflexivity);
    destruct (evalExpFun x) as [bx | ]; try reflexivity; destruct bx; try reflexivity;
    destruct (evalExpFun y) as [b2 | ]; try reflexivity; destruct b2; reflexivity.
  - destruct (evalExpFun x) as [bx | ]; try reflexivity; destruct bx; try reflexivity;
    destruct (evalExpFun y) as [b2 | ]; try reflexivity; destruct b2; reflexivity.
Qed.

(* A currPincCheck whose range argument is an eSubtract has no discrete move. *)
Lemma audit_cpc_stuck (x y e1 e2 : Exp) a q :
  ~ (currPincCheck x y (eSubtract e1 e2) -PA- a -PA> q).
Proof.
  intro S. unfold currPincCheck in S. pose proof (audit_possInc_sub_none x y e1 e2) as N.
  inversion S; subst;
  match goal with V : stepDiscProc (ifThen _ _) _ _ |- _ => inversion V; subst end;
  match goal with V : evalBoolExpFunTot _ = true |- _ =>
    unfold evalBoolExpFunTot in V; simpl in V; simpl in N; rewrite N in V; simpl in V; discriminate V end.
Qed.


(* Two discrete steps from gotMsg reach a process with no discrete move. *)
Lemma audit_gotMsg_deriv_stuck (m : Mode) (l1 : Position) b q :
  gotMsg m l1 -PA- b -PA> q ->
  forall a Q, q -PA- a -PA> Q -> forall a2 Q2, ~ (Q -PA- a2 -PA> Q2).
Proof.
  intros S1 a Q S2 a2 Q2 S3.
  unfold gotMsg in S1. inversion S1; subst.
  match goal with LEN : length ?lv = length _ |- _ =>
    destruct lv as [ | v [ | v' lv'] ]; simpl in LEN; try discriminate end.
  simpl in S2. audit_vareq.
  inversion S2; subst.
  match goal with V : def _ = (_, _) |- _ => simpl in V; inversion V; subst end.
  simpl in *. audit_vareq.
  match goal with V : stepDiscProc (inPrefix _ _ _) _ _ |- _ => inversion V; subst end.
  match goal with LEN : length ?lv = length _ |- _ =>
    destruct lv as [ | w [ | w' lw'] ]; simpl in LEN; try discriminate end.
  simpl in S3. audit_vareq.
  inversion S3; subst.
  match goal with V : def _ = (_, _) |- _ => simpl in V; inversion V; subst end.
  simpl in *. audit_vareq.
  match goal with V : stepDiscProc _ a2 Q2 |- _ => exact (audit_cpc_stuck _ _ _ _ _ _ V) end.
Qed.

(* gotRange m' r (r a genuine Distance) can read a mode and then move again. *)
Lemma audit_gotRange_two_steps (m' : Mode) (r : Distance) :
  exists R1, gotRange m' r -PA- chanMCurr ;? [baseMode m'] -PA> R1 /\
  exists a2 R2, R1 -PA- a2 -PA> R2.
Proof.
  eexists. split.
  - unfold gotRange. apply stepDpIn. reflexivity.
  - simpl. audit_vareq.
    destruct (possIncBool m' m' r) eqn:P.
    + eexists. eexists. eapply stepDpApp; [reflexivity | ]. simpl. audit_vareq.
      apply stepDpChoiceR. apply stepDpThen.
      * eapply stepDpApp; [reflexivity | ]. simpl. unfold badOvlp. apply stepDpOut. constructor.
      * unfold evalBoolExpFunTot. simpl. rewrite P. reflexivity.
    + eexists. eexists. eapply stepDpApp; [reflexivity | ]. simpl. audit_vareq.
      apply stepDpChoiceL. apply stepDpThen.
      * eapply stepDpApp; [reflexivity | ]. simpl. audit_vareq. unfold currComp.
        apply stepDpChoiceL. apply (stepDpIn _ [] _). reflexivity.
      * unfold evalBoolExpFunTot. simpl. rewrite P. reflexivity.
Qed.

Lemma audit_gotMsg_deriv_not_gotRange (m m' : Mode) (l1 : Position) (r : Distance) b q :
  gotMsg m l1 -PA- b -PA> q -> ~ ProcEquiv.bisimulation q (gotRange m' r).
Proof.
  intros S B. destruct (audit_gotRange_two_steps m' r) as [R1 [S1 [a2 [R2 S2]]]].
  apply ProcEquiv.bisim_symm in B. destruct B as [B1 _].
  destruct (B1 _ _ (stepPDisc _ _ _ S1)) as [Q [SQ BQ]].
  inversion SQ; subst.
  destruct BQ as [C1 _].
  destruct (C1 _ _ (stepPDisc _ _ _ S2)) as [Q2 [SQ2 _]].
  inversion SQ2; subst.
  eapply audit_gotMsg_deriv_stuck; eassumption.
Qed.

Lemma audit_gotMsg_not_gotRange (m m' : Mode) (l1 : Position) (r : Distance) :
  ~ ProcEquiv.bisimulation (gotMsg m l1) (gotRange m' r).
Proof.
  intro B. destruct (audit_gotRange_two_steps m' r) as [R1 [S1 _]].
  apply ProcEquiv.bisim_symm in B. destruct B as [B1 _].
  destruct (B1 _ _ (stepPDisc _ _ _ S1)) as [Q [SQ _]].
  inversion SQ; subst.
  match goal with V : stepDiscProc (gotMsg _ _) _ _ |- _ => unfold gotMsg in V; inversion V end.
Qed.

Lemma audit_triple_listener p1 p2 p3 q1 q2 q3 a :
  (p1 $||$ p2 $||$ p3) -PA- a -PA> (q1 $||$ q2 $||$ q3) ->
  p3 = q3 \/ exists b, p3 -PA- b -PA> q3.
Proof.
  intro S. inversion S; subst;
  try (match goal with V : stepDiscProc (p2 $||$ p3) _ _ |- _ => inversion V; subst end);
  first [left; reflexivity | right; eexists; eassumption].
Qed.

Lemma audit_ent_proc p l h k p' l' h' k' a :
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] -> p = p' \/ exists b, p -PA- b -PA> p'.
Proof.
  intro S. inversion S; subst; first [left; reflexivity | right; eexists; eassumption].
Qed.

(* The target statement, verbatim, is PROVABLE (vacuously) in the frozen semantics. *)
Lemma audit_gotMsg_gotRange_track_ent_vacuous (m m' : Mode) (l l' l1 : Position)
  (r : Distance) (p p' : ProcTerm) h h' k k' a :
  gotMsgStateEnt m l1 ([|p, l, h, k|]) ->
  gotRangeStateEnt m' r ([|p', l', h', k'|]) ->
  [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
  l = l' /\ m = m' /\
  r = {| distance := dist2d l l1 -nn- speedMax *nn* msgLatency |}.
Proof.
  intros GM GR ST. exfalso.
  inversion GM as [p0 l0 h0 k0 GP]; subst.
  inversion GP as [p1 p2 p3 G3]; subst.
  inversion GR as [p0' l0' h0' k0' RP]; subst.
  inversion RP as [q1 q2 q3 R3]; subst.
  unfold gotMsgState in G3. unfold gotRangeState in R3.
  assert (NE : ~ ProcEquiv.bisimulation p3 (gotRange m' r)).
  { intro B. apply (audit_gotMsg_not_gotRange m m' l1 r).
    eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact G3 | exact B]. }
  destruct (audit_ent_proc _ _ _ _ _ _ _ _ _ ST) as [EQ | [b SP]].
  - injection EQ as E1 E2 E3. subst. exact (NE R3).
  - destruct (audit_triple_listener _ _ _ _ _ _ _ SP) as [EQ3 | [b' S3]].
    + subst. exact (NE R3).
    + destruct G3 as [G31 _].
      destruct (G31 _ _ (stepPDisc _ _ _ S3)) as [q' [SQ BQ]].
      inversion SQ; subst.
      eapply (audit_gotMsg_deriv_not_gotRange m m' l1 r); [eassumption | ].
      eapply ProcEquiv.bisim_trans; [apply ProcEquiv.bisim_symm; exact BQ | exact R3].
Qed.

Print Assumptions audit_cpc_stuck.
Print Assumptions audit_gotMsg_deriv_not_gotRange.
Print Assumptions audit_gotMsg_gotRange_track_ent_vacuous.
