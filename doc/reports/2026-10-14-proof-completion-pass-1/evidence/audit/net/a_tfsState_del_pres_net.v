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

(* ===== helpers copied verbatim from work/w1b-12/NetAuxBasics.tfsState_del_pres_net.v ===== *)

From Stdlib Require Import Lra.
Require Import ComhCoq.ProcEquiv.

(* A delay prefix whose guard is not zero has no discrete transition. *)
Lemma tfsState_del_pres_net_nodisc (e : Exp) (Q : ProcTerm) a q :
  evalExpFunTime e <> Some zeroTime -> ~ ($< e >$ Q) -PA- a -PA> q.
Proof. intros NZ H. inversion H; subst. contradiction. Qed.

Lemma tfsState_del_pres_net_nobisim (e : Exp) (Q R : ProcTerm) :
  evalExpFunTime e <> Some zeroTime ->
  (exists a R', R -PA- a -PA> R') -> ~ (($< e >$ Q) ~p~ R).
Proof.
  intros NZ [a [R' S]] B.
  apply bisim_symm in B.
  destruct (bisim_disc_match _ _ _ _ B S) as [q' T'].
  eapply tfsState_del_pres_net_nodisc; eassumption.
Qed.

(* A pending delay prefix is in none of the five tfs states. *)
Lemma tfsState_del_pres_net_notfs (e : Exp) (Q : ProcTerm) :
  evalExpFunTime e <> Some zeroTime -> ~ tfsState ($< e >$ Q).
Proof.
  intros NZ T. destruct T as [S | m0 S | S | S | S];
  unfold tfsStartState, tfsNextState, tfsCurrState, tfsBcState,
    tfsListenState in S;
  revert S; apply tfsState_del_pres_net_nobisim; auto.
  - do 2 eexists. unfold tfsStart.
    apply stepDpIn with (l1 := [baseTime zeroTime]). reflexivity.
  - do 2 eexists. unfold tfsNext. apply stepDpChoiceR.
    apply stepDpOut. constructor.
  - do 2 eexists. unfold tfsCurr. apply stepDpChoiceR.
    apply stepDpOut. constructor.
  - do 2 eexists. unfold tfsBc. apply stepDpOut. constructor.
  - do 2 eexists. unfold tfsListen. apply stepDpChoiceR.
    apply stepDpOut. constructor.
Qed.

Lemma tfsState_del_pres_net_der (e : Exp) (Q : ProcTerm) d q :
  (forall d q, Q -PD- d -PD> q -> q = Q) ->
  ($< e >$ Q) -PD- d -PD> q -> q = Q \/ exists e', q = $< e' >$ Q.
Proof.
  intros QD H. inversion H; subst.
  - left. eapply QD; eassumption.
  - right. eexists. reflexivity.
  - right. eexists. reflexivity.
Qed.

Ltac tfsState_del_pres_net_nil :=
  match goal with H : nilProc -PA- _ -PA> _ |- _ => inversion H end.

Lemma tfsState_del_pres_net_tripA (Q : ProcTerm) (P : DiscAct -> Prop) q a q' :
  (forall a q', Q -PA- a -PA> q' -> P a) ->
  (q = Q \/ exists e', q = $< e' >$ Q) ->
  (nilProc $||$ q $||$ nilProc) -PA- a -PA> q' -> P a.
Proof.
  intros QA QF S. inversion S; subst; try tfsState_del_pres_net_nil.
  match goal with H : (q $||$ nilProc) -PA- _ -PA> _ |- _ =>
    inversion H; subst; try tfsState_del_pres_net_nil end.
  match goal with H : q -PA- _ -PA> _ |- _ => rename H into S1 end.
  destruct QF as [E | [e' E]]; subst.
  - eapply QA; eassumption.
  - inversion S1; subst. eapply QA; eassumption.
Qed.

(* Generic counterexample: an overlap component "$<r>$ Q" (r > 0) delays by
   r + d into Q, inside an otherwise inert entity. *)
Lemma tfsState_del_pres_net_cexG (m : Mode) (Q : ProcTerm) (r : nonnegreal)
  (d : Delay) :
  (forall d q, Q -PD- d -PD> q -> q = Q) ->
  (forall d, Q -PD- d -PD> Q) ->
  (forall a q', Q -PA- a -PA> q' ->
    (forall h, ~ discActEnabledInter (a^) h) /\
    ~ discActEnabledMState (a^) (sing m)) ->
  [ [| nilProc $||$ ($< liftTimeExp (mkTime r) >$ Q) $||$ nilProc, origin,
       mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ]
  -ND- ((mkTime r) +dt+ d) -ND>
  [ [| nilProc $||$ Q $||$ nilProc, addPos origin origin,
       mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ].
Proof.
  intros QD QDel QA.
  apply stepTnCons; [ | apply stepTnEmp].
  apply stepTeDel.
  - apply stepTpPar.
    + apply stepTpNil.
    + apply stepTpPar.
      * apply stepTpDelAdd; [apply QDel | reflexivity].
      * apply stepTpNil.
      * intros a S1 S2. inversion S2.
    + intros a S1 S2. inversion S1.
  - apply stepIntDel.
    + apply stepIlDel.
    + apply stepOlLift. apply stepTlDelEmp.
    + apply stepNlLift. apply stepTlDelEmp.
  - apply stepMsDelSing.
  - unfold displacement. rewrite dist2D_refl. simpl.
    apply Rmult_le_pos; [apply cond_nonneg | ].
    apply Rlt_le. pose proof (cond_nonneg r). pose proof (cond_pos (delay d)).
    simpl in *. lra.
  - intro a. split.
    + intros [q' S].
      eapply (tfsState_del_pres_net_tripA Q) in S;
        [ | exact QA | right; eexists; reflexivity].
      destruct S as [S1 S2]. split; [apply S1 | exact S2].
    + intros p'' i' k' d' _ PD _ KD [q' S].
      inversion KD; subst.
      inversion PD; subst.
      match goal with H : nilProc -PD- _ -PD> _ |- _ => inversion H; subst end.
      match goal with H : (_ $||$ nilProc) -PD- _ -PD> _ |- _ =>
        inversion H; subst end.
      match goal with H : nilProc -PD- _ -PD> _ |- _ => inversion H; subst end.
      match goal with H : ($< _ >$ Q) -PD- _ -PD> _ |- _ =>
        apply (tfsState_del_pres_net_der _ _ _ _ QD) in H; rename H into QF end.
      eapply (tfsState_del_pres_net_tripA Q) in S; [ | exact QA | exact QF].
      destruct S as [S1 S2]. split; [apply S1 | exact S2].
Qed.

Lemma tfsState_del_pres_net_r1 : 0 <= 1.
Proof. lra. Qed.

Lemma tfsState_del_pres_net_nz :
  evalExpFunTime (liftTimeExp (mkTime (mknonnegreal 1 tfsState_del_pres_net_r1)))
    <> Some zeroTime.
Proof.
  intro H. simpl in H.
  apply (f_equal (fun o => match o with Some t => nonneg (time t) | None => 0 end)) in H.
  simpl in H. lra.
Qed.

(* tfsBc only outputs on chanTrans, which neither the interface nor a stable
   mode state can input on. *)
Lemma tfsState_del_pres_net_tfsBcA (m : Mode) a q' :
  tfsBc -PA- a -PA> q' ->
  (forall h, ~ discActEnabledInter (a^) h) /\
  ~ discActEnabledMState (a^) (sing m).
Proof.
  intro S. unfold tfsBc in S. inversion S; subst.
  match goal with H : evalExpLists [] _ |- _ => inversion H; subst end.
  simpl. split.
  - intros h E. inversion E; subst.
    match goal with H : _ -i- _ -i> _ |- _ => inversion H end.
  - intro E. inversion E; subst.
    match goal with H : _ -ms- _ -ms> _ |- _ => inversion H end.
Qed.

Lemma tfsState_del_pres_net_tfsBcD d q : tfsBc -PD- d -PD> q -> q = tfsBc.
Proof. intro H. unfold tfsBc in *. inversion H; subst. reflexivity. Qed.

(* The target is refuted (for any mode m). *)
Lemma tfsState_del_pres_net_refuted (m : Mode) :
  ~ (forall (n n' : Network) (i : nat) (d : Delay),
     n -ND- d -ND> n' -> (tfsStateNet i n <-> tfsStateNet i n')).
Proof.
  intro H.
  pose proof (tfsState_del_pres_net_cexG m tfsBc
    (mknonnegreal 1 tfsState_del_pres_net_r1) (mkDelay (mkposreal 1 Rlt_0_1))
    tfsState_del_pres_net_tfsBcD
    (fun d => ltac:(unfold tfsBc; apply stepTpOut))
    (tfsState_del_pres_net_tfsBcA m)) as ND.
  destruct (H _ _ 0%nat _ ND) as [_ B].
  match type of ND with _ -ND- _ -ND> (?e' :: []) =>
    assert (tfsStateNet 0 (e' :: [])) as T' end.
  { econstructor; [ | apply einConsLeft]. econstructor. econstructor.
    apply tfsBcSt. apply bisim_refl. }
  apply B in T'. inversion T' as [e X EIN]. inversion EIN; subst.
  inversion X as [p l h k TP Hpe]; subst.
  inversion TP as [p1 p2 p3 TS Hp]; subst.
  exact (tfsState_del_pres_net_notfs _ _ tfsState_del_pres_net_nz TS).
Qed.

(* The forward direction IS provable without reachability (via
   ProtAuxResults.del_pres_tfsState); offered as a sound replacement. *)
Lemma tfsState_del_pres_net_fwd (n n' : Network) (i : nat) (d : Delay) :
  n -ND- d -ND> n' -> tfsStateNet i n -> tfsStateNet i n'.
Proof.
  intros V T. destruct T as [[p l h k] X EIN].
  inversion X as [p0 l0 h0 k0 TP E0]; subst.
  inversion TP as [p1 p2 p3 TS E1]; subst.
  revert i EIN.
  induction V as [d0 | n0 n0' e0 e0' d0 ED V IH]; intros i EIN.
  - inversion EIN.
  - inversion EIN; subst.
    + destruct e0' as [p' l' h' k'].
      apply link_ent_soft_del in ED.
      destruct (link_par_triple_delEx _ _ _ _ _ ED) as [p1' [p2' [p3' E]]]; subst.
      apply link_par_triple_del in ED. destruct ED as [_ [D2 _]].
      econstructor; [ | apply einConsLeft].
      econstructor. econstructor. eapply del_pres_tfsState; eassumption.
    + match goal with H : _ @ ?j .: n0 |- _ =>
        destruct (IH _ H) as [e2 X2 EIN2] end.
      econstructor; [exact X2 | apply einConsRight; exact EIN2].
Qed.

(* The same construction with Q := tfsCurr refutes the earlier conjecture
   tfsCurrState_del_pres_net (NetAuxBasics.v:178) as well. *)
Lemma tfsState_del_pres_net_tfsCurrA (m : Mode) a q' :
  tfsCurr -PA- a -PA> q' ->
  (forall h, ~ discActEnabledInter (a^) h) /\
  ~ discActEnabledMState (a^) (sing m).
Proof.
  intro S. unfold tfsCurr in S.
  repeat match goal with H : _ -PA- _ -PA> _ |- _ => inversion H; subst; clear H end;
  repeat match goal with H : evalExpLists [] _ |- _ => inversion H; subst; clear H end;
  repeat match goal with H : length ?l = length [] |- _ =>
    destruct l; [clear H | discriminate H] end;
  simpl; split;
  try (intros h E; inversion E; subst;
       match goal with H : _ -i- _ -i> _ |- _ => inversion H end);
  try (intro E; inversion E; subst;
       match goal with H : _ -ms- _ -ms> _ |- _ => inversion H end).
Qed.

Lemma tfsState_del_pres_net_tfsCurrD d q : tfsCurr -PD- d -PD> q -> q = tfsCurr.
Proof.
  intro H. unfold tfsCurr in *.
  repeat match goal with H : _ -PD- _ -PD> _ |- _ => inversion H; subst; clear H end.
  reflexivity.
Qed.

Lemma tfsState_del_pres_net_tfsCurrDel d : tfsCurr -PD- d -PD> tfsCurr.
Proof. unfold tfsCurr. repeat (apply stepTpSum || apply stepTpIn || apply stepTpOut). Qed.

Lemma tfsState_del_pres_net_refuted_curr (m : Mode) :
  ~ (forall (n n' : Network) (d : Delay) (i : nat),
     n -ND- d -ND> n' -> (tfsCurrStateNet i n <-> tfsCurrStateNet i n')).
Proof.
  intro H.
  pose proof (tfsState_del_pres_net_cexG m tfsCurr
    (mknonnegreal 1 tfsState_del_pres_net_r1) (mkDelay (mkposreal 1 Rlt_0_1))
    tfsState_del_pres_net_tfsCurrD tfsState_del_pres_net_tfsCurrDel
    (tfsState_del_pres_net_tfsCurrA m)) as ND.
  destruct (H _ _ _ 0%nat ND) as [_ B].
  match type of ND with _ -ND- _ -ND> (?e' :: []) =>
    assert (tfsCurrStateNet 0 (e' :: [])) as T' end.
  { econstructor; [ | apply einConsLeft]. econstructor. econstructor.
    apply bisim_refl. }
  apply B in T'. inversion T' as [e X EIN]. inversion EIN; subst.
  inversion X as [p l h k TP Hpe]; subst.
  inversion TP as [p1 p2 p3 TS Hp]; subst.
  revert TS. apply tfsState_del_pres_net_nobisim.
  - exact tfsState_del_pres_net_nz.
  - do 2 eexists. unfold tfsCurr. apply stepDpChoiceR. apply stepDpOut. constructor.
Qed.

(* ===== audit wrapper ===== *)
Definition audit_stmt : Prop := ltac:(let T := type of @ComhCoq.NetAuxBasics.tfsState_del_pres_net in exact T).
Lemma audit_tfsState_del_pres_net : audit_stmt -> Mode -> False.
Proof.
  unfold audit_stmt. intros H m.
  exact (tfsState_del_pres_net_refuted m H).
Qed.
Print Assumptions audit_tfsState_del_pres_net.
