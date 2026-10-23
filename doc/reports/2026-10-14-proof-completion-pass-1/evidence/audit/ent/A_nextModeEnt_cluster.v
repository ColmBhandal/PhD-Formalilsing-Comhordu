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
(* ===== HELPERS copied verbatim from w1b-16/EntAuxResults.nextModeEnt_not_stable.v ===== *)

(* Demonstration only: the intended definition of the nextModeEnt stub
   (per the comment at EntAuxDefs.v:147). *)
Inductive nextModeEnt_not_stable_nme (m' : Mode) : Entity -> Prop :=
  | nextModeEnt_not_stable_nme_c p l h m t :
      nextModeEnt_not_stable_nme m' ([| p, l, h, <| m, m', t |> |]).

(* As stated, m2 is inferred to be a ModeState, so the statement says the
   relation is empty on every entity.  For the intended definition this is
   false whenever a Mode exists. *)
Lemma nextModeEnt_not_stable_cex :
  (forall m1 (m2 : ModeState) p l h,
     nextModeEnt_not_stable_nme m1 ([| p, l, h, m2 |]) -> False) ->
  Mode -> ProcTerm -> Position -> Interface -> False.
Proof.
  intros H m p l h. apply (H m (<| m, m, zeroTime |>) p l h). constructor.
Qed.

(* The statement as stated is equivalent to emptiness of nextModeEnt. *)
Lemma nextModeEnt_not_stable_equiv :
  (forall m1 (m2 : ModeState) p l h, nextModeEnt m1 ([| p, l, h, m2 |]) -> False) <->
  (forall m e, ~ nextModeEnt m e).
Proof.
  split.
  - intros H m e He. destruct e. eapply H; eassumption.
  - intros H m1 m2 p l h He. eapply H; eassumption.
Qed.

(* Intended statement (m2 a stable mode) is immediate for the intended definition. *)
Lemma nextModeEnt_not_stable_fixed m1 (m2 : Mode) p l h :
  nextModeEnt_not_stable_nme m1 ([| p, l, h, sing m2 |]) -> False.
Proof. intro H. inversion H. Qed.

(* ===== HELPERS copied verbatim from w1b-03/EntAuxResults.nextEq_mode.v ===== *)

(* Intended definition of the stub nextModeEnt, per the comment in EntAuxDefs.v. *)
Inductive nextEq_mode_nextModeEntI (m' : Mode) : Entity -> Prop :=
  | nextEq_mode_nmi p l h m d : nextEq_mode_nextModeEntI m' ([|p, l, h, <| m, m', d |>|]).

(* Under the intended definition, the statement is false: the hypothesis only
   constrains the software component, not the mode state. *)
Lemma nextEq_mode_cex_intended (m0 m1 m2 : Mode) (l : Position) (h : Interface) :
  (forall (m' m'' : Mode) (e : Entity),
     nextEqStateEnt m' m'' e -> nextEq_mode_nextModeEntI m' e) -> False.
Proof.
  intro H.
  specialize (H m1 m2 ([|nilProc $||$ nilProc $||$ nextEq m1 m2, l, h, sing m0|])).
  assert (N : nextEq_mode_nextModeEntI m1
             ([|nilProc $||$ nilProc $||$ nextEq m1 m2, l, h, sing m0|])).
  { apply H. constructor. constructor. unfold nextEqState. apply ProcEquiv.bisim_refl. }
  inversion N.
Qed.

(* ===== HELPERS copied verbatim from w1b-11/EntAuxResults.nextMode_ent_mState.v ===== *)

(* Demonstration only (not for splicing): two candidate definitions of the
   nextModeEnt stub, under prefixed local names, and proofs of the target
   statement for each. *)
Inductive nextMode_ent_mState_NME (m' : Mode) : Entity -> Prop :=
  | nextMode_ent_mState_nme p l h m t :
      nextMode_ent_mState_NME m' ([|p, l, h, <| m, m', t |>|]).

Lemma nextMode_ent_mState_demo1 p l h k m :
  nextMode_ent_mState_NME m ([|p, l, h, k|]) -> nextModeMState k = Some m.
Proof. intro U. inversion U; subst. reflexivity. Qed.

Definition nextMode_ent_mState_NME2 (m : Mode) (e : Entity) : Prop :=
  EntityLanguage.nextModeEnt e = Some m.

Lemma nextMode_ent_mState_demo2 p l h k m :
  nextMode_ent_mState_NME2 m ([|p, l, h, k|]) -> nextModeMState k = Some m.
Proof. intro U. exact U. Qed.

(* Both definitions also discharge the (m2 : Mode)-annotated version of nextModeEnt_not_stable. *)
Lemma nextMode_ent_mState_demo_not_stable m1 (m2 : Mode) p l h :
  nextMode_ent_mState_NME m1 ([|p, l, h, m2|]) -> False.
Proof. intro U. inversion U. Qed.

Lemma nextMode_ent_mState_demo2_not_stable m1 (m2 : Mode) p l h :
  nextMode_ent_mState_NME2 m1 ([|p, l, h, m2|]) -> False.
Proof. intro U. discriminate U. Qed.

Lemma nextMode_ent_mState_demo_equiv m e :
  nextMode_ent_mState_NME m e <-> nextMode_ent_mState_NME2 m e.
Proof.
  split.
  - intro U. inversion U; subst. reflexivity.
  - destruct e as [p l h k]. destruct k as [m0 | m0 m1 t]; intro U;
    unfold nextMode_ent_mState_NME2 in U; simpl in U; inversion U; subst.
    constructor.
Qed.

(* ===== HELPERS copied verbatim from w1b-02/EntAuxResults.tfsCurr_failSafe.v ===== *)

(* Demonstration only: the proposed definition of the nextModeEnt stub. *)
Inductive tfsCurr_failSafe_nextModeEnt (m' : Mode) : Entity -> Prop :=
  | tfsCurr_failSafe_nme p l h m t :
      tfsCurr_failSafe_nextModeEnt m' ([| p, l, h, <| m, m', t |> |]).

(* Without a reachability hypothesis the statement is false for that definition:
   a tfsCurr process paired with a stable mode state has no next mode. *)
Lemma tfsCurr_failSafe_cex :
  (forall e, tfsCurrStateEnt e -> exists m, tfsCurr_failSafe_nextModeEnt m e /\ failSafe m) ->
  Mode -> Position -> Interface -> False.
Proof.
  intros H m l h.
  destruct (H ([| nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m |])) as [m' [N _]].
  - unfold tfsCurrStateEnt, tfsCurrStateProt. constructor. constructor.
    unfold tfsCurrState. apply ProcEquiv.bisim_refl.
  - inversion N.
Qed.

(* Even with reachability: the overlap's write of the fail-safe mode on chanMNext can
   synchronise *inside the process term* with the listener's read on chanMNext
   (currOK / currComp), so the overlap reaches tfsCurr while the mode state is
   still the stable mode m (no next mode at all). *)
Lemma tfsCurr_failSafe_unfold : ProcEquiv.bisimulation (liftNameProc tfsCurrN) tfsCurr.
Proof.
  assert (E : subProcTerm (listsToSub [] []) tfsCurr = tfsCurr).
  { change (listsToSub [] []) with idSubst. apply subProc_id_eq. }
  constructor.
  - intros a p' S. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S as [a0 t' D | d t' D]; subst.
    + constructor. inversion D; subst.
      match goal with Hd : def _ = (_, _), Hs : _ -PA- _ -PA> _ |- _ =>
        cbv [def] in Hd; inversion Hd; subst; rewrite E in Hs; exact Hs end.
    + apply stepPTimed. inversion D; subst.
      match goal with Hd : def _ = (_, _), Hs : _ -PD- _ -PD> _ |- _ =>
        cbv [def] in Hd; inversion Hd; subst; rewrite E in Hs; exact Hs end.
  - intros a q' S. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion S as [a0 t' D | d t' D]; subst.
    + constructor. eapply stepDpApp. reflexivity. rewrite E. exact D.
    + apply stepPTimed. eapply stepTpApp. reflexivity. rewrite E. exact D.
Qed.

Lemma tfsCurr_failSafe_bypass (m m'' : Mode) (l : Position) (h : Interface) :
  tfsNextStateEnt m ([| nilProc $||$ tfsNext m $||$ currOK m'', l, h, sing m |]) /\
  exists q3,
    [| nilProc $||$ tfsNext m $||$ currOK m'', l, h, sing m |] -EA- aeTau ->>
    [| nilProc $||$ liftNameProc tfsCurrN $||$ q3, l, h, sing m |] /\
    tfsCurrStateEnt ([| nilProc $||$ liftNameProc tfsCurrN $||$ q3, l, h, sing m |]).
Proof.
  split.
  - unfold tfsNextStateEnt, tfsNextStateProt. constructor. constructor.
    unfold tfsNextState. apply ProcEquiv.bisim_refl.
  - eexists. split.
    + apply stepDeProcTau. apply stepDpParR. eapply stepDpSyncLR.
      * unfold tfsNext. apply stepDpChoiceL. apply stepDpOut. repeat econstructor.
      * unfold currOK. apply stepDpChoiceR. apply stepDpIn. reflexivity.
    + unfold tfsCurrStateEnt, tfsCurrStateProt. constructor. constructor.
      unfold tfsCurrState. apply tfsCurr_failSafe_unfold.
Qed.

(* ===== HELPERS copied verbatim from EntAuxResults-2/EntAuxResults.nextEq_mode.cex.v ===== *)

(** The statement of nextEq_mode contradicts the (admitted) lemma
    nextModeEnt_not_stable: an entity with a stable mode state whose listener is
    literally the term nextEq m1 m2 is in the nextEq state. *)
Lemma nextEq_mode_cex (m0 m1 m2 : Mode) (l : Position) (h : Interface) :
  (forall (m' m'' : Mode) (e : Entity), nextEqStateEnt m' m'' e -> nextModeEnt m' e) ->
  False.
Proof.
  intro H.
  apply (nextModeEnt_not_stable m1 m0 (nilProc $||$ nilProc $||$ nextEq m1 m2) l h).
  apply (H m1 m2). constructor. constructor. unfold nextEqState. apply ProcEquiv.bisim_refl.
Qed.

(* ===== Audit additions ===== *)
Definition auditPos : Position := mkPosition 0%R 0%R.
Definition auditInt : Interface := mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil).

Lemma audit_tfsCurr_ent (m : Mode) :
  tfsCurrStateEnt ([| nilProc $||$ tfsCurr $||$ nilProc, auditPos, auditInt, sing m |]).
Proof. constructor. constructor. unfold tfsCurrState. apply ProcEquiv.bisim_refl. Qed.

Lemma audit_nextEq_ent (m m1 m2 : Mode) :
  nextEqStateEnt m1 m2 ([| nilProc $||$ nilProc $||$ nextEq m1 m2, auditPos, auditInt, sing m |]).
Proof. constructor. constructor. unfold nextEqState. apply ProcEquiv.bisim_refl. Qed.

(* (a) nextModeEnt_not_stable + tfsCurr_failSafe *)
Lemma audit_nmens_vs_tfsCurr : Mode -> False.
Proof.
  intro m. destruct (tfsCurr_failSafe _ m (audit_tfsCurr_ent m)) as [m' [N _]].
  exact (nextModeEnt_not_stable _ _ _ _ _ N).
Qed.

(* (b) nextModeEnt_not_stable + nextEq_mode *)
Lemma audit_nmens_vs_nextEq : Mode -> False.
Proof.
  intro m. exact (nextModeEnt_not_stable _ _ _ _ _ (nextEq_mode _ _ _ (audit_nextEq_ent m m m))).
Qed.

(* (c) nextMode_ent_mState + tfsCurr_failSafe *)
Lemma audit_nmems_vs_tfsCurr : Mode -> False.
Proof.
  intro m. destruct (tfsCurr_failSafe _ m (audit_tfsCurr_ent m)) as [m' [N _]].
  apply nextMode_ent_mState in N. simpl in N. discriminate N.
Qed.

(* (d) nextMode_ent_mState + nextEq_mode *)
Lemma audit_nmems_vs_nextEq : Mode -> False.
Proof.
  intro m. pose proof (nextMode_ent_mState _ _ _ _ _ (nextEq_mode _ _ _ (audit_nextEq_ent m m m))) as N.
  simpl in N. discriminate N.
Qed.

(* Sanity: each lemma alone is satisfiable by some interpretation of the stub
   (shown informally): nextModeEnt := fun _ _ => False satisfies nextModeEnt_not_stable
   and nextMode_ent_mState; nextModeEnt := fun _ _ => True satisfies tfsCurr_failSafe
   (witness failSafeSucc m) and nextEq_mode. *)
Lemma audit_tfsCurr_failSafe_trueStub (e : Entity) (m : Mode) :
  tfsCurrStateEnt e -> exists m, (fun (_ : Mode) (_ : Entity) => True) m e /\ failSafe m.
Proof. intros _. exists (failSafeSucc m). split; [exact I | apply failSafeSuccFS]. Qed.

Print Assumptions nextModeEnt_not_stable_cex.
Print Assumptions nextModeEnt_not_stable_fixed.
Print Assumptions nextEq_mode_cex_intended.
Print Assumptions nextMode_ent_mState_demo1.
Print Assumptions tfsCurr_failSafe_cex.
Print Assumptions tfsCurr_failSafe_bypass.
Print Assumptions nextEq_mode_cex.
Print Assumptions audit_nmens_vs_tfsCurr.
Print Assumptions audit_nmens_vs_nextEq.
Print Assumptions audit_nmems_vs_tfsCurr.
Print Assumptions audit_nmems_vs_nextEq.
