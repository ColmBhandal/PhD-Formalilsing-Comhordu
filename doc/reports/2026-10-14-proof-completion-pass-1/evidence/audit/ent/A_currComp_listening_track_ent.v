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

(* ===== HELPERS copied verbatim from w1b-01/EntAuxResults.currComp_listening_track_ent.v ===== *)

From Stdlib Require Import Lra.

(** An application process is bisimilar to its unfolded body.*)
Lemma currComp_listening_track_ent_app_bisim n l2 :
  ProcEquiv.bisimulation (app n l2)
    (subProcTerm (listsToSub (fst (def n)) l2) (snd (def n))).
Proof.
  destruct (def n) as [l1 b] eqn:D. simpl. constructor.
  - intros a p' H. exists p'. split; [ | apply ProcEquiv.bisim_refl].
    inversion H; subst.
    + apply stepPDisc.
      match goal with [V : app n l2 -PA- _ -PA> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
    + apply stepPTimed.
      match goal with [V : app n l2 -PD- _ -PD> _ |- _] => inversion V; subst end.
      match goal with [V : def n = (_, _) |- _] => rewrite D in V; inversion V; subst end.
      assumption.
  - intros a q' H. exists q'. split; [ | apply ProcEquiv.bisim_refl].
    inversion H; subst.
    + apply stepPDisc. eapply stepDpApp; eassumption.
    + apply stepPTimed. eapply stepTpApp; eassumption.
Qed.

Lemma currComp_listening_track_ent_listeningN : listeningState listeningN.
Proof.
  unfold listeningState.
  eapply ProcEquiv.bisim_trans; [apply currComp_listening_track_ent_app_bisim | ].
  change (ProcEquiv.bisimulation (subProcTerm idSubst listening) listening).
  rewrite subProc_id_eq. apply ProcEquiv.bisim_refl.
Qed.

(** Counterexample 1 (no reachability, overlap/listener synchronisation):
the "overlap" component outputs on chanMStable (as tfsNext and ovAbort do in the
protocol), the listener in currComp inputs it and moves to listening; this is a
process-level tau, so the entity takes stepDeProcTau and the (transitional) mode
state is unchanged, hence it cannot output on chanMStable.*)
Lemma currComp_listening_track_ent_cex1 (m m'' : Mode) (r : Distance)
  (l : Position) (h : Interface) :
  currCompStateEnt m'' r
    ([|nilProc $||$ (chanMStable ! nilProc) $||$ currComp m'' r, l, h, <|m, m, zeroTime|>|]) /\
  listeningStateEnt ([|nilProc $||$ nilProc $||$ listeningN, l, h, <|m, m, zeroTime|>|]) /\
  [|nilProc $||$ (chanMStable ! nilProc) $||$ currComp m'' r, l, h, <|m, m, zeroTime|>|]
    -EA- aeTau ->> [|nilProc $||$ nilProc $||$ listeningN, l, h, <|m, m, zeroTime|>|] /\
  ~ ((<|m, m, zeroTime|>) -ms- chanMStable @! -ms> (<|m, m, zeroTime|>)).
Proof.
  splits.
  - constructor. constructor. apply ProcEquiv.bisim_refl.
  - constructor. constructor. apply currComp_listening_track_ent_listeningN.
  - apply stepDeProcTau. apply stepDpParR.
    apply stepDpSyncLR with (c := chanMStable) (l := []).
    + apply stepDpOut. constructor.
    + unfold currComp. apply stepDpChoiceL.
      exact (stepDpIn chanMStable [] [] listeningN eq_refl).
  - intro S. inversion S.
Qed.

(** Counterexample 2 (natural protocol behaviour, survives reachability): the
mode state is transitional with next mode m', the listener in currComp reads m'
on chanMNext and, since m' is not possibly incompatible, nextPincCheck takes its
listening branch, which is bisimilar to listening.*)
Lemma currComp_listening_track_ent_cex2 (m m' m'' : Mode) (t : Time) (r : Distance)
  (l : Position) (h : Interface) :
  ~ possiblyIncompatible m' m'' r ->
  exists p',
  [|nilProc $||$ nilProc $||$ currComp m'' r, l, h, <|m, m', t|>|]
    -EA- aeTau ->> [|p', l, h, <|m, m', t|>|] /\
  currCompStateEnt m'' r ([|nilProc $||$ nilProc $||$ currComp m'' r, l, h, <|m, m', t|>|]) /\
  listeningStateEnt ([|p', l, h, <|m, m', t|>|]) /\
  ~ ((<|m, m', t|>) -ms- chanMStable @! -ms> (<|m, m', t|>)).
Proof.
  intro NPI.
  assert (PB : possIncBool m' m'' r = false).
  { unfold possIncBool. destruct (possIncDec m' m'' r); [contradiction | reflexivity]. }
  eexists. splits.
  - eapply stepDeNextRead with (m := m').
    + apply stepDpParR. apply stepDpParR. unfold currComp. apply stepDpChoiceR.
      apply stepDpIn. reflexivity.
    + apply stepMsOutNext.
  - constructor. constructor. apply ProcEquiv.bisim_refl.
  - constructor. constructor. unfold listeningState. clean_proc.
    eapply ProcEquiv.bisim_trans; [apply currComp_listening_track_ent_app_bisim | ].
    clean_proc.
    eapply ProcEquiv.bisim_trans.
    { apply ProcEquiv.choice_bisim_context.
      - apply ProcEquiv.cond_bisim_true.
        replace true with (negb (possIncBool m' m'' r)) by (rewrite PB; reflexivity).
        apply bevalNot. apply bevalPossInc; constructor.
      - apply ProcEquiv.cond_bisim_false.
        unfold evalBoolExpFunTot. simpl. exact PB. }
    eapply ProcEquiv.bisim_trans; [apply ProcEquiv.choice_bism_unit_r | ].
    apply currComp_listening_track_ent_listeningN.
  - intro S. inversion S.
Qed.

(** possIncDist is a legal distance, so counterexample 2 is realisable.*)
Lemma currComp_listening_track_ent_possIncDist_nonneg m' m'' :
  0 <= possIncDist m' m''.
Proof.
  unfold possIncDist.
  pose proof (cond_nonneg (distance (minDistComp m' m''))).
  pose proof (cond_nonneg speedMax).
  pose proof (cond_nonneg (time adaptNotif)).
  pose proof (Rmax_l adaptNotif transMax).
  pose proof (cond_nonneg (time (period m''))).
  pose proof (cond_nonneg (time (trans m''))).
  apply Rplus_le_le_0_compat; [lra | ].
  apply Rmult_le_pos; [lra | lra].
Qed.

(** The statement as given is refutable whenever Mode is inhabited (and
Position/Interface are, which they are).*)
Lemma currComp_listening_track_ent_refuted (m : Mode) (r : Distance)
  (l : Position) (h : Interface) :
  ~ (forall m'' r l l' p p' h h' k k' a,
     currCompStateEnt m'' r ([|p, l, h, k|]) ->
     listeningStateEnt ([|p', l', h', k'|]) ->
     [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
     k -ms- chanMStable @! -ms> k' /\ h = h').
Proof.
  intro STMT. destruct (currComp_listening_track_ent_cex1 m m r l h) as [A [B [C D]]].
  apply D. exact (proj1 (STMT _ _ _ _ _ _ _ _ _ _ _ A B C)).
Qed.

(** Refutation via counterexample 2, with r := possIncDist m m.*)
Lemma currComp_listening_track_ent_refuted2 (m : Mode) (t : Time)
  (l : Position) (h : Interface) :
  ~ (forall m'' r l l' p p' h h' k k' a,
     currCompStateEnt m'' r ([|p, l, h, k|]) ->
     listeningStateEnt ([|p', l', h', k'|]) ->
     [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
     k -ms- chanMStable @! -ms> k' /\ h = h').
Proof.
  intro STMT.
  set (r := mkDistance (mknonnegreal (possIncDist m m)
    (currComp_listening_track_ent_possIncDist_nonneg m m))).
  assert (NPI : ~ possiblyIncompatible m m r).
  { unfold possiblyIncompatible. simpl. apply Rlt_irrefl. }
  destruct (currComp_listening_track_ent_cex2 m m m t r l h NPI) as [p' [C [A [B D]]]].
  apply D. exact (proj1 (STMT _ _ _ _ _ _ _ _ _ _ _ A B C)).
Qed.

Print Assumptions currComp_listening_track_ent_refuted.
Print Assumptions currComp_listening_track_ent_refuted2.

(* ===== end of copied helpers ===== *)

Lemma audit_currComp_listening_track_ent_Mode_False : Mode -> False.
Proof.
  intro m.
  apply (currComp_listening_track_ent_refuted m (mkDistance zeroNonneg) (mkPosition 0%R 0%R)
    (mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil))).
  exact currComp_listening_track_ent.
Qed.

Lemma audit_currComp_listening_track_ent_Mode_False2 : Mode -> False.
Proof.
  intro m.
  apply (currComp_listening_track_ent_refuted2 m zeroTime (mkPosition 0%R 0%R)
    (mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil))).
  exact currComp_listening_track_ent.
Qed.

Print Assumptions currComp_listening_track_ent_refuted.
Print Assumptions currComp_listening_track_ent_refuted2.
Print Assumptions audit_currComp_listening_track_ent_Mode_False.
Print Assumptions audit_currComp_listening_track_ent_Mode_False2.
