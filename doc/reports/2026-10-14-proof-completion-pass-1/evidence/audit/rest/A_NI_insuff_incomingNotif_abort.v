From Stdlib Require Import Program.Equality.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.
Require Import ComhCoq.NARMisc.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.EntAuxResults.
Require Import ComhCoq.ProtAuxDefs.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.ProtAuxResults.
Require Import ComhCoq.NARInsuff.

(* ===== audit evidence ===== *)

From Stdlib Require Import Lra.

(* Counterexample witness: a (non-reachable) single-entity network whose
   process consumes the timed-out notification with a 3-ary chanAN input. *)
Lemma insuff_incomingNotif_abort_cex (m : Mode) (r : Distance) (l l0 : Position) :
  let v := [baseDistance r, baseMode m, basePosition l] in
  let k := <| m, m, zeroTime |> in
  let e := [| inPrefix chanAN [vR, vM'', vL] nilProc, l0,
     mkInterface (mkInputList []) (mkOutputList [])
       (mkNotifList [<(v, zeroTime)>]), k |] in
  let e' := [| nilProc, l0,
     mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), k |] in
  nextModeMState k = Some m /\
  (e :: []) -NA- anTau -NA> (e' :: []) /\
  incomingNetNotif v zeroTime 0 (e :: []) /\
  ~ incomingNetNotif v zeroTime 0 (e' :: []) /\
  ~ notifAbortPathNet 0 (e' :: []).
Proof.
  cbv zeta. splits.
  - reflexivity.
  - apply stepDnTauHead.
    apply stepDeNotif with (v := [baseDistance r, baseMode m, basePosition l]).
    + apply stepDpIn. reflexivity.
    + apply stepIntFwdNotif. apply stepNlLift. apply stepTlFwdHd.
  - econstructor. constructor. simpl. left. reflexivity.
  - intro H. inversion H as [p0 l1 li0 lo0 ln0 k0 EIN IN]. inversion EIN; subst.
    simpl in IN. exact IN.
  - intro H. inversion H as [e0 NA EIN]. inversion EIN; subst.
    inversion NA; subst;
    unfold rangeBadStateProt, currOKStateProt, abortOvlpStateProt in *;
    match goal with Hl : liftListen _ _ |- _ => inversion Hl end.
Qed.

(* Insufficient coverages exist for every mode (so the ~sufficient premise
   is satisfiable). *)
Lemma insuff_incomingNotif_abort_insuff_zero (m : Mode) :
  ~ sufficient m (mkDistance zeroNonneg).
Proof.
  intro H. unfold sufficient in H. simpl in H.
  assert (A1 := cond_nonneg (distance (maxMinDistComp m))).
  assert (A2 := speedMax_pos).
  assert (A3 := Rmax_l adaptNotif transMax).
  assert (A4 := adaptNotif_positive).
  assert (A5 := period_positive m).
  assert (A6 := cond_nonneg (time (trans m))).
  assert (0 < Rmax adaptNotif transMax + period m + trans m) as P by lra.
  assert (0 < speedMax * (Rmax adaptNotif transMax + period m + trans m)) as Q
    by (apply Rmult_lt_0_compat; assumption).
  lra.
Qed.

(* Refutation of the target for ANY interpretation of nextModeNet that
   contains the intended one ("lift nextModeEnt", i.e. some entity at i has
   next mode m in its mode state). *)
Lemma insuff_incomingNotif_abort_refuted
  (NM : Mode -> nat -> Network -> Prop)
  (NMdef : forall m i n e, e @ i .: n -> nextModeMState (mstEnt e) = Some m -> NM m i n)
  (m : Mode) (r : Distance) (l : Position) :
  ~sufficient m r ->
  ~ (forall (n n' : Network) (a : ActDiscNet) (i : nat),
     NM m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
     incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
     incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
     notifAbortPathNet i n').
Proof.
  intros NS H.
  pose proof (insuff_incomingNotif_abort_cex m r l l) as C. cbv zeta in C.
  destruct C as [K [ST [IN [NIN NNA]]]].
  match type of ST with (?e :: []) -NA- _ -NA> _ =>
    assert (NM m 0%nat (e :: [])) as NM0 by exact (NMdef m 0%nat (e :: []) e (einConsLeft e []) K) end.
  destruct (H _ _ _ _ NM0 ST NS IN) as [X | X]; [exact (NIN X) | exact (NNA X)].
Qed.



Print Assumptions insuff_incomingNotif_abort_cex.

Print Assumptions insuff_incomingNotif_abort_refuted.
