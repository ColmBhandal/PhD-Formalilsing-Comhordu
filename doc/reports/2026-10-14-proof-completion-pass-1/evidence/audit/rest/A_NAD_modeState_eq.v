From Stdlib Require Import List.
Require Import ComhCoq.Extras.LibTactics.
Require Import ComhCoq.StandardResults.
Require Import ComhCoq.ComhBasics.
Require Import ComhCoq.LanguageFoundations.
Require Import ComhCoq.SoftwareLanguage.
Require Import ComhCoq.InterfaceLanguage.
Require Import ComhCoq.ModeStateLanguage.
Require Import ComhCoq.EntityLanguage.
Require Import ComhCoq.NetworkLanguage.
Require Import ComhCoq.EntAuxDefs.
Require Import ComhCoq.NetAuxBasics.
Require Import ComhCoq.NetAuxDefs.

(* ===== audit evidence ===== *)
(* Audit reconstruction of the cloud prover's counterexample: stepDeTest changes the
   mode state of an entity whatever its process does. *)
Section ModeStateEqCex.
End ModeStateEqCex.

Lemma modeState_eq_cex_step (q : ProcTerm) (l : Position) (h : Interface) (m : Mode) :
  [ [| q, l, h, sing m |] ] -NA- anTau -NA>
  [ [| q, l, h, <| m, failSafeSucc m, modeTransTime m (failSafeSucc m) (failSafeSucc_successor m) |> |] ].
Proof.
  apply stepDnTauHead. eapply stepDeTest. apply stepMsInit.
Qed.

Lemma modeState_eq_cex_not_in (q : ProcTerm) (l : Position) (h : Interface) (m : Mode) :
  ~ mState_in_net (sing m) 0
    [ [| q, l, h, <| m, failSafeSucc m, modeTransTime m (failSafeSucc m) (failSafeSucc_successor m) |> |] ].
Proof.
  intro H. inversion H as [p0 l0 h0 E]. inversion E.
Qed.

Lemma modeState_eq_cex_in (q : ProcTerm) (l : Position) (h : Interface) (m : Mode) :
  mState_in_net (sing m) 0 [ [| q, l, h, sing m |] ].
Proof. econstructor. apply einConsLeft. Qed.

Definition modeState_eq_cex_bad := nilProc $||$ nilProc $||$ badOvlp.
Definition modeState_eq_cex_abort := nilProc $||$ nilProc $||$ abortOvlp.
Definition modeState_eq_cex_h :=
  mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []).

Lemma msgBad_modeState_eq_refuted (m : Mode) :
  ~ (forall n n' a i k, msgBadPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' ->
     mState_in_net k i n').
Proof.
  intro H. eapply (modeState_eq_cex_not_in modeState_eq_cex_bad (mkPosition 0 0) modeState_eq_cex_h m).
  eapply H; [ | apply modeState_eq_cex_in | apply modeState_eq_cex_step].
  econstructor; [ | apply einConsLeft]. apply mbpBad. constructor.
  apply ComhCoq.ProcEquiv.bisim_refl.
Qed.

Lemma notifBad_modeState_eq_refuted (m : Mode) :
  ~ (forall n n' a i k, notifBadPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' ->
     mState_in_net k i n').
Proof.
  intro H. eapply (modeState_eq_cex_not_in modeState_eq_cex_bad (mkPosition 0 0) modeState_eq_cex_h m).
  eapply H; [ | apply modeState_eq_cex_in | apply modeState_eq_cex_step].
  econstructor; [ | apply einConsLeft]. apply nbpBad. constructor.
  apply ComhCoq.ProcEquiv.bisim_refl.
Qed.

Lemma msgAbort_modeState_eq_refuted (m : Mode) :
  ~ (forall n n' a i k, msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' ->
     mState_in_net k i n').
Proof.
  intro H. eapply (modeState_eq_cex_not_in modeState_eq_cex_abort (mkPosition 0 0) modeState_eq_cex_h m).
  eapply H; [ | apply modeState_eq_cex_in | apply modeState_eq_cex_step].
  econstructor; [ | apply einConsLeft]. apply mapAbort. constructor.
  apply ComhCoq.ProcEquiv.bisim_refl.
Qed.

Lemma notifAbort_modeState_eq_refuted (m : Mode) :
  ~ (forall n n' a i k, notifAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' ->
     mState_in_net k i n').
Proof.
  intro H. eapply (modeState_eq_cex_not_in modeState_eq_cex_abort (mkPosition 0 0) modeState_eq_cex_h m).
  eapply H; [ | apply modeState_eq_cex_in | apply modeState_eq_cex_step].
  econstructor; [ | apply einConsLeft]. apply napAbort. constructor.
  apply ComhCoq.ProcEquiv.bisim_refl.
Qed.


Print Assumptions msgBad_modeState_eq_refuted.

Print Assumptions notifBad_modeState_eq_refuted.

Print Assumptions msgAbort_modeState_eq_refuted.

Print Assumptions notifAbort_modeState_eq_refuted.
