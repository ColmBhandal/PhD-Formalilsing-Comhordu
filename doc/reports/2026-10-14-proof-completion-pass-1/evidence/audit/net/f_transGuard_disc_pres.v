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

(* ===== helpers copied verbatim from work/NetAuxBasics-5/NetAuxBasics.transGuard_disc_pres.v ===== *)

(* Refutation: the conjecture implies that Mode is empty. *)
Lemma transGuard_disc_pres_refute :
  (forall (n n' : Network) (a : ActDiscNet) (t : Time) (i : nat),
    n -NA- a -NA> n' -> transGuard t i n -> transGuard t i n') ->
  Mode -> False.
Proof.
  intros TDP m.
  assert (ST : [ [| outPrefix chanMCurr [] nilProc, origin,
                    mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []),
                    <| m, m, zeroTime |> |] ] -NA- anTau -NA>
               [ [| nilProc, origin,
                    mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []),
                    sing m |] ]).
  { apply stepDnTauHead.
    apply (stepDeCurrWrite _ _ _ _ _ _ m).
    - apply stepDpOut. constructor.
    - apply stepMsSwitch. }
  assert (TG : transGuard zeroTime 0 [ [| outPrefix chanMCurr [] nilProc, origin,
                    mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []),
                    <| m, m, zeroTime |> |] ]).
  { econstructor. apply einConsLeft. }
  pose proof (TDP _ _ _ _ _ ST TG) as TG'.
  destruct TG' as [p l h m1 m2 E]. inversion E.
Qed.

(* Corrected statement (extra hypothesis 0 < t) is provable. *)
Lemma transGuard_disc_pres_fixed : forall (n n' : Network)
  (a : ActDiscNet) (t : Time) (i : nat),
  n -NA- a -NA> n' -> 0 < t -> transGuard t i n -> transGuard t i n'.
Proof.
  intros n n' a t i ST POS TG. destruct TG as [p l h m m' E].
  destruct (link_net_ent_disc_fwd n n' _ i a ST E) as [e' [E' [EQ | [a' STE]]]].
  - subst e'. econstructor. exact E'.
  - inversion STE; subst;
    try (econstructor; exact E');
    try match goal with
        | K : <| _, _, _ |> -ms- _ -ms> _ |- _ =>
            inversion K; subst;
            first [ econstructor; exact E'
                  | simpl in POS; lra ]
        end.
Qed.
(* ===== audit wrapper ===== *)
Print Assumptions transGuard_disc_pres_fixed.
