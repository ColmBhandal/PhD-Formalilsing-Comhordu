(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(** Theorems about Real numbers, distances, intervals.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".
Require Import ComhCoq.Extras.LibTactics.
Require Export Reals.
Require Export Logic.ProofIrrelevance.
Require Import ComhCoq.GenTacs.

Open Scope R_scope.

(****************************** Misc ******************************)

(**Equality is decidable on the set X.*)
Definition eqDec (X : Type) := forall x1 x2 : X,
  {x1 = x2} + {x1 <> x2}.

Lemma notEq_symm : forall (X : Type) (x1 x2 : X), ~x1 = x2 -> ~x2 = x1.
  unfold not. intros. apply H. symmetry. assumption. Qed.

Lemma two_nonneg : 0 <= 2. replace 0 with (0 + 0).
  apply Rplus_le_compat;apply Rle_0_1. ring. Qed.
  
Ltac Rmult_le_zero :=
  match goal with
  | [ |- 0 <= ?y1 * ?y2] => 
    replace 0 with (0 * 0);[ | ring];
    apply Rmult_le_compat;[apply Rle_refl | apply Rle_refl | ..]
  end.

Ltac Rplus3_swap_2_3 a b c := replace (a + b + c) with (a + c + b); [ | ring].
Ltac Rminus_plus_zero a b := replace (a - b) with (a + (0 - b));[ | ring].

(** Splits the goal into 2 subgoals based on d <= t or t < d*)
Ltac Rleltcases d t U :=  let H := fresh in lets H : Rle_or_lt d t;
  let U1 := fresh U in elim_intro H U1 U1.

(****************************** Inequality ******************************)

Lemma not_Rle_lt : forall (r1 r2 : R),
  ~r1 <= r2 -> r2 < r1. intros. addHyp (Rlt_or_le r1 r2). invertClear H0.
  apply False_ind. apply H. apply Rlt_le. assumption.
  apply Rle_lt_or_eq_dec in H1. invertClear H1. assumption.
  rewrite H0 in H. apply False_ind. apply H. apply Rle_refl. Qed.

Lemma RltMinusBothSides : forall (r1 r2 : R),
  r2 < r1 -> 0 < (r1 - r2).
  intros. apply Rnot_le_lt. unfold not. intros.
  apply Rplus_le_compat_l with (r := r2) in H0. rewrite Rplus_minus in H0.
  rewrite Rplus_0_r in H0. eapply Rle_not_lt. apply H0. apply H.
  Qed.

(**** Rle ****)

Ltac Rle_trans_red := 
  match goal with
  | [H1 : ?r1 <= ?r2, H2 : ?r2 <= ?r3 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[apply H1 | apply H2]
  | [H1 : ?r1 <= ?r2 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[apply H1 | ]
  | [H2 : ?r2 <= ?r3 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[ | apply H2]
  end.

Ltac Rle_trans_rev_red := 
  match reverse goal with
  | [H1 : ?r1 <= ?r2, H2 : ?r2 <= ?r3 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[apply H1 | apply H2]
  | [H1 : ?r1 <= ?r2 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[apply H1 | ]
  | [H2 : ?r2 <= ?r3 |- ?r1 <= ?r3] =>
    eapply Rle_trans;[ | apply H2]
  end.

Ltac Rplus_le_cancel_middle :=
  match goal with
  | [ |- ?x1 + ?r + ?x2 <= ?y1 + ?r + ?y2] =>
    replace (x1 + r + x2) with (x1 + x2 + r);[ | ring];
    replace (y1 + r + y2) with (y1 + y2 + r);[ | ring];
    apply Rplus_le_compat_r
  | [ |- ?x1 + ?r <= ?y1 + ?r + ?y2] =>
    replace (y1 + r + y2) with (y1 + y2 + r);[ | ring];
    apply Rplus_le_compat_r
  end.

Ltac Rle_ring_solve := apply Req_le; simpl; ring.

Ltac Rle_refl_solve := apply Rle_refl.

Lemma Rle_plus_r : forall (x y : R),
  0 <= y -> x <= x + y. intros. apply Rle_trans with (r2 := x + 0).
  replace (x + 0) with x. apply Rle_refl. ring.
  apply Rplus_le_compat. apply Rle_refl. assumption. Qed.

Lemma Rle_plus_l : forall (x y : R),
  0 <= y -> x <= y + x. intros. rewrite Rplus_comm.
  apply Rle_plus_r. assumption. Qed.

Lemma RleMinusBothSides : forall (r1 r2 : R),
  r2 <= r1 -> 0 <= (r1 - r2). intros. apply Rle_lt_or_eq_dec in H.
  inversion H. apply RltMinusBothSides in H0. apply Rlt_le. assumption.
  rewrite H0. rewrite Rminus_diag_eq. apply Rle_refl. reflexivity. Qed.

Lemma Rmult_le_0_compat : forall r1 r2 : R,
  0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
  intros. simpl. rewrite <- (Rmult_0_r 0). apply Rmult_le_compat;
  try assumption; try apply Rle_refl. Qed.

Lemma Rle_zero_plus : forall r1 r2 : R,
  0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
  intros. rewrite <- Rplus_0_r at 1. apply Rplus_le_compat; assumption. Qed.

Lemma Rle_zero_mult : forall r1 r2 : R,
  0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2. intros. rewrite <- (Rmult_0_l r2)at 1.
  apply Rmult_le_compat_r; assumption. Qed.

Lemma RlePlusExistsR : forall (r1 r2 : R),
  r1 <= r2 -> exists r3, r2 = r1 + r3 /\ 0 <= r3. intros.
  exists (r2 - r1). split. ring. apply (Rplus_le_reg_r r1).
  replace (r2 - r1 + r1) with r2; try ring. rewrite Rplus_0_l.
  assumption. Qed.

Lemma RlePlusExistsL : forall (r1 r2 : R),
  r1 <= r2 -> exists r3, r2 = r3 + r1 /\ 0 <= r3. intros.
  apply RlePlusExistsR in H. invertClear H.
  exists x. rewrite Rplus_comm. assumption. Qed.

Lemma Rle_or_le : forall (r1 r2 : R), r1 <= r2 \/ r2 <= r1.
  intros. addHyp (Rlt_or_le r1 r2). invertClear H. left.
  apply Rlt_le. assumption. right. assumption. Qed.

Lemma Rplus_le_swap_rr : forall (x y z : R),
  x <= y + z -> x - z <= y. intros. eapply Rplus_le_reg_r.
  eapply Rle_trans;[ | apply H ].
  apply Req_le. ring. Qed.

Lemma Rplus_le_swap_rl : forall (x y z : R),
  x <= y + z -> x - y <= z. intros. rewrite Rplus_comm in H.
  apply Rplus_le_swap_rr. assumption. Qed.

Lemma Rplus_le_swap_lr : forall (x y z : R),
  x + y <= z -> x <= z - y. intros. eapply Rplus_le_reg_r.
  eapply Rle_trans. apply H. apply Req_le. ring. Qed.

Lemma Rplus_le_swap_ll : forall (x y z : R),
  x + y <= z -> y <= z - x. intros. rewrite Rplus_comm in H.
  apply Rplus_le_swap_lr. assumption. Qed.

Lemma Rminus_le_swap_rr : forall (x y z : R),
  x <= y - z -> x + z <= y. intros. eapply Rplus_le_reg_r.
  eapply Rle_trans;[ | apply H]. apply Req_le. ring. Qed.

Lemma Rminus_le_swap_lr : forall (x y z : R),
  x - y <= z -> x <= z + y. intros. eapply Rplus_le_reg_r.
  eapply Rle_trans. apply H. apply Req_le. ring. Qed.

Lemma Rplus_le_weaken_lr : forall (x y z : R), x + y <= z -> 0 <= y -> x <= z.
  intros. eapply Rle_trans;[ |apply H]. apply Rle_plus_r. assumption. Qed.

Lemma Rplus_le_weaken_ll : forall (x y z : R), x + y <= z -> 0 <= x -> y <= z.
  intros. rewrite Rplus_comm in H. eapply Rplus_le_weaken_lr. apply H. assumption.
  Qed.

Lemma Rplus_le_weaken_rr : forall (x y z : R), 0 <= z -> x <= y -> x <= y + z.
  intros. replace x with (x + 0). eapply Rplus_le_compat; assumption.
  ring. Qed.

Lemma Rplus_le_weaken_rl : forall (x y z : R), 0 <= y -> x <= z -> x <= y + z.
  intros. rewrite Rplus_comm. apply Rplus_le_weaken_rr;assumption. Qed.

Lemma Rminus_le_weaken_lr : forall (x y z : R), 0 <= y -> x <= z -> x - y <= z.
  intros. replace z with (z - 0);[ | ring]. eapply Rplus_le_compat.
  assumption. apply Ropp_le_contravar. assumption. Qed.

(** Tries to solve an inequality on real numbers.*)
Ltac Rplus_le_tac := 
  match goal with
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 <= ?r4 |- ?r1 + ?r2 <= ?r3 + ?r4] =>
    apply Rplus_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 <= ?r4 |- ?r2 + ?r1 <= ?r3 + ?r4] =>
    rewrite Rplus_comm; apply Rplus_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r2|- ?r + ?r1 <= ?r + ?r2] =>
    apply Rplus_le_compat_l;apply H1
  | [ H1 : ?r1 <= ?r2|- ?r1 + ?r <= ?r2 + ?r] =>
    apply Rplus_le_compat_r;apply H1
  | [ |- ?r + ?r1 <= ?r + ?r2] =>
    apply Rplus_le_compat_l
  | [ |- ?r1 + ?r <= ?r2 + ?r] =>
    apply Rplus_le_compat_r
  | [ H : ?r1 + ?r <= ?r2 + ?r |- ?r1 <= ?r2] =>
    apply Rplus_le_reg_l in H; assumption
  | [ H : ?r + ?r1 <= ?r + ?r2 |- ?r1 <= ?r2] =>
    apply Rplus_le_reg_r in H; assumption
  | [ H : ?x <= ?y + ?z |- ?x - ?z <= ?y] =>
    apply Rplus_le_swap_rr; assumption
  | [ H : ?x + ?y <= ?z |- ?y <= ?z - ?x] =>
    apply Rplus_le_swap_ll; assumption
  | [ H : ?x + ?y <= ?z |- ?x <= ?z - ?y] =>
    apply Rplus_le_swap_lr; assumption
  | [ H : ?x <= ?y + ?z |- ?x - ?y <= ?z] =>
    apply Rplus_le_swap_rl; assumption
  | [ |- ?r1 <= ?r1 + _] => apply Rle_plus_r
  | [ |- ?r1 <= _ + ?r1] => apply Rle_plus_l
  | [ H : ?x + ?y <= ?z |- ?x <= ?z] =>
    eapply Rplus_le_weaken_lr; apply H
  | [ H : ?x + ?y <= ?z |- ?y <= ?z] =>
    eapply Rplus_le_weaken_ll; apply H
  end.


(**** Rlt ****)

Ltac Rlt_trans_red := 
  match goal with
  | [H1 : ?r1 < ?r2, H2 : ?r2 < ?r3 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[apply H1 | apply H2]
  | [H1 : ?r1 < ?r2 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[apply H1 | ]
  | [H2 : ?r2 < ?r3 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[ | apply H2]
  end.

Ltac Rlt_trans_rev_red := 
  match reverse goal with
  | [H1 : ?r1 < ?r2, H2 : ?r2 < ?r3 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[apply H1 | apply H2]
  | [H1 : ?r1 < ?r2 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[apply H1 | ]
  | [H2 : ?r2 < ?r3 |- ?r1 < ?r3] =>
    eapply Rlt_trans;[ | apply H2]
  end.

Ltac Rplus_lt_cancel_middle :=
  match goal with
  | [ |- ?x1 + ?r + ?x2 < ?y1 + ?r + ?y2] =>
    replace (x1 + r + x2) with (x1 + x2 + r);[ | ring];
    replace (y1 + r + y2) with (y1 + y2 + r);[ | ring];
    apply Rplus_lt_compat_r
  | [ |- ?x1 + ?r < ?y1 + ?r + ?y2] =>
    replace (y1 + r + y2) with (y1 + y2 + r);[ | ring];
    apply Rplus_lt_compat_r
  end.

Lemma Rlt_plus_r : forall (x y : R),
  0 < y -> x < x + y. intros. apply Rle_lt_trans with (r2 := x + 0).
  replace (x + 0) with x. apply Rle_refl. ring.
  apply Rplus_le_lt_compat. apply Rle_refl. assumption. Qed.

Lemma Rlt_plus_l : forall (x y : R),
  0 < y -> x < y + x. intros. rewrite Rplus_comm.
  apply Rlt_plus_r. assumption. Qed.

Lemma Rlt_zero_plus : forall r1 r2 : R,
  0 < r1 -> 0 < r2 -> 0 < r1 + r2.
  intros. rewrite <- Rplus_0_r at 1. apply Rplus_lt_compat; assumption. Qed.

Lemma RltPlusExistsR : forall (r1 r2 : R),
  r1 < r2 -> exists r3, r2 = r1 + r3 /\ 0 < r3. intros.
  exists (r2 - r1). split. ring. apply (Rplus_lt_reg_r r1).
  replace (r1 + (r2 - r1)) with r2; try ring. rewrite Rplus_0_r.
  assumption. Qed.

Lemma RltPlusExistsL : forall (r1 r2 : R),
  r1 < r2 -> exists r3, r2 = r3 + r1 /\ 0 < r3. intros.
  apply RltPlusExistsR in H. invertClear H.
  exists x. rewrite Rplus_comm. assumption. Qed.

Lemma RltExistsBetween (r1 r2 : R) : r1 < r2 -> exists r3,
  r1 < r3 < r2. intros. addHyp (RltPlusExistsL r1 r2 H). invertClear H0.
  invertClear H1. exists (r1 + x/2). assert (0 < x/2). rewrite double_var in H2.
  addHyp (Rlt_or_le 0 (x/2)). invertClear H1. assumption.
  assert (x / 2 + x / 2 <= 0 + 0). apply Rplus_le_compat;
  assumption. replace (0 + 0) with 0 in H1; [|ring].
  apply False_ind. eapply Rlt_not_le. apply H2. assumption.
  assert (x / 2 < x). rewrite double_var. apply Rlt_plus_l.
  assumption. split. apply Rlt_plus_r. assumption. rewrite H0.
  rewrite Rplus_comm. apply Rplus_lt_le_compat. assumption.
  apply Rle_refl. Qed. 

Lemma Rplus_lt_swap_rl : forall (x y z : R),
  x < y + z -> x - y < z. intros. eapply Rplus_lt_compat_r in H.
  eapply Rlt_le_trans. unfold Rminus. apply H. apply Req_le.
  ring. Qed.

Lemma Rplus_lt_swap_rr : forall (x y z : R),
  x < y + z -> x - z < y. intros. rewrite Rplus_comm in H.
  apply Rplus_lt_swap_rl. assumption. Qed.

Lemma Rplus_lt_swap_ll : forall (x y z : R),
  x + y < z -> y < z - x. intros. eapply Rplus_lt_compat_r in H.
  unfold Rminus. eapply Rle_lt_trans;[| apply H]. apply Req_le.
  ring. Qed.  

Lemma Rplus_lt_swap_lr : forall (x y z : R),
  x + y < z -> x < z - y. intros. rewrite Rplus_comm in H.
  apply Rplus_lt_swap_ll. assumption. Qed.

Lemma Rminus_lt_swap_rr : forall (x y z : R),
  x < y - z -> x + z < y. intros. rewrite <- (Ropp_involutive z).
  apply Rplus_lt_swap_rr. apply H. Qed.

Lemma Rminus_lt_swap_lr : forall (x y z : R),
  x - y < z -> x < z + y. intros. rewrite <- (Ropp_involutive y).
  apply Rplus_lt_swap_lr. apply H. Qed.

Lemma Rplus_lt_reg_l: forall r r1 r2 : R, r1 + r < r2 + r -> r1 < r2.
  intros. replace r2 with (r2 + r - r);[ | ring]. apply Rplus_lt_swap_lr.
  assumption. Qed.

Lemma Rplus_lt_reg_r: forall r r1 r2 : R, r + r1 < r + r2 -> r1 < r2.
  intros. apply (Rplus_lt_reg_l r). my_applys_eq H;ring. Qed.

Lemma Rplus_lt_weaken_lr : forall (x y z : R), x + y < z -> 0 <= y -> x < z.
  intros. eapply Rle_lt_trans;[ |apply H]. apply Rle_plus_r. assumption. Qed.

Lemma Rplus_lt_weaken_ll : forall (x y z : R), x + y < z -> 0 <= x -> y < z.
  intros. rewrite Rplus_comm in H. eapply Rplus_lt_weaken_lr. apply H. assumption.
  Qed.

Lemma Rplus_lt_weaken_rr : forall (x y z : R), 0 <= z -> x < y -> x < y + z.
  intros. replace x with (x + 0). eapply Rplus_lt_le_compat; assumption.
  ring. Qed.

Lemma Rplus_lt_weaken_rl : forall (x y z : R), 0 <= y -> x < z -> x < y + z.
  intros. rewrite Rplus_comm. apply Rplus_lt_weaken_rr;assumption. Qed.

Lemma Rminus_lt_weaken_lr : forall (x y z : R), 0 <= y -> x < z -> x - y < z.
  intros. replace z with (z - 0);[ | ring]. eapply Rplus_lt_le_compat.
  assumption. apply Ropp_le_contravar. assumption. Qed.

(** Tries to solve an inequality on real numbers.*) 
Ltac Rplus_lt_tac := 
  match goal with
  | [ H1 : ?r1 < ?r3, H2 : ?r2 < ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 <= ?r3, H2 : ?r2 < ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_le_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r3, H2 : ?r2 <= ?r4 |- ?r1 + ?r2 < ?r3 + ?r4] =>
    apply Rplus_lt_le_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r3, H2 : ?r2 < ?r4 |- ?r2 + ?r1 < ?r3 + ?r4] =>
    rewrite Rplus_comm; apply Rplus_lt_compat;[apply H1 | apply H2]
  | [ H1 : ?r1 < ?r2|- ?r + ?r1 < ?r + ?r2] =>
    apply Rplus_lt_compat_l;apply H1
  | [ H1 : ?r1 < ?r2|- ?r1 + ?r < ?r2 + ?r] =>
    apply Rplus_lt_compat_r;apply H1
  | [ H : ?r1 + ?r < ?r2 + ?r |- ?r1 < ?r2] =>
    apply Rplus_lt_reg_l in H; assumption
  | [ H : ?r + ?r1 < ?r + ?r2 |- ?r1 < ?r2] =>
    apply Rplus_lt_reg_r in H; assumption
  | [ H : ?x < ?y + ?z |- ?x - ?z < ?y] =>
    apply Rplus_lt_swap_rr; assumption
  | [ H : ?x + ?y < ?z |- ?y < ?z - ?x] =>
    apply Rplus_lt_swap_ll; assumption
  | [ H : ?x < ?y + ?z |- ?x - ?y < ?z] =>
    apply Rplus_lt_swap_rl; assumption
  | [ H : ?x + ?y < ?z |- ?x < ?z - ?y] =>
    apply Rplus_lt_swap_lr; assumption
  | [ |- ?r1 < ?r1 + _] => apply Rlt_plus_r
  | [ |- ?r1 < _ + ?r1] => apply Rlt_plus_l
  | [ H : ?x + ?y < ?z |- ?x < ?z] =>
    eapply Rplus_lt_weaken_lr; apply H
  | [ H : ?x + ?y < ?z |- ?y < ?z] =>
    eapply Rplus_lt_weaken_ll; apply H
  end.

(** Takes a hypothesis H of type r1 < r2 and gives a hypothesis U of type
r2 = r1 + d'*)
Ltac Rlttoplus H d' U := let Q1 := fresh in lets Q1 : RltPlusExistsL H;
  let U1 := fresh U in let U2 := fresh U in decompExAnd Q1 d' U1 U2.


(****************************** Restricted Reals ******************************)

(** Performs a contradiction on the assumption that some non-negative real is
less than 0, i.e. negative.*)
Ltac nonneg_lt0_contra :=
  match goal with
  | [H : (nonneg ?x) < 0 |- _] =>
    apply Rlt_not_le in H; false; apply H; unwrap_apply2 x
  end.

(** The number one as a positive real number.*)
Definition onePos : posreal. assert (0 < (INR 1)). apply lt_0_INR.
  constructor. eapply mkposreal. apply H. Defined.

(** The minimum of two numbers. Note, r2 is returned if the numbers are equal,
but in that case r1 = r2, so this is the same as returning r1.*)
Definition minR (r1 r2 : R) : R :=
  if (Rlt_le_dec r1 r2) then r1 else r2.

(** The maximum of two numbers. Note, r1 is returned if the numbers are equal,
but in that case r1 = r2, so this is the same as returning r2.*)
Definition maxR (r1 r2 : R) : R :=
  if (Rlt_le_dec r1 r2) then r2 else r1.

Definition zeroNonneg : nonnegreal := mknonnegreal 0 (Rle_refl 0).

(** Euclidean distance is always >= 0.*)
Lemma dist_euc_nonneg : forall (x1 y1 x2 y2 : R),
  0 <= dist_euc x1 y1 x2 y2. intros. unfold dist_euc.
  apply sqrt_positivity. apply Rplus_le_le_0_compat;
  apply Rle_0_sqr. Qed.

(** Adding a vector to both points leaves distance unchanged.*)
Lemma dist_eucAddPres : forall (x1 y1 x2 y2 x3 y3 : R),
  dist_euc x1 y1 x2 y2 = dist_euc (x1 + x3) (y1 + y3) (x2 + x3) (y2 + y3).
  intros. unfold dist_euc. unfold Rsqr. f_equal. ring. Qed.

(** Adding (x, y) to one of the coordinates of dist_euc yeilds and expression
that is within |(x, y)| of the original.*)
Lemma dist_eucAddLe : forall (x1 y1 x2 y2 x3 y3 : R),
  dist_euc (x1 + x3) (y1 + y3) (x2) (y2) <=
  dist_euc x1 y1 x2 y2 + dist_euc x3 y3 0 0.
  intros. rewrite (dist_eucAddPres x3 y3 0 0 x1 y1).
  repeat rewrite Rplus_0_l. rewrite Rplus_comm.
  replace (dist_euc x1 y1 x2 y2 + dist_euc (x3 + x1) (y3 + y1) x1 y1)
  with (dist_euc (x3 + x1) (y3 + y1) x1 y1 + dist_euc x1 y1 x2 y2).
  replace (y3 + y1) with (y1 + y3). apply triangle. apply Rplus_comm.
  apply Rplus_comm. Qed.

(**To show the equality of two nonnegative reals, it suffices to show
the equality of the numerical parts, i.e. we can ignore the proof terms.*)
Lemma nonnegRealEqR : forall (r1 r2 : nonnegreal),
  nonneg r1 = nonneg r2 -> r1 = r2. intros. destruct r1. destruct r2.
  simpl in H. generalize cond_nonneg. rewrite H. intros. f_equal.
  apply proof_irrelevance. Qed.

(**To show the equality of two positive reals, it suffices to show
the equality of the numerical parts, i.e. we can ignore the proof terms.*)
Lemma posRealEqR : forall (r1 r2 : posreal),
  pos r1 = pos r2 -> r1 = r2. intros. destruct r1. destruct r2.
  simpl in H. generalize cond_pos. rewrite H. intros. f_equal.
  apply proof_irrelevance. Qed.

Open Scope R_scope.

(** Multiplication defined for nonneg reals.*)
Definition multNonneg (r1 r2 : nonnegreal) : nonnegreal :=
  let prod := (r1 * r2) in
  let h1 := cond_nonneg r1 in
  let h2 := cond_nonneg r2 in
  let h := Rmult_le_0_compat r1 r2 h1 h2 in
  mknonnegreal prod h.
Notation "r1 *nn* r2" := (multNonneg r1 r2) (at level 40, left associativity).

(** Subtraction on nonnegative reals as a total function.
Gives r1 - r2 if that result is nonnegative, else returns 0.*)
Definition subNonnegTot (r1 r2 : nonnegreal) : nonnegreal :=
  match (Rle_dec r2 r1) with
  | left p => mknonnegreal (r1 - r2) (RleMinusBothSides r1 r2 p)
  | _ => zeroNonneg
  end.
Notation "r1 -nn- r2" := (subNonnegTot r1 r2) (at level 50).

(** Adds two nonnegreals together to get a resulting nonegreal.*)
Definition addNonneg (r1 r2 : nonnegreal) : nonnegreal :=
  match r1 with
  | {|nonneg := x1; cond_nonneg := cn1 |} => match r2 with
  | {|nonneg := x2; cond_nonneg := cn2 |} => let r := x1 + x2 in
  let Heqr := eq_refl r in
  {| nonneg := r; cond_nonneg := eq_ind_r (fun r0 : R => 0 <= r0)
   (Rplus_le_le_0_compat x1 x2 cn1 cn2) Heqr |} end end.
Notation "x +nn+ y" := (addNonneg x y) (at level 50).

(** Adding two nonneg numbers and then removing the real part is the same
as removing the real part and then adding*)
Lemma addNonnegFact : forall (r1 r2 : nonnegreal),
  nonneg (r1 +nn+ r2) = (nonneg r1) + (nonneg r2).
  intros. unfold addNonneg. destruct r1, r2. simpl.
  reflexivity. Qed.

(** zeroNonneg is the right zero for addNonneg*)
Lemma addNonnegZeroR : forall (r : nonnegreal),
  r +nn+ zeroNonneg = r. intros.
  assert (nonneg (r +nn+ zeroNonneg) = nonneg r).
  rewrite addNonnegFact. unfold zeroNonneg. simpl. ring.
  destruct (r +nn+ zeroNonneg), r. simpl in H.
  generalize dependent cond_nonneg0.
  generalize dependent cond_nonneg.
  rewrite H. intros. f_equal. apply proof_irrelevance. Qed.

(** zeroNonneg is the right zero for addNonneg*)
Lemma addNonnegZeroL : forall (r : nonnegreal),
  zeroNonneg +nn+ r = r. intros.
  assert (nonneg (zeroNonneg +nn+ r) = nonneg r).
  rewrite addNonnegFact. unfold zeroNonneg. simpl. ring.
  destruct (zeroNonneg +nn+ r), r. simpl in H.
  generalize dependent cond_nonneg0.
  generalize dependent cond_nonneg.
  rewrite <- H. intros. f_equal. apply proof_irrelevance. Qed.

(** Removes the proof from an equality of nonnegative reals, simplifying the
proof obligation to proving the equality on just the reals.*)
Lemma nonnegEqSimpl : forall (r1 r2 : nonnegreal),
  nonneg r1 = nonneg r2 -> r1 = r2. intros. destruct r1, r2.
  simpl in H. generalize dependent cond_nonneg.
  generalize dependent cond_nonneg. rewrite H. intros.
  f_equal. apply proof_irrelevance. Qed.

(** Addition of nonnegative reals is associative*)
Lemma addNonnegAssoc : forall (r1 r2 r3 : nonnegreal),
  r1 +nn+ (r2 +nn+ r3) = r1 +nn+ r2 +nn+ r3. intros. apply nonnegEqSimpl.
  repeat (rewrite addNonnegFact). ring. Qed.

Lemma addNonnegComm : forall (r1 r2 : nonnegreal),
  r1 +nn+ r2 = r2 +nn+ r1. intros. destruct r1, r2.
  simpl. apply nonnegEqSimpl. simpl. ring. Qed.

Lemma addNonnegCancel : forall (r1 r2 r3 : nonnegreal),
  r1 +nn+ r2 = r1 +nn+ r3 -> r2 = r3. intros.
  destruct r1 as [r1 c1]. destruct r2 as [r2 c2].
  destruct r3 as [r3 c3]. apply nonnegRealEqR.
  simpl. simpl in H. inversion H. eapply Rplus_eq_reg_l.
  apply H1. Qed.

(**Equality is decidable for reals.*)
Lemma eqDecReal : eqDec R. unfold eqDec. intros.
  generalize (total_order_T x1 x2). intros.
  inversion H. inversion H0. right. unfold not; intros. apply Rlt_not_eq in H1.
  inversion H2. apply H1. assumption. left. f_equal. assumption. right. unfold not.
  intros. apply Rlt_not_eq in H0. apply H0. symmetry.  assumption. Qed.

Lemma eqDecNonnegReal : eqDec nonnegreal. unfold eqDec. destruct x1, x2.
  generalize (eqDecReal nonneg nonneg0).
  intros. inversion H. left. generalize dependent cond_nonneg.
  generalize dependent cond_nonneg0. rewrite H0. intros. repeat f_equal.
  apply proof_irrelevance. right. unfold not; intros. inversion H1.
  apply H0. assumption. Qed.

Lemma eqDecPosReal : eqDec posreal. unfold eqDec. destruct x1, x2.
  generalize (eqDecReal pos pos0).
  intros. inversion H. left. generalize dependent cond_pos.
  generalize dependent cond_pos0. rewrite H0. intros. repeat f_equal.
  apply proof_irrelevance. right. unfold not; intros. inversion H1.
  apply H0. assumption. Qed.

(**Squares each element and the adds them.*)
Definition sumSquares (r1 r2 : R) : R :=
  Rsqr r1 + Rsqr r2.

(** Coerce a positive real to a nonnegative real.*)
Coercion posToNonneg (r : posreal) : nonnegreal :=
  match r with mkposreal p c =>
    mknonnegreal p (Rlt_le 0 p c) end.

(** Every positive real is the sum of two positive reals. The simplest
existential witnesses for this are both half the original number i.e. every number is equal
to half itself plus half itself.*)
Theorem addPosRealExists : forall (r : posreal),
  exists r1 r2, pos r = pos r1 + pos r2.
  intros. assert (0 < r/2). addHyp (Rlt_or_le 0 (r/2)). invertClear H.
  assumption. apply False_ind. apply (Rlt_not_le r 0). apply cond_pos.
  replace 0 with (0 + 0); [|ring]. rewrite (double_var r).
  apply Rplus_le_compat; assumption. remember (mkposreal (r/2) H) as r'.
  exists r'. exists r'. rewrite Heqr'. simpl. apply double_var. Qed.




(****************************** Position ******************************)

(** A position is a pair of reals.*)
Record Position := mkPosition {xCoord : R; yCoord : R}.

(** Addition on positions (vector addition).*)
Definition addPos (p1 p2 : Position) : Position :=
  let x1 := xCoord p1 in let y1 := yCoord p1 in
  let x2 := xCoord p2 in let y2 := yCoord p2 in
  mkPosition (x1 + x2) (y1 + y2).
Notation "p1 +p+ p2" := (addPos p1 p2) (at level 50).
Hint Unfold addPos.

(** Subtraction (vector) on positions.*)
Definition minusPos (p1 p2 : Position) : Position :=
  let x1 := xCoord p1 in let y1 := yCoord p1 in
  let x2 := xCoord p2 in let y2 := yCoord p2 in
  mkPosition (x1 - x2) (y1 - y2).
Notation "p1 -~p- p2" := (minusPos p1 p2) (at level 50).
Hint Unfold minusPos.

Definition oppPos (p : Position) : Position :=
  let x := xCoord p in let y := yCoord p in
  mkPosition (-x) (-y).
Notation "~- p" := (oppPos p) (at level 40).
Hint Unfold oppPos.

(** The Euclidean distance between a pair of positions.*)
Definition dist (p1 p2 : Position) : nonnegreal :=
  mknonnegreal
  (dist_euc (xCoord p1) (yCoord p1) (xCoord p2) (yCoord p2))
  (dist_euc_nonneg (xCoord p1) (yCoord p1) (xCoord p2) (yCoord p2)).

(** The origin is the point (0, 0).*)
Definition origin := mkPosition 0 0.

(** The vector length of a position. Defined to be the distance between
that position and (0, 0).*)
Definition displacement (p : Position) : nonnegreal := dist p origin.

Ltac unfoldPosDefs := unfold addPos; unfold minusPos; unfold oppPos;
  unfold dist; unfold origin; unfold displacement.

(** The negation of p1 - p2 is p2 - p1.*)
Theorem oppMinusPos : forall (p1 p2 : Position),
   ~-(p1 -~p- p2) = (p2 -~p- p1). intros. destruct p1.
  destruct p2. unfold minusPos. simpl. unfold oppPos.
  simpl. repeat rewrite Ropp_minus_distr. reflexivity.
  Qed.

(** 0 is the right unit of plus.*)
Theorem plusRightUnitPos : forall (p1 : Position),
  p1 +p+ origin = p1. intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring. Qed.

(** 0 is the left unit of plus.*)
Theorem plusLeftUnitPos : forall (p1 : Position),
  origin +p+ p1 = p1. intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring. Qed.

Theorem minusCancellativePos : forall (p1 : Position),
  p1 -~p- p1 = origin. intros. unfoldPosDefs. f_equal; ring. Qed.

(** Subtracting p2 is that same as adding -p2.*)
Theorem minusPlusOppPos : forall (p1 p2 : Position),
  p1 -~p- p2 = p1 +p+ (~-p2). intros. unfoldPosDefs. f_equal. Qed.

(** Add and then subtract p2 and you're left with the original position.*)
Lemma plusMinusCancelPos : forall (p1 p2 : Position),
  p1 +p+ p2 -~p- p2 = p1. intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring. Qed.

(** Subtract and then add p2 and you're left with the original position.*)
Lemma minusPlusCancelPos : forall (p1 p2 : Position),
  p1 -~p- p2 +p+ p2 = p1. intros. destruct p1. unfoldPosDefs.
  f_equal; simpl; ring. Qed.

(** The distance function is symmetric.*)
Lemma distSymmetric : forall (p1 p2 : Position), dist p1 p2 = dist p2 p1.
  intros. unfold dist. f_equal. apply nonnegRealEqR. simpl.
  apply distance_symm. Qed.

(** Adding the difference between two vectors to the subtracted
vector gets you the other vector.*)
Theorem minusPlusInvPos : forall (p1 p2 : Position),
  p1 = p2 +p+ (p1 -~p- p2). intros. destruct p1. unfoldPosDefs. simpl.
  repeat rewrite Rplus_minus. reflexivity. Qed.

(** Adding the same vector to the arguments of dist preserves the result.*)
Theorem distAddPres : forall (p1 p2 p3 : Position),
  dist p1 p2 = dist (p1 +p+ p3) (p2 +p+ p3). intros.
  unfold dist. destruct p1, p2, p3. simpl.
  generalize (dist_euc_nonneg xCoord0 yCoord0 xCoord1 yCoord1).
  generalize (dist_euc_nonneg (xCoord0 + xCoord2) (yCoord0 + yCoord2)
                 (xCoord1 + xCoord2) (yCoord1 + yCoord2)).
  rewrite <- dist_eucAddPres with (x3 := xCoord2) (y3 := yCoord2).
  intros. f_equal. apply proof_irrelevance. Qed.

(** Subtracting the same vector to the arguments of dist preserves the result.*)
Theorem distMinusPres : forall (p1 p2 p3 : Position),
  dist p1 p2 = dist (p1 -~p- p3) (p2 -~p- p3). intros.
  repeat rewrite minusPlusOppPos. apply distAddPres. Qed.

(** The distance between p1 and p2 is the same as the length of p1 - p2.*)
Theorem minusLengthDistance : forall (p1 p2 : Position),
  dist p1 p2 = displacement (p1 -~p- p2). intros. unfold displacement.
  rewrite (distAddPres (p1 -~p- p2) origin p2). rewrite minusPlusCancelPos.
  f_equal. rewrite plusLeftUnitPos. reflexivity. Qed.

(** Adding p3 to p1 changes the distance between p1 and p2 by
at most |p3|.*)
Theorem distAddLe : forall (p1 p2 p3 : Position),
  dist (p1 +p+ p3) (p2) <= dist p1 p2 + displacement p3. intros.
  destruct p1, p2, p3. unfoldPosDefs. simpl. apply dist_eucAddLe. Qed.

(** Adding p3 to p1 changes the distance between p1 and p2 by
at most r if |p3| <= r.*)
Theorem distAddLeLe : forall (p1 p2 p3 : Position) (r : R),
  displacement p3 <= r -> dist (p1 +p+ p3) (p2) <= dist p1 p2 + r. intros.
  Open Scope R_scope. apply Rle_trans with (r2 := (dist p1 p2 + displacement p3)).
  apply distAddLe. apply Rplus_le_compat_l. assumption. Qed.

(** If the distance between p1 and p1' is bounded above by r, and the
same holds for p2 and p2', then the distance between p1 and p2 is
at most the difference between p1' and p2' + 2r.*)
Theorem posDiffBound : forall (p1 p2 p1' p2' : Position) (r : R),
  dist p1  p1' <= r -> dist p2 p2' <= r ->
  dist p1 p2 <= dist p1' p2' + 2*r. intros. assert (2*r = r + r).
  ring. rewrite H1. rewrite <- Rplus_assoc.
  eapply Rle_trans. rewrite (minusPlusInvPos p1 p1'). apply distAddLeLe.
  rewrite <- minusLengthDistance. apply H. rewrite (minusPlusInvPos p2 p2').
  apply Rplus_le_compat_r. rewrite distSymmetric.
  replace (dist p1' p2') with (dist p2' p1'); try apply distSymmetric.
  apply distAddLeLe. rewrite <- minusLengthDistance. apply H0. Qed.

Lemma eqDecPosition : eqDec Position. unfold eqDec.
  destruct x1, x2. generalize (eqDecReal xCoord0 xCoord1).
  generalize (eqDecReal yCoord0 yCoord1). intros.
  inversion H. inversion H0. left. f_equal; assumption.
  right. unfold not; intros. apply H2. inversion H3.
  reflexivity. right. unfold not; intros. apply H1. inversion H2.
  reflexivity. Qed.

Lemma dist_tri_ineq : forall (l1 l2 l3 : Position),
  dist l1 l3 <= dist l1 l2 + dist l2 l3. intros l1 l2 l3. apply triangle.
  Qed.

Lemma dist_refl : forall l : Position, dist l l = zeroNonneg. intros.
  apply nonnegRealEqR. unfold dist. simpl. apply distance_refl. Qed.

(****************************** Interval ******************************)

(** An interval on the real line. We allow upper < lower, the interpretation
in this case being that the interval is empty. The two fields lowerClosed and
upperClosed allow for the four possibilities of interval, from fully closed
to fully open: [], [), (], ().*)
Record Interval := mkInterval{
  lower : R;
  upper : R;
  lowerClosed : bool;
  upperClosed : bool
  }.

(** inInterval r i means that the real number r is in the Interval i,
where i is interpreted as a closed interval.*)
Definition inInterval (r : R) (i : Interval) :=
  match lowerClosed i, upperClosed i with
  | true, true => lower i <= r <= upper i
  | true, false => lower i <= r < upper i
  | false, true => lower i < r <= upper i
  | false, false => lower i < r < upper i
  end.
Notation "r [:] i" := (inInterval r i) (at level 70).

(** v1 is a (non-strict) sub interval of v2*)
Definition subInterval (i1 i2 : Interval) : Prop :=
  forall r : R, r [:] i1 -> r [:] i2.

Open Scope R_scope.

(** Add the lower bounds and the upper bounds just as in vector addition.
Closedness of a bound in the resulting interval is equivalent to closedness of
the respective bounds in both i1 and i2.*)
Definition addInterval (i1 i2 : Interval) : Interval :=
  match i1 with (mkInterval l1 u1 lc1 uc1) =>
  match i2 with (mkInterval l2 u2 lc2 uc2) =>
  mkInterval (l1 + l2) (u1 + u2) (andb lc1 lc2) (andb uc1 uc2)
  end end.
Notation "i [++] i'" := (addInterval i i') (at level 45).

(** If x is in i then x is less than or equal to the upper bound of i.*) 
Lemma inIntervalLeUpper : forall (i : Interval) (x : R),
  x [:] i -> x <= upper i. destruct i. intros. unfold inInterval in H.
  simpl in H. destruct lowerClosed0, upperClosed0; simpl; inversion H;
  try assumption; try apply Rlt_le; assumption. Qed. 

(** If x is in i then the lower bound of i is less than or equal x.*) 
Lemma inIntervalLeLower: forall (i : Interval) (x : R),
  x [:] i -> lower i <= x. destruct i. intros. unfold inInterval in H.
  simpl in H. destruct lowerClosed0, upperClosed0; simpl; inversion H;
  try assumption; try apply Rlt_le; assumption. Qed. 

Lemma inIntervalLtUpper : forall (i : Interval) (r : R),
  r [:] i -> upperClosed i = false ->
  r < upper i. intros. destruct i. destruct lowerClosed0.
  simpl in H0. rewrite H0 in H. unfold inInterval in H.
  simpl in H. simpl. invertClear H. assumption.
  simpl in H0. rewrite H0 in H. unfold inInterval in H.
  simpl in H. simpl. invertClear H. assumption. Qed.

Lemma inIntervalLtLower : forall (i : Interval) (r : R),
  r [:] i -> lowerClosed i = false ->
  lower i < r. intros. destruct i. destruct upperClosed0.
  simpl in H0. rewrite H0 in H. unfold inInterval in H.
  simpl in H. simpl. invertClear H. assumption.
  simpl in H0. rewrite H0 in H. unfold inInterval in H.
  simpl in H. simpl. invertClear H. assumption. Qed.

Lemma inAddLtLower : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 ->
  lowerClosed i1 = false \/ lowerClosed i2 = false ->
  lower i1 + lower i2 < r1 + r2. intros.
  inversion H1. apply Rplus_lt_le_compat.
  apply inIntervalLtLower; assumption.
  apply inIntervalLeLower; assumption.
  apply Rplus_le_lt_compat.
  apply inIntervalLeLower; assumption.
  apply inIntervalLtLower; assumption.
  Qed.

Lemma inAddLtUpper : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 ->
  upperClosed i1 = false \/ upperClosed i2 = false ->
  r1 + r2 < upper i1 + upper i2. intros.
  inversion H1. apply Rplus_lt_le_compat.
  apply inIntervalLtUpper; assumption.
  apply inIntervalLeUpper; assumption.
  apply Rplus_le_lt_compat.
  apply inIntervalLeUpper; assumption.
  apply inIntervalLtUpper; assumption.
  Qed.

Lemma addIntervalLower : forall (i1 i2 : Interval),
  lower (i1 [++] i2) = lower i1 + lower i2.
  destruct i1, i2; reflexivity. Qed.

Lemma addIntervalUpper : forall (i1 i2 : Interval),
  upper (i1 [++] i2) = upper i1 + upper i2.
  destruct i1, i2; reflexivity. Qed.

Lemma addIntervalUpperOpen : forall (i1 i2 : Interval),
  upperClosed (i1 [++] i2) = false ->
  upperClosed i1 = false \/ upperClosed i2 = false.
  destruct i1, i2. simpl. intros. apply Bool.andb_false_iff.
  assumption. Qed.

Lemma addIntervalLowerOpen : forall (i1 i2 : Interval),
  lowerClosed (i1 [++] i2) = false ->
  lowerClosed i1 = false \/ lowerClosed i2 = false.
  destruct i1, i2. simpl. intros. apply Bool.andb_false_iff.
  assumption. Qed.

Theorem inAddInterval : forall (i1 i2 : Interval) (r1 r2 : R),
  r1 [:] i1 -> r2 [:] i2 -> (r1 + r2) [:] (i1 [++] i2).
  intros. unfold inInterval. remember (lowerClosed (i1[++]i2)) as l.
  remember (upperClosed (i1[++]i2)) as u. destruct l, u;
  rewrite addIntervalLower, addIntervalUpper.
  split. apply Rplus_le_compat; apply inIntervalLeLower; assumption.
  apply Rplus_le_compat; apply inIntervalLeUpper; assumption.
  (*Case 2*)
  split. apply Rplus_le_compat; apply inIntervalLeLower; assumption.
  apply inAddLtUpper; try assumption.
  apply addIntervalUpperOpen. symmetry. assumption.
  (*Case 3*)
  split. apply inAddLtLower; try assumption.
  apply addIntervalLowerOpen. symmetry. assumption.
  apply Rplus_le_compat; apply inIntervalLeUpper; assumption.
  (*Case 4*)
  split. apply inAddLtLower; try assumption.
  apply addIntervalLowerOpen. symmetry. assumption.
  apply inAddLtUpper; try assumption.
  apply addIntervalUpperOpen. symmetry. assumption.
  Qed.

(** Shifts an interval right by some amount i.e. adds that amount to the upper and lower
bounds of the interval. Closedness does not change.*)
Definition plusInterval (i : Interval) (r : R) : Interval :=
  match i with mkInterval l u cl cu=>
  mkInterval (l + r) (u + r) cl cu end.

(** Shifts an interval left by some amount i.e. adds that amount to the upper and lower
bounds of the interval.*)
Definition minusInterval (i : Interval) (r : R) : Interval :=
  match i with mkInterval l u cl cu=>
  mkInterval (l - r) (u - r) cl cu end.

Notation "i [+] r" := (plusInterval i r) (at level 45).
Notation "i [-] r" := (minusInterval i r) (at level 45).
Notation "[\ x , y \]" := (mkInterval x y true true).
Notation "[\ x , y \)" := (mkInterval x y true false).
Notation "(\ x , y \]" := (mkInterval x y false true).
Notation "(\ x , y \)" := (mkInterval x y false false).
Notation "i1 <[ i2" := (subInterval i1 i2) (at level 50).

(** Every interval can be rewritten by subtracting and then adding the same r.*)
Theorem minusPlusInterval : forall (i : Interval) (r : R),
  i = i [-] r [+] r. intros. destruct i. simpl. f_equal; ring. Qed.

(** Every interval can be rewritten by adding and then subtracting the same r.*)
Theorem plusMinusInterval : forall (i : Interval) (r : R),
  i = i [+] r [-] r. intros. destruct i. simpl. f_equal; ring. Qed.

(** Adding a negative is the same as subtracting*)
Theorem minusOppInterval : forall (i : Interval) (r : R),
  i [+] -r = i [-] r. intros. destruct i. simpl. f_equal; ring. Qed.

Theorem inIntervalPlusCancel : forall (i : Interval) (x r : R),
  x + r [:] i [+] r -> x [:] i. intros. destruct i.
  destruct lowerClosed0, upperClosed0. inversion H. clear H;
  simpl in H0, H1; unfold inInterval; simpl; split;
  replace lower0 with (lower0 + r - r);
  replace upper0 with (upper0 + r - r);
  replace x with (x + r - r); try ring; (apply Rplus_le_compat;
  [assumption | apply Rle_refl]).
  inversion H. clear H;
  simpl in H0, H1; unfold inInterval; simpl; split;
  replace lower0 with (lower0 + r - r);
  replace upper0 with (upper0 + r - r);
  replace x with (x + r - r); try ring. apply Rplus_le_compat;
  [assumption | apply Rle_refl].
  apply Rplus_lt_le_compat;[assumption | apply Rle_refl].
  inversion H. clear H;
  simpl in H0, H1; unfold inInterval; simpl; split;
  replace lower0 with (lower0 + r - r);
  replace upper0 with (upper0 + r - r);
  replace x with (x + r - r); try ring.
  apply Rplus_lt_le_compat;[assumption | apply Rle_refl].
  apply Rplus_le_compat; [assumption | apply Rle_refl].
  inversion H. clear H;
  simpl in H0, H1; unfold inInterval; simpl; split;
  replace lower0 with (lower0 + r - r);
  replace upper0 with (upper0 + r - r);
  replace x with (x + r - r); try ring; (apply Rplus_lt_le_compat;
  [assumption | apply Rle_refl]). Qed.

Theorem subIntervalPlusCancel : forall (i i' : Interval) (r : R),
  i [+] r <[ i' [+] r -> i <[ i'. unfold subInterval. intros.
  eapply inIntervalPlusCancel. apply H.
  apply inIntervalPlusCancel with (r := -r).
  rewrite minusOppInterval. rewrite <- plusMinusInterval.
  replace (r0 + r + - r) with r0. apply H0. ring. Qed.

Theorem inIntervalPlusCompat : forall (i : Interval) (x r : R),
  x [:] i -> x + r [:] i [+] r. intros.
  apply inIntervalPlusCancel with (r := -r).
  replace (x + r + - r) with x.
  replace ((i[+]r)[+]- r) with i. assumption.
  destruct i. simpl. f_equal; ring. ring. Qed.

(** Every interval is a sub interval of itself.*)
Lemma subIntervalRefl : forall (i : Interval), i <[ i. unfold subInterval.
  intros; assumption. Qed.


(** If a number is less than the lower bound of an interval then it is
not in that interval.*)
Lemma outIntervalLtLower : forall (r : R) (i : Interval),
  r < lower i -> ~ r [:] i. unfold not; intros.
  apply inIntervalLeLower in H0. eapply Rlt_not_le.
  apply H. assumption. Qed.

(** If a number is greater than the upper bound of an interval then it is
not in that interval.*)
Lemma outIntervalLtUpper : forall (r : R) (i : Interval),
  upper i < r-> ~ r [:] i. unfold not; intros.
  apply inIntervalLeUpper in H0. eapply Rlt_not_le.
  apply H. assumption. Qed.

(** If a number is less than or equal the lower bound of an interval
that is lower closed then it is not in the interval.*)
Lemma outIntervalLeLower : forall (r : R) (i : Interval),
  r <= lower i -> lowerClosed i = false -> ~ r [:] i.
  unfold not; intros. eapply Rlt_not_le; try
  eapply inIntervalLtLower; try apply H1; assumption. Qed.

(** If a number is less than or equal the lower bound of an interval
that is lower closed then it is not in the interval.*)
Lemma outIntervalLeUpper : forall (r : R) (i : Interval),
  upper i <= r -> upperClosed i = false -> ~ r [:] i.
  unfold not; intros. eapply Rlt_not_le; try
  eapply inIntervalLtUpper; try apply H1; assumption. Qed.

(** Membership of an interval is decidable.*)
Lemma inIntervalDec : forall (r : R) (i : Interval),
  r [:] i \/ ~ r [:] i. intros.
  destruct i as [l u cl cu].
  addHyp (Rle_dec l r). addHyp (Rlt_dec l r).
  addHyp (Rle_dec r u). addHyp (Rlt_dec r u).
  destruct cl, cu; unfold inInterval; simpl.
  invertClear H. invertClear H1. left; split; assumption.
  right. unfold not. intro. apply H. inversion H1. assumption.
  right. unfold not. intro. apply H3. inversion H. assumption.
  invertClear H. invertClear H2. left; split; assumption.
  right. unfold not. intro. apply H. inversion H2. assumption.
  right. unfold not. intro. apply H3. inversion H. assumption.
  invertClear H0. invertClear H1. left; split; assumption.
  right. unfold not. intro. apply H0. inversion H1. assumption.
  right. unfold not. intro. apply H3. inversion H0. assumption.
  invertClear H0. invertClear H2. left; split; assumption.
  right. unfold not. intro. apply H0. inversion H2. assumption.
  right. unfold not. intro. apply H3. inversion H0. assumption.
  Qed.

(**If a number exists in the point interval [x, x]
then that number must be equal to x.*)
Lemma inIntervalPoint : forall (x y : R),
  x [:] [\y, y\] -> x = y. intros. inversion H.
  eapply Rle_antisym; assumption. Qed.

(*LOCAL TIDY*)

Ltac Rminus_refl_simpl := match goal with |- context [?x - ?x] =>
  replace (x - x) with 0; [ | ring] end.

Lemma Rminus_lt_subNonnegTot (a b : nonnegreal) c :
  0 < c -> a - b < c -> a -nn- b < c. unfold subNonnegTot.
  remember (Rle_dec b a). intros. destruct s. assumption.
  assumption. Qed.

Lemma Rminus_plus_lt_subNonnegTot (a b : nonnegreal) c z :
  z < c -> a - b + z < c -> a -nn- b + z < c. intros.
  apply Rplus_lt_swap_lr in H0. assert (0 < c - z).
  apply Rplus_lt_swap_ll. my_applys_eq H. ring.
  apply Rminus_lt_swap_rr. apply Rminus_lt_subNonnegTot;
  assumption. Qed.

Lemma subNonnegTot_le_Rminus_eq (r1 r2 : nonnegreal) :
  r2 <= r1 -> nonneg (r1 -nn- r2) = r1 - r2. intros.
  unfold subNonnegTot. remember (Rle_dec r2 r1). destruct s.
  reflexivity. false. Qed.

Lemma Rlt_double x : 0 < x -> x < x + x. intro. cut (0 + x < x + x).
  intros. rewrite Rplus_0_l in H0. assumption. apply Rplus_lt_le_compat.
  assumption. apply Rle_refl. Qed.
  
Lemma Rmult_lt_0 y z : 0 < y -> 0 < z -> 0 < y * z.
  intros. replace 0 with (0 * z);[ | ring].
  apply Rmult_lt_compat_r; assumption. Qed.

Lemma Rlt_le_zero_plus r1 r2 : 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
  intros. replace 0 with (0 + 0). apply Rplus_lt_le_compat; assumption.
  ring. Qed.

Lemma Rmax_lt_l x y a : a < x -> a < Rmax x y. intros. unfold Rmax.
  remember (Rle_dec x y). destruct s. eapply Rlt_le_trans; eassumption.
  assumption. Qed.

Lemma subNonnegTot_0_or_Rminus r1 r2 :
  nonneg (r1 -nn- r2) = 0 \/
  nonneg (r1 -nn- r2) = r1 - r2. unfold subNonnegTot.
  destruct (Rle_dec r2 r1). right. reflexivity.
  left. reflexivity. Qed.

Lemma subNonnegTot_lt_0 (r1 r2 : nonnegreal) :
  r1 < r2 -> nonneg (r1 -nn- r2) = 0. intros.
  unfold subNonnegTot. remember (Rle_dec r2 r1). destruct s.
  apply Rlt_not_le in H. false. reflexivity. Qed.

Ltac Rplus3_swap_2_3_free := match goal with
  | |- context[?r1 + ?r2 + ?r3] => Rplus3_swap_2_3 r1 r2 r3 
  | |- context[?r1 + (?r2 + ?r3)] => rewrite <- Rplus_assoc;
    Rplus3_swap_2_3 r1 r2 r3
  end.

Lemma Rle_subNonnegTot_r (r1 r2 r3 : nonnegreal) :
  r1 <= r2 -> (r1 -nn- r3) <= (r2 -nn- r3). intros.
  lets RLD : Rle_or_lt r3 r1. elim_intro RLD LER LTR.
  repeat rewrite subNonnegTot_le_Rminus_eq. apply Rplus_le_compat_r.
  assumption. eapply Rle_trans; eassumption. assumption.
  rewrite subNonnegTot_lt_0. apply cond_nonneg. assumption. Qed.

Lemma addNonneg_subNonnegTot_le_assoc r1 r2 r3 :
  (r1 +nn+ r2) -nn- r3 <= r1 +nn+ (r2 -nn- r3).
  lets RLD : Rle_lt_dec r3 r2. elim_intro RLD LER LTR.
  rewrite addNonnegFact. rewrite (subNonnegTot_le_Rminus_eq r2 r3);[ | assumption].
  assert (nonneg r3 <= nonneg (r1 +nn+ r2)). rewrite addNonnegFact.
  eapply Rle_trans. apply LER. Rplus_le_tac. apply cond_nonneg.
  rewrite subNonnegTot_le_Rminus_eq; [ | assumption].
  rewrite addNonnegFact. apply Req_le. ring.
  rewrite addNonnegFact. rewrite (subNonnegTot_lt_0 r2 r3);[ | assumption].
  lets STM : subNonnegTot_0_or_Rminus (r1 +nn+ r2) r3. elim_intro STM SZ SM.
  rewrite SZ. Rplus_le_tac. apply cond_nonneg. rewrite SM.
  rewrite addNonnegFact. lets RP : RltPlusExistsR LTR. exand_flat.
  rewrite AND. replace (nonneg r1 + nonneg r2 - (nonneg r2 + x))
  with (nonneg r1 - x);[ | ring]. apply Rplus_le_swap_rr.
  rewrite Rplus_assoc. Rplus_le_tac. Rplus_le_tac.
  apply Rlt_le. assumption. Qed.

Lemma multNonneg_Rmult_eq r1 r2 :
  nonneg (r1 *nn* r2) = r1 * r2. destruct r1, r2.
  reflexivity. Qed.

Lemma subNonnegTot_le_Rminus (r1 r2 : nonnegreal) :
  r1 - r2 <= (r1 -nn- r2). lets RLD : Rle_lt_dec r2 r1.
  elim_intro RLD LER LTR. rewrite subNonnegTot_le_Rminus_eq.
  apply Rle_refl. assumption. rewrite subNonnegTot_lt_0.
  apply Rplus_le_swap_rl. apply Rlt_le in LTR. my_applys_eq LTR.
  ring. assumption. Qed.

Lemma subNonnegTot_plus_lt_Rminus (a b : nonnegreal) c z :
  a -nn- b + z < c -> a - b + z < c. intros. eapply Rle_lt_trans;
  [ | apply H]. Rplus_le_tac. apply subNonnegTot_le_Rminus. Qed.

(*-LOCAL TIDY*)