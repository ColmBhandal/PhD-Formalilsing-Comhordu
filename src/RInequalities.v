Require Export Reals.
Require Import ComhCoq.GenTacs.
Require Import ComhCoq.Extras.LibTactics.
Open Scope R_scope.

Ltac Rmult_le_zero :=
  match goal with
  | [ |- 0 <= ?y1 * ?y2] => 
    replace 0 with (0 * 0);[ | ring];
    apply Rmult_le_compat;[apply Rle_refl | apply Rle_refl | ..]
  end.

(** Splits the goal into 2 subgoals based on d <= t or t < d*)
Ltac Rleltcases d t U :=  let H := fresh in lets H : Rle_or_lt d t;
                                            let U1 := fresh U in elim_intro H U1 U1.

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
  replace (r2 - r1 + r1) with r2; try ring. rewrite Rplus_0_l.
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
