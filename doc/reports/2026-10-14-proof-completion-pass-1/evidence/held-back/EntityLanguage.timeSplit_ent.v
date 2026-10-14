(* HELPERS *)
From Stdlib Require Import Lra.

(** Helper for timeSplit_ent: scaling a vector by a nonnegative factor scales its
displacement by the same factor.*)
Local Lemma timeSplit_ent_aux1 (s x y : R) : 0 <= s ->
  nonneg (displacement (mkPosition (s * x) (s * y))) =
  s * nonneg (displacement (mkPosition x y)).
  intros. unfold displacement, dist2d, origin, dist_euc. simpl.
  replace (Rsqr (s * x - 0) + Rsqr (s * y - 0)) with
    (Rsqr s * (Rsqr (x - 0) + Rsqr (y - 0))) by (unfold Rsqr; ring).
  rewrite sqrt_mult_alt by apply Rle_0_sqr. rewrite sqrt_Rsqr by assumption.
  reflexivity. Qed.
(* PROOF *)
Proof.
  intros ED EQ. inversion ED as [d0 p p'' l delta i i'' k k'' PD ID KD DISP NS]; subst.
  lets TSP : timeSplit PD (eq_refl (d +d+ d')). destruct TSP as [p' [PD1 PD2]].
  lets TSI : timeSplit_inter ID (eq_refl (d +d+ d')). destruct TSI as [i' [ID1 ID2]].
  lets TSK : timeSplit_mState KD (eq_refl (d +d+ d')). destruct TSK as [k' [KD1 KD2]].
  assert (DP : 0 < pos (delay d)) by (destruct d as [[r rp]]; simpl; assumption).
  assert (DP' : 0 < pos (delay d')) by (destruct d' as [[r rp]]; simpl; assumption).
  set (r := pos (delay d)) in *. set (r' := pos (delay d')) in *.
  assert (SUM : pos (delay (d +d+ d')) = r + r') by reflexivity.
  set (s1 := r / (r + r')). set (s2 := r' / (r + r')).
  assert (S1 : 0 <= s1) by (unfold s1; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  assert (S2 : 0 <= s2) by (unfold s2; apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  destruct delta as [x y].
  exists ([|p', addPos l (mkPosition (s1 * x) (s1 * y)), i', k'|]).
  rewrite SUM in DISP.
  set (D := nonneg (displacement (mkPosition x y))) in *.
  split.
  (*First step*)
  constructor; try assumption.
  rewrite timeSplit_ent_aux1 by assumption. fold D.
  apply Rle_trans with (s1 * (speedMax * (r + r'))).
  apply Rmult_le_compat_l; assumption.
  right. unfold s1. change (pos (delay d)) with r. field. lra.
  intro a. destruct (NS a) as [NS1 NS2]. split. assumption.
  intros p2 i2 k2 d2 LT P2 I2 K2. apply (NS2 p2 i2 k2 d2); try assumption.
  rewrite SUM. unfold r, r' in *. lra.
  (*Second step*)
  replace (addPos l (mkPosition x y)) with
    (addPos (addPos l (mkPosition (s1 * x) (s1 * y))) (mkPosition (s2 * x) (s2 * y))).
  constructor; try assumption.
  rewrite timeSplit_ent_aux1 by assumption. fold D.
  apply Rle_trans with (s2 * (speedMax * (r + r'))).
  apply Rmult_le_compat_l; assumption.
  right. unfold s2. change (pos (delay d')) with r'. field. lra.
  intro a. destruct (NS a) as [NS1 NS2]. split.
  apply (NS2 p' i' k' d); try assumption. rewrite SUM. unfold r, r' in *. lra.
  intros p2 i2 k2 d2 LT PD3 ID3 KD3. apply (NS2 p2 i2 k2 (d +d+ d2)).
  rewrite SUM. simpl. unfold r, r' in *. lra.
  eapply delAddSoft; eassumption.
  eapply delAddInter; eassumption.
  eapply delAddMState; eassumption.
  assert (E : s1 + s2 = 1) by (unfold s1, s2; field; lra).
  unfold addPos. simpl. f_equal.
  transitivity (xCoord l + (s1 + s2) * x). ring. rewrite E. ring.
  transitivity (yCoord l + (s1 + s2) * y). ring. rewrite E. ring.
  Qed.
