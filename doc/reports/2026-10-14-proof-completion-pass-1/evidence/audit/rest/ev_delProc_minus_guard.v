Lemma delProc_minus_guard_refuted :
  ~ (forall t d d' H p p' e,
       $< minusTime t (delay d) H >$ p -PD- d' -PD> p' ->
       $< e >$ p -PD- d +d+ d' -PD> p').
Proof.
  intro S.
  set (d := mkDelay (mkposreal 1 Rlt_0_1)).
  set (t := pos (delay d)).
  assert (H : pos (delay d) <= t) by (unfold t; apply Rle_refl).
  assert (P : $< minusTime t (delay d) H >$ nilProc -PD- (minusTime t (delay d) H) +dt+ d -PD> nilProc).
  { apply stepTpDelAdd; [apply stepTpNil | apply evalExpFunTime_time]. }
  specialize (S _ _ _ _ _ _ (eVar (var 0)) P).
  inversion S; subst;
  match goal with [E : evalExpFunTime (eVar _) = Some _ |- _] => simpl in E; discriminate E end.
Qed.
