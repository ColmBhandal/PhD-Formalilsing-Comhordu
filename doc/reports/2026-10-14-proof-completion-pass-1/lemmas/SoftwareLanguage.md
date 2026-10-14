# Unproved lemmas in `SoftwareLanguage`

[← Lemma index](README.md) · [Report summary](../README.md)

1 lemma here could not be proved as stated, none of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `delProc_minus_guard`

- **Where:** `src/SoftwareLanguage.v` line 2000 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:unconstrained-guard-expression` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis evalExpFunTime e = Some t (delAddSoft has it in context at the call).

- **Status:** FALSE / NEEDS-HYPOTHESIS (counterexample, machine-checked in the cloud session from the definitions alone, so admitting it is inconsistent)
- **Intent:** If a guard counted down to `t - d` delays by `d'` to `p'`, then the original guard, which evaluates to `t`, delays by `d + d'` to `p'`. This is the `stepTpDelSub` case of `delAddSoft`.
- **Failure:**
  - The guard expression `e` in the conclusion is unconstrained.
  - Counterexample: `t := d`, `p := nilProc`, `e := eVar (var 0)`. The premise holds with `p' := nilProc`. But `evalExpFunTime e = None`, so only `stepTpDelIll` applies, which forces `p' = $<e>$ nilProc`.
  - Refutation proved: `~ (forall t d d' H p p' e, $<minusTime t d H>$ p -PD- d' -PD> p' -> $<e>$ p -PD- d +d+ d' -PD> p')`.
- **Ripple-up:**
  - Its only user is `SoftwareLanguage.delAddSoft`, an existing `Qed` lemma, in the `stepTpDelSub` case, where `evalExpFunTime e = Some t` is already in context.
  - Through `delAddSoft`, it underlies `EntityLanguage.timeSplit_ent`, then `NetworkLanguage.timeSplit_net`, which is in the safety cone.
  - `delAddSoft` itself is true; only its route through this lemma is unsound.
- **Suggested fix:** Add the missing hypothesis `evalExpFunTime e = Some t ->`. The corrected lemma was proved in full in the cloud session, and `delAddSoft`'s existing call (`eapply ...; eassumption`) should go through unchanged.
