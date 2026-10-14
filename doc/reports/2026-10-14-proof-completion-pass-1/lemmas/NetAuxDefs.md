# Unproved lemmas in `NetAuxDefs`

[← Lemma index](README.md) · [Report summary](../README.md)

4 lemmas here could not be proved as stated, none of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `msgBad_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 168 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change). No users: could simply be deleted.

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

## `notifBad_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 171 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change). No users: could simply be deleted.

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

## `msgAbort_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 174 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change).

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

## `notifAbort_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 177 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change).

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.
