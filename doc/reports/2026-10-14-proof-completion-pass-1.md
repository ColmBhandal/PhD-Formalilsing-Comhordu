# Proof completion, pass 1

**Date:** 2026-10-14 · **Workstream:** [Rocq upgrade & proof completion](../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md) · **Branch:** `claude/awesome-faraday-8n07pj`

This report covers the first agent pass over every unproved result in the development: all 228 `Admitted` lemmas and all 28 `Conjecture`s, 256 targets in total. For each target that could not be proved as stated, it says what the lemma was meant to say, why it fails, how the failure ripples up towards `safety`, and what should change. Per-lemma detail is in the [appendix](2026-10-14-proof-completion-pass-1-appendix.md).

## 1. Summary

- **The toolchain is current.** The project builds on Rocq 9.2.0 with no broken proofs. CI is green, and `Print Assumptions safety` is unchanged from the Coq 8.15 baseline.
- **The model axioms are consistent.** `src/ModelConsistency.v` gives an axiom-free, non-degenerate model of the 28 `ComhBasics` axioms.
- **123 of the 256 targets are now proved and merged.**
  - Every proof is checked in isolation, and the whole project rebuilds with all of them together.
  - A further 25 proofs exist but are **held back**, because they depend on admitted lemmas that turned out to be inconsistent (§3).
- **108 targets cannot be proved as stated.** Each one is written up. 93 of these were independently re-checked by an auditor that recompiled the counterexample against the exact statement (§4).
- **Headline: as the development stands, `safety` is vacuous.**
  - Its assumption set contains admitted lemmas that are refutable from the model axioms alone, so `False` is derivable from what `safety` rests on.
  - This was **found and machine-checked**, not just suspected.
  - It does not mean the protocol is unsafe. It means the formal proof currently establishes nothing until those lemmas are fixed.
  - Almost every problem traces back to about a dozen modelling issues, and each has a concrete proposed fix (§5). Most are statement or definition changes, so they need your approval.

## 2. What this PR changes

| Area | Change |
|---|---|
| Toolchain | Rocq 9.2.0 + `rocq-stdlib`. Explicit `From Stdlib` imports, LibTactics compatibility fixes, `rocq makefile`-based `Makefile`, `rocq-comhordu.opam`. No proof broke in the upgrade. |
| CI | `.github/workflows/build.yml` on `rocq/rocq-prover:9.2.0`. It builds everything and writes `make assumptions` to the job summary. |
| Rules | `AGENTS.md` files by directory (top level, `src/`, `doc/**`) and a `CLAUDE.md` pointer. |
| Docs | The 2015 plan is moved to `doc/archive/` after a relevance check. This workstream, this report and the reals ADR are added. |
| Reals | 58 hand-rolled inequality proofs in `RInequalities.v`/`StandardResults.v` replaced by `lra`/`nra` one-liners. Statements unchanged; trust base byte-identical (§8). |
| Model axioms | `src/ModelConsistency.v`: the axioms are jointly satisfiable by a non-degenerate model (§7). |
| Proofs | 123 targets proved. `Admitted`/`Conjecture` replaced by `Qed`, **statements unchanged**. Helper lemmas are prefixed with their target's name and placed just before it. |

Statements, definitions, model axioms and `Parameter` stubs are **unchanged everywhere**. Every proposed change below is a proposal for you to approve.

## 3. Is `safety` meaningful? Not yet: two independent reasons

**(a) Inconsistent admitted lemmas inside `safety`'s assumption cone.**

These admitted lemmas are on `safety`'s critical path, and each was refuted in Rocq from the model axioms plus the stdlib alone: `EntAuxResults.link_ent_outList`, `NARMisc.notifBadPathNet_urgent`, `NARMisc.outgoing_timeout_disc`, `NetAuxBasics.bcWaitNet_del_bkwd`, `NetAuxBasics.nextSince_del_ovWait`, `ProtAuxResults.listening_AN_prot`, `ProtAuxResults.ovWait_del_pres`, `ProtAuxResults.reachableProt_triple`.

The most structural of them is `ProtAuxResults.reachableProt_triple`, which says "every reachable protocol process is a triple of component states". It is false, because `overlapState` and `listenerState` are marked `INCOMPLETE` and list only some of the states, for example not `tfsStart` or `paused`. A single `chanBad?` step from the initial process reaches `sleeping || tfsStartN || listening`, which `overlapState` doesn't cover.

**(b) A trivialising pair.** `tfsListen_failSafe_net` and `currMode_intro` are both in the cone. Together they imply that every mode is fail-safe, and then `safe n` holds for every network, because `minDistComp` is 0 for fail-safe modes. The auditor compiled `stmt -> forall n, safe n`.

**Consequence.** `Print Assumptions safety` still lists 85 entries after this PR (50 of them unproved project lemmas; it was 134 and 100 before), and the formal result is vacuous until (a) and (b) are fixed. The fixes are mostly mechanical once you approve the definition changes (§5). Many dependent proofs already exist in conditional form, so pass 2 should be fast.

## 4. Results

### 4.1 Overall

| Outcome | Targets | In safety cone |
|---|---|---|
| Proved and merged | 123 | 57 |
| Proved, held back (depends on an inconsistent admit) | 25 | 12 |
| Not provable as stated (written up) | 108 | 31 |
| **Total** | **256** | **100** |

### 4.2 Why the unprovable ones fail (audit classes)

The auditors recompiled every claimed refutation against the target's exact statement and ran `Print Assumptions` on it. None of the evidence failed to compile.

| Class | Meaning | Count |
|---|---|---|
| INCONSISTENT | Refuted in Rocq from model + stdlib axioms alone (or implies `False` given any `Mode`). Admitting it makes the development inconsistent. | 43 (8 in cone) |
| CONTRADICTS-ADMITTED | Refuted only together with other admits/stubs: jointly inconsistent. | 8 (2 in cone) |
| FALSE-IN-INTENDED-MODEL | Not refutable from the axioms, but false under the intended reading (e.g. two distinct modes, intended stub definition). | 11 (6 in cone) |
| FALSE-ARGUED | False by a rigorous paper argument; not mechanised. | 6 (2 in cone) |
| NEEDS-HYPOTHESIS | False as stated in degenerate models; true with a named extra hypothesis. | 4 (0 in cone) |
| BLOCKED-ON-STUB | Unprovable while a `Parameter` stub is opaque; true under the suggested definition (§6). | 17 (9 in cone) |
| BLOCKED-ON-DEFINITION | Needs a definition change, or rests on an inconsistent lemma (a conditional proof exists). | 4 (2 in cone) |
| NOT-AUDITED | Late cloud write-ups (NARNonFS_currSince, NAR-small); prover verdict only. | 15 (2 in cone) |

"INCONSISTENT" lemmas are the dangerous ones: admitting one lets you prove `False`. The harness rejects any proof that depends on one, and the PR holds back such proofs, so no **new** proof in this PR rests on them. Pre-existing `Qed` results still do: `safety` itself (§3), and for example `SoftwareLanguage.delAddSoft`, which goes through `delProc_minus_guard`. The audited list and the compiled evidence are in [`…-evidence/`](2026-10-14-proof-completion-pass-1-evidence/README.md).

### 4.3 Held-back proofs

These 25 proofs compile, but they rest on at least one admitted lemma from the audited inconsistent list. They are **not** merged; their proof scripts are in [`…-evidence/held-back/`](2026-10-14-proof-completion-pass-1-evidence/held-back/). Once the lemmas they depend on are fixed, they can be re-checked and merged in pass 2.

| Target | Inconsistent dependencies |
|---|---|
| `EntAuxResults.abortOvlpStateEnt_urgent` | `reachableProt_triple` |
| `EntAuxResults.del_listening` | `paused_switch`, `reachableProt_triple` |
| `EntAuxResults.del_listening_pre` | `reachableProt_triple` |
| `EntAuxResults.del_ovlp` | `reachableProt_triple` |
| `EntAuxResults.tfsStart_next_ent` | `tfsStart_next` |
| `EntityLanguage.timeSplit_ent` | `delProc_minus_guard` |
| `NARIncomp.incomp_tfs` | `currComp_listening_track_ent`, `currComp_next`, `currComp_nextPincCheck_track_ent`, `gotMessage_next`, `gotMsgStateEnt_urgent`, `gotMsg_state`, `gotRange_currPincCheck_track_ent`, `gotRange_next`, `inList_pres_input`, `msgAbort_modeState_eq`, `msgBadPathNet_urgent`, `ovWait_del_pres`, `reachableProt_triple`, `switchBc_nextMode_net` |
| `NARInsuff.nextSince_next` | `ovWait_del_pres`, `switchBc_nextMode_net` |
| `NARInsuff.notifAbort_not_nextSince` | `currOK_listening_track`, `nextEq_mode`, `nextMode_ent_mState`, `notifAbort_modeState_eq`, `reachableProt_triple` |
| `NARMisc.currModeNet_switch_states` | `mState_switch_states` |
| `NARMisc.nextSince_ovReaddy_modeEq` | `ovReady_del_pres_bkwd_net`, `ovReady_prev_net` |
| `NARMisc.nextSince_ovWait_modeEq` | `mState_switch_states`, `nextMode_ent_mState`, `switchBc_nextMode_net` |
| `NARMisc.nextSince_switchBc_modeEq` | `mState_switch_states`, `nextMode_ent_mState`, `switchBc_nextMode_net` |
| `NARMisc.ovWait_nextSince_time` | `ovWait_del_pres`, `ovWait_del_pres_bkwd_net_strong`, `ovWait_prev_net` |
| `NARMisc.tfsNext_tfs_mode_eq` | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `mState_switch_states`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| `NARMisc.tfsNext_tfs_zero` | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| `NARMisc.tfsStart_tfs_zero` | `del_pres_bkwd_tfsStart`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| `NARMisc.tfs_bound` | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `mState_switch_states`, `reachableProt_triple`, `tfsCurrStateNet_bktrk_net`, `tfsCurrState_del_pres_net`, `tfsListen_paused`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net`, `transGuard_del` |
| `NARMisc.tfs_rel_state` | `tfsState_del_pres_net` |
| `NARTop.ovWait_del_pres_bkwd_net_strong` | `ovWait_del_pres_bkwd_net_strong` |
| `NetAuxBasics.del_listening_net` | `reachableProt_triple` |
| `NetAuxBasics.del_pres_bkwd_tfsNext` | `del_pres_bkwd_tfsNext`, `tfsState_del_pres_net` |
| `NetAuxBasics.ovReady_prev_net` | `ovReady_prev_net`, `ovReady_prev_net_strong` |
| `NetAuxBasics.ovWait_ovReady_nextMode_net` | `init_nextMode_net`, `ovReady_del_pres_bkwd_net`, `ovReady_prev_net_strong`, `ovWait_del_pres_bkwd_net_strong`, `ovWait_prev_net_strong` |
| `NetAuxBasics.paused_switch_net` | `paused_switch` |

## 5. Root causes and proposed fixes

These cover almost every failure. They are ranked by impact on `safety`. Each fix is a 🧑 decision.

1. **Incomplete component-state predicates** (`overlapState`, `listenerState` marked INCOMPLETE). This makes `reachableProt_triple` false and in the cone, and it poisons every lemma that leans on it.
   - **Fix (validated):** define each component predicate as "reachable from that component's initial process", e.g. `overlapState := compReach dormant`. A prover proved `reachableProt_triple` under this definition (`reachableProt_triple_fix`, in [`…-evidence/fixes/`](2026-10-14-proof-completion-pass-1-evidence/fixes/)).
2. **Missing reachability hypotheses.** This is the most frequent cause.
   - State predicates are bisimilarity classes, so an unreachable term (`del 1 X`, a `nilProc` component, a bare `chanPos?` prefix) satisfies them and breaks backtracking, delay-preservation and urgency lemmas.
   - **Fix:** add `reachableNet n` / `reachableProt p` / `reachableEnt e`. In almost every case the callers already have that hypothesis in scope.
3. **Untyped process inputs.** A process can input a `Time` on a channel meant for a `Mode`, which reaches stuck states, so the forward-tracking `*_next` lemmas are false. Thesis Remark 4.1 deliberately leaves channels untyped.
   - **Fix:** channel sorts (arities and types), or a well-typed-input hypothesis on these lemmas.
4. **Listener notification arity (also in the thesis).**
   - The interface delivers notifications `⟨r, m, l⟩`, as in IFWD-OUT and Remark 4.15, but `listening` inputs `chanAN⟨r, m''⟩` (thesis p.134). By PFX-IN-MSG (|~v| = |~x|) it can never consume a real notification, so the coverage-degradation → `rangeBad` safety mechanism is dead.
   - `listening_AN_prot` (in the cone) is false.
   - **Fix:** `chanAN⟨r, m'', l'⟩?`. The proof script for the 3-field version is ready.
5. **Range typing (`eSubtract` vs `bPossInc`).** `gotMsg` computes the range with `eSubtract`, which yields a `baseNonneg`, but `bPossInc` only evaluates on a `baseDistance`. So after handling any message the listener gets stuck at `currPincCheck`, and the incompatibility-detection path never reaches `badOvlp`.
   - **Fix:** make `bPossInc` accept any non-negative value, or convert in `gotMsg`.
6. **`noSyncNow` is missing the thesis's no-position-read clause (Def 4.22).** An entity whose process can read its position on `chanPos` can still delay. So `gotMsg`, `pending` and `ovWait(y=0)` are not urgent, and several urgency lemmas are false.
   - **Fix:** restore the clause in `noSyncNow`/`stepTeDel`. This was checked against a local copy: `gotMsgStateEnt_urgent` then proves in a few lines.
7. **`stepDeTest` changes the mode state without the process.** It models an environment mode request, and it breaks the four `NetAuxDefs.*_modeState_eq` lemmas and `mState_switch_states`.
   - **Fix:** weaken those lemmas to "k preserved, or the process is unchanged and k was stable", and adjust the two callers. Alternatively re-model mode requests.
8. **Missing WRITE-STBL rule (in the thesis, not in `stepDiscEnt`).** Process `chanMStable!` never synchronises with the mode state, so `ovAbort` and the `tfsNext` self-loop can never abort a transition.
   - **Fix:** add the rule.
9. **Internal synchronisation on mode-state channels.** Components can synchronise with each other on `chanMNext`/`chanMStable` and bypass the mode state, which breaks `currComp`/`currOK` tracking.
   - **Fix:** add a `~ modeStateChan c` premise to `stepDpSyncLR`/`stepDpSyncRL`.
10. **Parameter tracking under bisimulation.** With truncated subtraction, `ovWait m t x y ~p~ ovWait m t' x y` whenever both `t, t' <= period m`, so lemmas asserting `t = t'` are false.
    - **Fix:** weaken those conclusions to what callers use (usually `m = m'` and `y = period m`).
11. **Gaps in the model axioms.** Nothing forbids `failSafeSucc m = m`, `modeTransTime = 0`, or a one-element `Mode`.
    - **Fix:** add `failSafeSucc m <> m` (and maybe `0 < modeTransTime`), or add `~ failSafe m` hypotheses where needed.
12. **Small statement bugs.**
    - `nextModeEnt_not_stable` has `m2 : ModeState` where `Mode` was meant, which makes it say "never".
    - `delProc_minus_guard` lacks `evalExpFunTime e = Some t`. It underlies the already-`Qed` `delAddSoft`, and through it `timeSplit_ent` / `timeSplit_net`.
    - `outgoing_timeout_disc` quantifies the position universally.
    - `evalBoolExpFalseTot` fails on ill-formed expressions.

## 6. `Parameter` stubs: suggested completions (not applied)

| Stub | Suggested definition | Effect |
|---|---|---|
| `reachableEnt` (EntAuxDefs) | Inductive closure of `initialEnt` under discrete and delay entity steps. Move it below `initialEnt`. | `reachable_net_ent`, `reachable_ent_prot` and others become provable (checked in explore mode). |
| `currModeNet m i n` (NetAuxBasics) | `exists e, e @ i .: n /\ currModeEnt e = m`, or `liftEntNet (fun e => currModeEnt e = m)`. | `currMode_intro`, `currMode_pres_*`, `currMode_ent_ex` and `currModeNet_del_pres` prove; several were checked. |
| `nextModeNet m i n` | `liftEntNet (nextModeEnt m)` | `nextMode_ent_ex`, `nextModeNet_del_pres`. |
| `nextModeEnt m e` (EntAuxDefs) | One-constructor inductive over `<| m0, m, t |>`, or `EntityLanguage.nextModeEnt e = Some m`. These were proved equivalent. | `nextMode_ent_mState` and others. |
| `inPosEnt l e` | One-constructor inductive: `[|p, l, h, k|]` is at `l`. | `inPos_ent_net` becomes a one-liner. |

## 7. Model axioms

`src/ModelConsistency.v` (merged) defines:
- `ComhModel`, one field per axiom;
- `global_model`, which shows the global axioms are an instance of it;
- `concrete_model`, an axiom-free instance with a fail-safe mode `Safe` and a non-fail-safe mode `Moving` that must keep distance 1 from each other.

`Print Assumptions concrete_model` lists only the stdlib reals' own axioms, so the 28 axioms are jointly satisfiable and the model is non-degenerate.

**Proposal (🧑, not implemented): package the axioms as a `Module Type`.**
- Turn `ComhBasics`'s axioms into `Module Type ComhParams`, and make each downstream file a functor over it (or put the whole development in one `Section` with the parameters as variables).
- `safety` would then read "for every valid instantiation", and `ModelConsistency.concrete_model` becomes the witness instantiation.
- **Cost:** mechanical but broad. 22 of the source files reference these parameters.
- **Risk:** functor boilerplate, plus notation scoping across functor boundaries.
- A lighter variant is to keep the global axioms and just state the relationship via `global_model`, as now.

## 8. Reals clean-up notes (merged)

- **Removal candidates** (🧑): project lemmas that duplicate stdlib ones (`not_Rle_lt` = `Rnot_le_lt`, `RltMinusBothSides` = `Rlt_Rminus`, `Rle_zero_plus` = `Rplus_le_le_0_compat`, `Rmult_lt_0` = `Rmult_lt_0_compat`, …), and about 30 lemmas that are now one-line `lra` facts.
- **Naming hazard:** the project's `Rplus_lt_reg_l`/`_r` shadow the stdlib lemmas of the same names with the sides swapped.
- Nothing needed the mathcomp `Rstruct` bridge (see the ADR).

## 9. Decisions needed (🧑)

1. Approve or adjust the definition fixes in §5 (1, 4, 5, 6, 7, 8, 9). Fixes 1 and 4 matter most.
2. Approve the statement fixes, mainly the added reachability hypotheses (§5.2) and the small bugs (§5.12). The appendix gives the exact corrected statement for each.
3. Choose the stub completions (§6).
4. Model-axiom additions (§5.11) and the `Module Type` refactor (§7).
5. Removal candidates (§8), and whether to delete unused false lemmas rather than fix them. Several have no users.

After that, **pass 2** applies the approved changes and re-runs the fan-out on the affected lemmas. Many already have conditional proofs waiting: the 25 held-back proofs, and the cloud provers' conditional proofs listed in [`…-evidence/conditional/`](2026-10-14-proof-completion-pass-1-evidence/conditional/).

## 10. Method and trust

- **Harness.** Each target was proved in a copy of its module truncated just after it, compiled against a frozen build. A target may use earlier lemmas, including other admits. The harness rejects:
  - `Admitted`, `admit`, new axioms and similar escapes;
  - statement changes;
  - any proof whose `Print Assumptions` includes a known-inconsistent lemma.
- **Integration.** All accepted proofs are spliced into the real sources, and the whole project is rebuilt from clean (CI does the same).
- **Proved relative to the remaining admits.** A merged proof can still depend on admitted lemmas that are false but not inconsistent. Such proofs are valid reductions, but you should read them as conditional on those lemmas being fixed. `make assumptions` shows what remains.
- **Parallelism and logistics:**
  - Up to 20 local subagents (the environment's cap), plus 5 cloud sessions for the overflow, using work-stealing over a shared claim queue.
  - Three auditors re-verified every claimed counterexample in the 93 audited write-ups. None failed to compile, and they corrected several verdicts in both directions.
  - The first run was cut short by an account usage limit and relaunched the next morning, with an hourly watchdog to survive further limits.
- **Not independently audited:** write-ups from the last two cloud sessions (NARNonFS_currSince, NAR-small), which arrived after the audit started. They are marked as such in the appendix.
