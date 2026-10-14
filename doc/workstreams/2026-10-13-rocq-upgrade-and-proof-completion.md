# Workstream: Rocq upgrade & proof completion

| | |
|---|---|
| **Started** | 2026-10-13 |
| **Status** | 🧑 Phase 5: one fix per PR, starting with step 12 |
| **Branch** | One per PR |
| **Goal** | Port the Comhordú formalisation to **Rocq 9.2.0**, then close every assumption under `safety` that can be closed, and write up the ones that can't. |
| **Supersedes** | [2015 project plan](../archive/2015-05-08-coq-project-plan.pdf). What was carried over is in the [Appendix](#appendix-carried-over-from-the-2015-plan). |

**Legend:** 🤖 Agent · 🧑 Human-in-the-loop · ✅ / `[x]` done · `[ ]` to do

## Starting point (2026-10-13)

| Item | Count | Where |
|---|---|---|
| Lines of Rocq | ~15.6k | 25 files in `src/`, plus 4.1k vendored `src/Extras/LibTactics.v` |
| `Admitted` | 228 | 17 files; most in `ProtAuxResults.v` (56), `NetAuxBasics.v` (53), `EntAuxResults.v` (33), `NARMisc.v` (31) |
| `Conjecture` | 28 | `NetAuxBasics.v` 23, `InterfaceLanguage.v` 3, `EntityLanguage.v` 2 |
| `Axiom` | 28 | `ComhBasics.v`: the abstract model parameters, unprovable by design |
| `Parameter` (stubs) | 5 | `EntAuxDefs.v` 3 (`reachableEnt`, `nextModeEnt`, `inPosEnt`), `NetAuxBasics.v` 2 (`currModeNet`, `nextModeNet`) |
| Top-level result | `safety` | `src/Main.v`: `Theorem safety (n : Network) : reachableNet n -> safe n.` |

## Conventions

The rules live in `AGENTS.md` files, each in the directory it governs: [`doc/`](../AGENTS.md), [`workstreams/`](AGENTS.md), [`reports/`](../reports/AGENTS.md), [`adr/`](../adr/AGENTS.md), [`archive/`](../archive/AGENTS.md); the top-level and `src/` ones cover the code.

---

## Phase 0: Docs scaffolding

- [x] 🤖 **0.1 Archive and scaffolding.** ✅ 2026-10-13. Moved `coq_proj.pdf` to `doc/archive/2015-05-08-coq-project-plan.pdf` and checked it against the code and current tooling ([Appendix](#appendix-carried-over-from-the-2015-plan)). Created `doc/{workstreams,reports,adr,archive}` with an `AGENTS.md` in `doc/` and in each subfolder, this tracker and the [reals ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md). Added a "Project docs" section to README.

## Phase 1: Upgrade (🤖 agent only)

- [x] 🤖 **1. Baseline.** ✅ The unchanged code builds on **Coq 8.15** (the last known toolchain, ~2022): all 26 files compile cleanly. The same code on **Rocq 9.2.0** fails immediately in `src/Extras/LibTactics.v`, because `elimtype` was removed.
- [x] 🤖 **2. Upgrade to Rocq 9.2.0 + `rocq-stdlib`.** ✅ 2026-10-13. 9.2.0 is the latest stable release (9.3 is only at rc1). Changes:
  - LibTactics: removed tactic forms replaced (`elimtype`, bare `instantiate`, and a `Variable` declared outside a section).
  - All stdlib imports now use explicit `From Stdlib …`, plus `Arith` wherever `Reals` is exported (8.15's `Reals` re-exported it).
  - A handful of removed Arith lemma names mapped to their `Nat.*` equivalents; trivial nat helper proofs replaced by `lia`.
  - Tooling moved to the standard layout: `rocq makefile` Makefile, `rocq-comhordu.opam`, `rocq doc`.
  - **No proof broke**, so there are no `UPGRADE-BROKEN` admits. `Print Assumptions safety` is **identical** before and after the upgrade (134 entries on both 8.15 and 9.2).
- [x] 🤖 **3. Modernise real-number reasoning on the stdlib.** ✅ 2026-10-14. 58 hand-rolled inequality proofs replaced by `lra`/`nra`; statements unchanged; trust base byte-identical. Removal candidates are in the [report](../reports/2026-10-14-proof-completion-pass-1/what-changed.md#reals-clean-up-notes). Nothing needed the `Rstruct` bridge.
- [x] 🤖 **4. CI.** ✅ 2026-10-13. `.github/workflows/build.yml` runs on `rocq/rocq-prover:9.2.0`: it builds everything and writes `make assumptions` (`helper-scripts/summarise_assumptions.py`) to the job summary.
- [x] 🤖 **5. Gate.** ✅ 2026-10-13. Clean `make` is green on Rocq 9.2.0 (26 files, about 40s on 4 cores). Baseline for the fan-out: `safety` rests on 134 assumptions = **100 unproved project lemmas** + 4 `Parameter` stubs + 25 model axioms + 5 stdlib axioms.

## Phase 2: Model axioms (🤖)

- [x] 🤖 **6. Show the axioms are consistent.** ✅ 2026-10-13. `src/ModelConsistency.v` gives an axiom-free, non-degenerate model: a fail-safe and a moving mode, with positive separation. The `Module Type` proposal is in the [report](../reports/2026-10-14-proof-completion-pass-1/what-changed.md#model-axioms-are-consistent).

## Phase 3: Proof fan-out (🤖, ~24 parallel provers)

- [x] 🤖 **7. Prove everything as stated.** ✅ 2026-10-14.
  - All 256 targets were attempted: 123 proved and merged, 25 proved but held back, 108 written up.
  - About 20 local provers plus 5 cloud sessions, with work-stealing and an hourly watchdog for usage limits.
  - Three auditors recompiled every claimed counterexample.
  - See the [report](../reports/2026-10-14-proof-completion-pass-1/README.md).
- [x] 🤖 **8. Write up each lemma that won't go through as written.** ✅ All 108 are in the report's [lemma index](../reports/2026-10-14-proof-completion-pass-1/lemmas/README.md), audited where marked. **Finding: `safety` is currently vacuous.** Admitted lemmas inconsistent with the model axioms sit in its cone ([why](../reports/2026-10-14-proof-completion-pass-1/why-safety-is-vacuous.md)).
- [x] 🤖 **9. `Parameter` stubs.** ✅ Suggested completions are in the [report](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#parameter-stubs) and are not applied.

## Phase 4: Review (🤖 then 🧑)

- [x] 🤖 **10. Report and PR.** ✅ 2026-10-14. [Report](../reports/2026-10-14-proof-completion-pass-1/README.md) written; branch pushed; PR opened.
- [x] 🧑 **11. Review** the PR and the report. ✅ 2026-10-14. Reviewed and merged in [#1](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/1).

## Phase 5: Decide and fix, one PR at a time (🧑 then 🤖)

This phase runs as a loop: pick an item, agree the fix, open a PR, review and merge, repeat. Each PR applies its fix and re-proves what the fix unblocks, including pass 1's held-back and conditional proofs. The order below makes `safety` meaningful soonest, but it is a suggestion, not a rule.

- [ ] 🧑 **12. Listener arity** ([root cause 4](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis)). Fixes `listening_AN_prot`. The fix departs from the thesis (p.134).
- [ ] 🧑 **13. Component-state predicates** ([root cause 1](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#1-incomplete-component-state-predicates)). Fixes `reachableProt_triple`, the most structural problem.
- [ ] 🧑 **14. Quick fixes in the cone:** `link_ent_outList` and `outgoing_timeout_disc` ([root cause 12](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#12-small-statement-bugs)), and `ovWait_del_pres` ([root cause 10](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#10-parameter-tracking-under-bisimulation)).
- [ ] 🧑 **15. Reachability hypotheses and `noSyncNow`** ([root causes 2](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#2-missing-reachability-hypotheses) and [6](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#6-nosyncnow-is-missing-the-thesiss-position-read-clause)).
- [ ] 🧑 **16. `Parameter` stubs** ([suggestions](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#parameter-stubs)), then add `reachableNet n` to `tfsListen_failSafe_net`. This breaks the [pair that makes `safety` trivial](../reports/2026-10-14-proof-completion-pass-1/why-safety-is-vacuous.md#2-a-pair-that-makes-safety-trivial).

Steps 12–16 cover every known reason `safety` is vacuous today. After that, any order works.

- [ ] 🧑 **17. Other statement changes** for lemmas found false or mis-stated in step 8: the rest of root causes [10](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#10-parameter-tracking-under-bisimulation) and [12](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#12-small-statement-bugs), and the [model-axiom gaps](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#11-gaps-in-the-model-axioms). Corrected statements are in the [lemma write-ups](../reports/2026-10-14-proof-completion-pass-1/lemmas/README.md).
- [ ] 🧑 **18. Semantics fixes outside the cone:** root causes [3](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#3-untyped-process-inputs), [5](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#5-range-typing-esubtract-vs-bpossinc), [7](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#7-stepdetest-changes-the-mode-state-without-the-process), [8](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#8-missing-write-stbl-rule) and [9](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#9-internal-synchronisation-on-mode-state-channels).
- [ ] 🧑 **19. Garbage collection.** Decide whether to delete admitted lemmas **outside** the `Print Assumptions safety` cone rather than prove them, as the 2015 plan suggested. Best done just before pass 2, so the provers skip anything that will go.
- [ ] 🤖 **20. Pass 2.** Re-run the fan-out on whatever is still unproved.
- [ ] 🧑 **21. `Module Type` refactor** of the model axioms (from step 6). It touches 22 files, so it is easier after pass 2.
- [ ] 🧑 **22. Non-triviality.** Decide whether to prove that, without the protocol, an unsafe state is reachable. This is a 2015 "future extension".
- [ ] 🧑 _Placeholder: anything else the first pass couldn't decide._

## Log

- **2026-10-14:** Pass 1 reviewed and merged. Phase 5 reordered and set up as a one-fix-per-PR loop.
- **2026-10-14:** Pass 1 complete. 123 targets proved, 25 held back, 108 written up and audited. `Print Assumptions safety` went from 134 to 85, but `safety` is vacuous until the inconsistent admits are fixed. Reals modernised. PR opened for review.
- **2026-10-13:** Upgrade to Rocq 9.2.0 done with no broken proofs; assumption set unchanged. Standard tooling and CI added. Rules moved into `AGENTS.md` files.
- **2026-10-13:** Workstream started. Coq 8.15 baseline is green; Rocq 9.2.0 breaks on `elimtype`. Reals [ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md) accepted: option (c), stdlib reals with the `Rstruct` bridge. 2015 plan archived.

---

## Appendix: Carried over from the 2015 plan

Source: [`doc/archive/2015-05-08-coq-project-plan.pdf`](../archive/2015-05-08-coq-project-plan.pdf), *"Comhordú in Coq: Documentation and Project Plan"*, 8 May 2015. Each item was checked against `src/` and current Rocq tooling on 2026-10-13, and only what still holds is kept.

### A.1 Admitted labels (still in use)

The convention is still live in the code: **173 of the 228** live `Admitted` carry a trailing `(*label*)` comment. They are useful hints, but the 2015 counts are stale.

| Label | Meaning (2015) | 2015 | Now | How to use it now |
|---|---|---|---|---|
| `C` | The statement must change first, usually by adding a hypothesis. | 3 | 4 | Expect a step-8 write-up rather than a proof. The comment next to it often names the fix. |
| `D- X` | Depends on `X` being proved or defined first. | 4 | 13 | 7 × `D- reachableEnt` are blocked on a `Parameter` stub (step 9). `D- rangeBad_next_ent` and `D- badOvlp_next_ent` name entity-level lemmas that **don't exist**, so the prover must create them; the process-level `rangeBad_next`/`badOvlp_next` in `ProtAuxResults.v` exist. The other 4 are bare `D`. |
| `R` | The proof predates the switch to bisimulation-based state predicates. The old proof is **commented out just above** the `Admitted`. | 13 | 13 | Start from the commented-out proof and adapt it. `state_pred_elim` still exists (`GenTacs.v`). |
| `#tag` | A category of similar proofs that one shared tactic could solve. | 45 | 45 | Give a whole tag group to one prover chunk (see A.2). Main tags: `#fwd-track` (8), `#complexNetLift` (8), `#lift-track-net` (6), `#tfsNetLift`, `#fwd-track-lift-ent` (5 each), `#state-pred-elim`, `#delay-pres` (4 each), `#timeSplit-timedList` (3). |
| `1`–`10` | Estimated difficulty. **1 = hardest, 10 = easiest.** | 162 | 98 | For sizing chunks. Today's spread: 1:8, 2:7, 3:15, 4:20, 5:16, 6:22, 7:9, 9:1. Rough 2015 sizing: levels 1–3 take about 100–200 lines and 5–10 auxiliary lemmas; 4–6 take about 5 auxiliary lemmas; 7–10 are routine. |
| *(none)* | | | 55 | Triage from scratch. |

> **Counting gotcha:** `grep -c 'Admitted\.'` happens to give the right total (228), but only because two errors cancel. It **misses** `Admitted (*9*).` at `NARNonFS_currSince.v:27`, and it **counts** an `Admitted.` inside a commented-out block at `NARNonFS_currSince.v:76`. Count outside comments.

### A.2 Other guidance carried over

| 2015 item | Status now |
|---|---|
| §3.1 Tactic development per `#tag` | **Kept**, folded into step 7. Prove one lemma interactively, factor its proof into a tactic that doesn't depend on hypothesis names or order, then apply it to the rest of the group. Reuse what exists: `state_pred_elim` (`GenTacs.v`), `state_pred_elim_net`, `fwd_track_net_tac`, `backtrack_net_pre`, `initNet_contra` (`NetAuxBasics.v`), `backtrack_pre`/`_post`/`_weed`, `fwd_track_pre`, `link_partripout_tac` (`ProtAuxResults.v`). A new shared tactic goes to the lead to splice in, because provers don't edit `src/`. |
| In-file proof sketches | **Kept.** There are ~170 `(*Proof: …*)` comments next to lemmas. Read them before proving. |
| §3.2 "Garbage collection" of unneeded admits | **Kept** as a Phase 5 🧑 decision. It is now mechanical: `Print Assumptions safety` shows which admits are actually used. |
| §4 "General survey": recount what's left, revise the plan | **Kept**, now automated: the CI assumption report (step 4) plus this tracker's Log. |
| §4 "Tidying": recompile after moving code | **Kept.** The lead rebuilds after every splice (step 7). |
| §5 Axiom soundness check | **Kept** as Phase 2 step 6. It is a relative-consistency proof by building a model inside Rocq, so the 2015 doc's Gödel worry doesn't apply: we are not proving Rocq's own consistency. |
| §5 Show that an unsafe state is reachable without the protocol | **Kept** as a Phase 5 🧑 decision. |
| §1 Category definitions (Parameter = stub, Axiom = deliberately uninterpreted, Conjecture = assumed as "obvious") | **Kept** in [Starting point](#starting-point-2026-10-13). |

### A.3 Dropped, and why

| 2015 item | Why it was dropped |
|---|---|
| Table 1 (statistics) and Table 2 (label counts) | **Stale.** Replaced by [Starting point](#starting-point-2026-10-13) and A.1. Then vs now: lines 13,459 → ~15.6k; `Admitted` 226 → 228; Conjecture, Axiom and Parameter unchanged at 28/28/5; proved (`Qed`/`Defined`) 693 → 679; Definitions 259 → 259; Inductives 92 → 89; `Ltac` 225 → 221. |
| "Conjectures are not a priority", "`R` proofs are not a priority" | **Superseded.** Both are in scope in step 7. |
| §3.2 Lemma/Theorem demotion and promotion, renaming, statement standardisation, explicit typing, re-documenting | **Out of scope.** These are cosmetic. They would churn the diff and conflict with serial splicing. They could be revisited later as a 🧑 call. |
| §4 Find and replace with Notepad++; "Coq search can't match part of a name" | **Obsolete.** Use `grep`/`rg`. Rocq's `Search "fragment"` matches name substrings. |
| §4 Researching via the Coq website and the Coq-Club mailing list | **Obsolete pointers.** Use the Rocq reference manual and the Rocq Zulip and Discourse. |
| §4 "Use tactics" (generic) | **Replaced.** The 2015 doc names no specific tactics, and the code never used `omega`/`fourier` (0 hits). Real-number reasoning was done with hand-rolled lemmas (`RInequalities.v`, `StandardResults.v`). The modern answer is `lra`/`nra`/`Psatz` on `rocq-stdlib`, per the [ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md). `elimtype`, used in the vendored LibTactics, is gone in Rocq 9. |
