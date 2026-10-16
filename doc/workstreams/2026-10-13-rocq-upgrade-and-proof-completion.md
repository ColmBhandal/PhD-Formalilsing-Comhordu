# Workstream: Rocq upgrade & proof completion

| | |
|---|---|
| **Started** | 2026-10-13 |
| **Status** | 🧑 Phase 5: step 17 in review |
| **Branch** | One per PR |
| **Goal** | Port the Comhordú formalisation to **Rocq 9.2.0**, then close every assumption under `safety` that can be closed, and write up the ones that can't. |
| **Supersedes** | [2015 project plan](../archive/2015-05-08-coq-project-plan.pdf). What was carried over is in [`doc/archive/README.md`](../archive/README.md). |

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

The rules live in `AGENTS.md` files, each in the directory it governs: [`doc/`](../AGENTS.md), [`workstreams/`](AGENTS.md), [`reports/`](../reports/AGENTS.md), [`adr/`](../adr/AGENTS.md), [`archive/`](../archive/AGENTS.md); the top-level and `src/**` ones cover the code.

---

## Phase 0: Docs scaffolding

- [x] 🤖 **0.1 Archive and scaffolding.** ✅ 2026-10-13. Moved `coq_proj.pdf` to `doc/archive/2015-05-08-coq-project-plan.pdf` and checked it against the code and current tooling ([`doc/archive/README.md`](../archive/README.md)). Created `doc/{workstreams,reports,adr,archive}` with an `AGENTS.md` in `doc/` and in each subfolder, this tracker and the [reals ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md). Added a "Project docs" section to README.

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

This phase runs as a loop: pick an item, agree the fix, open a PR, review and merge, repeat. Each PR applies its fix and re-proves what the fix unblocks, including pass 1's held-back and conditional proofs. Any departure from the thesis goes in [`thesis-corrections.md`](../thesis/thesis-corrections.md) in the same PR. From step 18 on, each PR also refactors as it goes: it moves language-generic content into `lang/` wherever it can and simplifies the protocol proofs with it, while the statement of `safety` stays the same. The order below is a suggestion, not a rule: it separates the language from the protocol first, then makes `safety` meaningful as soon as possible.

- [x] 🧑 **12. Listener arity** ([root cause 4](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis)). ✅ 2026-10-14. The listener now reads all 3 notification fields, a [thesis correction](../thesis/thesis-corrections.md#1-the-listener-reads-too-few-fields-from-a-notification). `listening_AN_prot` is proved. `incomingNetNotif_del` gains a length hypothesis. [#2](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/2).
- [x] 🤖 **13. Make the language generic.** ✅ 2026-10-15. The code built the protocol's process names and their definitions into the language. Now the language takes them as parameters, and its results hold for any guarded definitions, a weaker form of Remark 4.2 (p.69) and a [thesis correction](../thesis/thesis-corrections.md#2-patience-needs-guarded-definitions). `ProtocolBridge.v` proves that the protocol's definitions are guarded. The statement of `safety` and its 84 assumptions are unchanged. The protocol-only channels are left for step 29. [#3](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/3).
- [x] 🤖 **14. Split `src/` into `lib/`, `model/`, `lang/` and `protocol/`.** ✅ 2026-10-15. Each folder depends only on the ones before it, and has a README and its own `AGENTS.md`. `ComhBasics.v` keeps the model, and its general helpers move to `lib/GenBasics.v`. Only code moves: printing every statement and definition before and after shows no change, and `safety` still rests on the same 84 assumptions. [#4](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/4).
- [x] 🤖 **15. Extract language results from the proved results.** ✅ 2026-10-15. Every proved protocol result about the language now rests on a general result in `lang/`: 63 language results added, 63 protocol lemmas removed ([report](../reports/2026-10-15-extract-language-results/README.md)). A few abstractions did most of the work, such as the inversion of a parallel triple's step and the entity's no-synchronisation principle. Every definition and statement that stays is unchanged, checked by `helper-scripts/print_statements.py`, and `safety` still rests on 84 assumptions. The generic network notions defined in `NetAuxBasics.v` move to `lang/` in step 17. [#5](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/5).
- [x] 🤖 **16. N-ary parallel composition.** ✅ 2026-10-15. `parAll p ps` in `lang/SoftwareLanguage.v` computes to the right-nested pairs `$||$` parses to, so the protocol's triples are instances of it and no protocol statement changes. The n-ary results are proved once by induction on the list, with a step at a position as a `stepAt` in `lib/GenBasics.v`. The 28 triple-shaped lemmas are gone ([report](../reports/2026-10-15-n-ary-parallel-composition/README.md)), `net_del_elim` is restated over an entity with no process structure, and the protocol reaches its three components through one tactic, `triple_pos`. `safety` still rests on 84 assumptions. [#6](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/6).
- [x] 🤖 **17. Move the generic network notions to `lang/`.** ✅ 2026-10-16. `inPosNet`, `distNet`, `outgoing`, `incomingNet`, `incomingNetNotif`, `mState_in_net`, `transGuard`, `liftEntNet` and `incomingEnt` are in `lang/` with the 21 proved results about them, every statement unchanged; the unproved results about them wait in the protocol for steps 21 and 22. `outgoing_disc_pres` is re-proved from the language, so the false `link_ent_outList` left the cone and was deleted with approval: `safety` rests on 83 assumptions, down from 84. [#7](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/7).
- [ ] 🧑 **18. Component-state predicates** ([root cause 1](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#1-incomplete-component-state-predicates)). Fixes `reachableProt_triple`, the most structural problem.
- [ ] 🧑 **19. Quick fixes in the cone:** `outgoing_timeout_disc` ([root cause 12](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#12-small-statement-bugs)), and `ovWait_del_pres` ([root cause 10](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#10-parameter-tracking-under-bisimulation)).
- [ ] 🧑 **20. Reachability hypotheses and `noSyncNow`** ([root causes 2](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#2-missing-reachability-hypotheses) and [6](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#6-nosyncnow-is-missing-the-thesiss-position-read-clause)).
- [ ] 🧑 **21. `Parameter` stubs** ([suggestions](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#parameter-stubs)), then add `reachableNet n` to `tfsListen_failSafe_net`. This breaks the [pair that makes `safety` trivial](../reports/2026-10-14-proof-completion-pass-1/why-safety-is-vacuous.md#2-a-pair-that-makes-safety-trivial).

Step 12 and steps 18–21 cover every known reason `safety` is vacuous today. After that, any order works.

- [ ] 🧑 **22. Other statement changes** for lemmas found false or mis-stated in step 8: the rest of root causes [10](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#10-parameter-tracking-under-bisimulation) and [12](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#12-small-statement-bugs), and the [model-axiom gaps](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#11-gaps-in-the-model-axioms). Corrected statements are in the [lemma write-ups](../reports/2026-10-14-proof-completion-pass-1/lemmas/README.md).
- [ ] 🧑 **23. Semantics fixes outside the cone:** root causes [3](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#3-untyped-process-inputs), [5](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#5-range-typing-esubtract-vs-bpossinc), [7](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#7-stepdetest-changes-the-mode-state-without-the-process), [8](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#8-missing-write-stbl-rule) and [9](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#9-internal-synchronisation-on-mode-state-channels).
- [ ] 🧑 **24. Garbage collection.** Decide whether to delete admitted lemmas **outside** the `Print Assumptions safety` cone rather than prove them, as the 2015 plan suggested. Best done just before pass 2, so the provers skip anything that will go.
- [ ] 🤖 **25. Pass 2.** Re-run the fan-out on whatever is still unproved.
- [ ] 🧑 **26. `Module Type` refactor** of the model axioms (from step 6). It touches 22 files, so it is easier after pass 2.
- [ ] 🧑 **27. Non-triviality.** Decide whether to prove that, without the protocol, an unsafe state is reachable. This is a 2015 "future extension".
- [ ] 🧑 **28. Initial interfaces.** Decide whether `initialEnt` should constrain an entity's interface, for example to start empty. Today it allows any contents, which is why step 12 needed a length hypothesis.
- [ ] 🧑 **29. Protocol-only channels.** Decide whether the 5 channels that only the protocol uses (`chanTrans`, `chanWake`, `chanPause`, `chanUnpause` and `chanBad`) should be supplied by the protocol instead of built into the language. The expression operators stay: they wrap the model's functions, so they belong with the model.
- [ ] 🤖 **Delete `parStructPres` and `parStructPres2`** in `lang/SoftwareLanguage.v`: pair-shaped, unused since step 16, and instances of `parAll_disc_weak` and `parAll_del_inv`.
- [ ] 🧑 _Placeholder: anything else the first pass couldn't decide._

## Log

- **2026-10-16:** Process: the PR is the record of a step, and reports are only written when asked for; CI now diffs the statements and the assumptions against the base branch. Agents in sandboxes install Rocq with `helper-scripts/install_rocq.sh`, and nothing specific to one agent or vendor goes in the repository.
- **2026-10-15:** Step 16 done: results about the parallel composition of any number of components replace the triple-shaped lemmas, `net_del_elim` is restated, 84 assumptions as before.
- **2026-10-15:** New step 16: n-ary parallel composition, so that `lang/` states results once for any number of components and the triple-shaped lemmas go. The network-notions move is now step 17, and old steps 17–28 are 18–29.
- **2026-10-15:** New step 16: move the generic network notions in `NetAuxBasics.v` to `lang/`, decided on step 15's report. Old steps 16–27 are now 17–28. Deleting a proved result that a general one replaces is now encouraged by `src/AGENTS.md`.
- **2026-10-15:** Step 15 done: the proved protocol results rest on general language results, 63 protocol lemmas removed for 63 language results, nothing claimed has changed, 84 assumptions as before.
- **2026-10-15:** Step 14 done: `src/` is split into `lib/`, `model/`, `lang/` and `protocol/`, and nothing it claims has changed.
- **2026-10-15:** Step 13 done: the language is generic in its process names and definitions, and `safety` still rests on 84 assumptions.
- **2026-10-15:** Step 14 settled: four folders, adding `lib/` and `model/` to `lang/` and `protocol/`.
- **2026-10-15:** New step 13: make the language generic before splitting `src/`, because the code builds the protocol into the language. Old steps 13–25 are now 14–26.
- **2026-10-14:** Thesis added under [`doc/thesis/`](../thesis/README.md), with a corrections file. Step 12 done: `safety` rests on 84 assumptions, down from 85.
- **2026-10-14:** Pass 1 reviewed and merged. Phase 5 reordered and set up as a one-fix-per-PR loop.
- **2026-10-14:** Pass 1 complete. 123 targets proved, 25 held back, 108 written up and audited. `Print Assumptions safety` went from 134 to 85, but `safety` is vacuous until the inconsistent admits are fixed. Reals modernised. PR opened for review.
- **2026-10-13:** Upgrade to Rocq 9.2.0 done with no broken proofs; assumption set unchanged. Standard tooling and CI added. Rules moved into `AGENTS.md` files.
- **2026-10-13:** Workstream started. Coq 8.15 baseline is green; Rocq 9.2.0 breaks on `elimtype`. Reals [ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md) accepted: option (c), stdlib reals with the `Rstruct` bridge. 2015 plan archived.
