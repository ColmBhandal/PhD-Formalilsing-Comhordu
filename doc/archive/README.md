# Archive

Historical documents, kept for reference. They are **not maintained** and may contradict the current code.

| File | What it is |
|---|---|
| [`2015-05-08-coq-project-plan.pdf`](2015-05-08-coq-project-plan.pdf) | *"Comhordú in Coq: Documentation and Project Plan"* (8 May 2015). Statistics of the Coq model at the time, the `Admitted. (*label*)` taxonomy, a plan towards completion, coding guidelines and possible extensions. Previously at the repo root as `coq_proj.pdf`. |

**Superseded** on 2026-10-13 by the Rocq upgrade and proof completion workstream, an ephemeral tracker. What still held of the 2015 plan, and what was dropped and why, is below.

## Carried over from the 2015 plan

Each item of the 2015 plan was checked against `src/` and current Rocq tooling on 2026-10-13, when the Rocq upgrade and proof completion workstream started, and only what still held is kept. Step and phase numbers refer to that workstream's plan as it stood then.

### 1 Admitted labels (still in use)

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

### 2 Other guidance carried over

| 2015 item | Status now |
|---|---|
| §3.1 Tactic development per `#tag` | **Kept**, folded into step 7. Prove one lemma interactively, factor its proof into a tactic that doesn't depend on hypothesis names or order, then apply it to the rest of the group. Reuse what exists: `state_pred_elim` (`GenTacs.v`), `state_pred_elim_net`, `fwd_track_net_tac`, `backtrack_net_pre`, `initNet_contra` (`NetAuxBasics.v`), `backtrack_pre`/`_post`/`_weed`, `fwd_track_pre`, `link_partripout_tac` (`ProtAuxResults.v`). A new shared tactic goes to the lead to splice in, because provers don't edit `src/`. |
| In-file proof sketches | **Kept.** There are ~170 `(*Proof: …*)` comments next to lemmas. Read them before proving. |
| §3.2 "Garbage collection" of unneeded admits | **Kept** as a Phase 5 🧑 decision. It is now mechanical: `Print Assumptions safety` shows which admits are actually used. |
| §4 "General survey": recount what's left, revise the plan | **Kept**, now automated: the CI assumption report (step 4) plus this tracker's Log. |
| §4 "Tidying": recompile after moving code | **Kept.** The lead rebuilds after every splice (step 7). |
| §5 Axiom soundness check | **Kept** as Phase 2 step 6. It is a relative-consistency proof by building a model inside Rocq, so the 2015 doc's Gödel worry doesn't apply: we are not proving Rocq's own consistency. |
| §5 Show that an unsafe state is reachable without the protocol | **Kept** as a Phase 5 🧑 decision. |
| §1 Category definitions (Parameter = stub, Axiom = deliberately uninterpreted, Conjecture = assumed as "obvious") | **Kept.** |

### 3 Dropped, and why

| 2015 item | Why it was dropped |
|---|---|
| Table 1 (statistics) and Table 2 (label counts) | **Stale.** A.1 has the counts as of 2026-10-13. Then vs now: lines 13,459 → ~15.6k; `Admitted` 226 → 228; Conjecture, Axiom and Parameter unchanged at 28/28/5; proved (`Qed`/`Defined`) 693 → 679; Definitions 259 → 259; Inductives 92 → 89; `Ltac` 225 → 221. |
| "Conjectures are not a priority", "`R` proofs are not a priority" | **Superseded.** Both are in scope in step 7. |
| §3.2 Lemma/Theorem demotion and promotion, renaming, statement standardisation, explicit typing, re-documenting | **Out of scope.** These are cosmetic. They would churn the diff and conflict with serial splicing. They could be revisited later as a 🧑 call. |
| §4 Find and replace with Notepad++; "Coq search can't match part of a name" | **Obsolete.** Use `grep`/`rg`. Rocq's `Search "fragment"` matches name substrings. |
| §4 Researching via the Coq website and the Coq-Club mailing list | **Obsolete pointers.** Use the Rocq reference manual and the Rocq Zulip and Discourse. |
| §4 "Use tactics" (generic) | **Replaced.** The 2015 doc names no specific tactics, and the code never used `omega`/`fourier` (0 hits). Real-number reasoning was done with hand-rolled lemmas (`RInequalities.v`, `StandardResults.v`). The modern answer is `lra`/`nra`/`Psatz` on `rocq-stdlib`, per the [ADR](../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md). `elimtype`, used in the vendored LibTactics, is gone in Rocq 9. |
