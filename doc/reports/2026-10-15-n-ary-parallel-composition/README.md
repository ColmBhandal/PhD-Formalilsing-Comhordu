# Report: n-ary parallel composition

| | |
|---|---|
| **Date** | 2026-10-15 |
| **Workstream** | [Rocq upgrade & proof completion](../../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md), step 16 |
| **Result** | `src/lang/` states its results about the parallel composition of any number of components once, and the 28 triple-shaped lemmas are gone. `safety` still rests on the same 84 assumptions. |

## What a reader most needs to know

- `parAll p ps`, in `src/lang/SoftwareLanguage.v`, is the parallel composition of one or more processes, nested to the right as the notation `$||$` parses. `parAll p1 [p2, p3]` computes to `p1 $||$ p2 $||$ p3`, so the protocol's triples are already instances of it and no protocol statement changes.
- The n-ary results are proved once, by induction on the list: the inversion of a delay and of a discrete step (one component steps, or two synchronise), the lifting of a component's step and enabledness, no synchronisation between two components while the whole delays, and bisimilarity as a congruence. A step at a position of the list is a `stepAt`, a new generic relation on lists in `src/lib/GenBasics.v`; a fact about every component is a `Forall2`.
- Every triple-shaped lemma is deleted: the `parTriple_*` and `link_par_triple_*` families, `del_triple_sort`, `par_del_sync_not` and `par_bisim_triple`, with the tactics that only served them. Each is listed with its replacement in [`removals.md`](removals.md).
- `net_del_elim` in `src/lang/NetworkLanguage.v` is **restated** over an entity with no process structure, as the workstream decided. It is the one statement that changes; its only use, in `NARMisc.v`, splits the process delay with the n-ary result instead.
- The protocol reaches the three components through one tactic, `triple_pos` in `src/protocol/ProtAuxResults.v`, which turns a position in the three-element list back into the named component. The `link_partrip*` tactics keep their names and the hypotheses they produce, so the long `NAR*` proofs are untouched; three protocol lemma families become tactics: `link_partripdiscW1/2/3_tac`, `dae_broadcast`/`dae_overlap`/`dae_listener` and `triple_del_sync_not`.
- Nothing else changes. [`print_statements.py`](../../../helper-scripts/print_statements.py) printed every statement and definition before and after; the diff is the removals, the additions and `net_del_elim`. `make assumptions` lists the same 84 entries. The [evidence](evidence/README.md) has both.

## Decisions needed from a human

1. **`link_reach_triple_tau` stays.** It says that a silent step of a protocol triple is a synchronisation of two components, as a six-way disjunction, and four `NAR*` proofs consume exactly that shape through `link_partriptau_tac`. It is now a one-line instance of `parAll_disc_inv`, but its statement is protocol-shaped. Replacing it would mean restating the six cases as positions and reworking those four proofs. **Proposed:** keep it until those proofs are revisited.
2. **`parStructPres` and `parStructPres2`** in `SoftwareLanguage.v` are pair-shaped and unused: a step of `p $||$ q` changes each side by at most one step. They are instances of `parAll_disc_weak` and `parAll_del_inv` and could go the same way. **Proposed:** delete them in a later clean-up, since nothing in this step needed them.

## What changed, by file

| File | Change |
|---|---|
| `src/lib/GenBasics.v` | `stepAt`, with `stepAt_Forall2` and `stepAt_stepAt_Forall2`, and the tactic `positions_inv`, which inverts `stepAt` and `Forall2` hypotheses on lists of known shape. |
| `src/lang/SoftwareLanguage.v` | `parAll` and nine results about it: `parAll_disc_intro`, `parAll_dae_intro`, `parAll_sort_intro`, `parAll_disc_inv`, `parAll_del_inv`, `parAll_del_sort_not`, `parAll_del_sync_not`, `parAll_disc_weak`, `parAll_disc_nonTau`. 27 lemmas and 2 tactics removed. |
| `src/lang/ProcEquiv.v` | `parAll_bisim_context` replaces `par_bisim_triple`. |
| `src/lang/EntityLanguage.v` | The unused tactic `del_triple_sort_tac` removed. |
| `src/lang/NetworkLanguage.v` | `net_del_elim` restated. |
| `src/protocol/ProtAuxResults.v` | `triple_pos` and the tactics that rebuild the triple-shaped facts on the n-ary results. `link_reach_triple_tau` re-proved through them. |
| `src/protocol/EntAuxResults.v`, `NetAuxBasics.v`, `NARMisc.v`, `NARIncomp.v`, `NARInsuff.v` | Uses of the deleted lemmas become uses of the tactics. |
| `src/AGENTS.md` | A note on writing intro patterns as `[ | x]`, because `[|` is a token of the entity notation. |

## Where to go next

| Document | Read it when |
|---|---|
| [`removals.md`](removals.md) | Reviewing each removed lemma and the n-ary result or tactic that does its job now. |
| [`evidence/README.md`](evidence/README.md) | Re-running the statement and assumption checks. |
