# Report: move the generic network notions to `lang/`

| | |
|---|---|
| **Date** | 2026-10-16 |
| **Workstream** | [Rocq upgrade & proof completion](../../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md), step 17 |
| **Result** | The eight network notions that step 15 found to be generic now live in `src/lang/NetworkLanguage.v`, with the 21 proved results about them, every statement unchanged. One of those results, `outgoing_disc_pres`, rested on a false protocol lemma and is re-proved from the language, so `safety` rests on **83** assumptions, down from 84. |

## What a reader most needs to know

- `inPosNet`, `distNet`, `outgoing`, `incomingNet`, `incomingNetNotif`, `mState_in_net`, `transGuard` and `liftEntNet` move from `src/protocol/NetAuxBasics.v` to the end of the section in `src/lang/NetworkLanguage.v`, where the interface and mode state notations are in scope. `incomingEnt`, which two of the moved results relate to `incomingNet`, moves from `src/protocol/EntAuxDefs.v` to `src/lang/EntityLanguage.v` for the same reason: nothing in it is about Comhordú.
- The 21 proved results about them move with them, and the tactic `inposdp`, which two `NARIncomp.v` proofs use, goes after the section. No statement changes. The pass-1 lemmas that these notions appear in stay as they are, and `safety` has the same statement.
- **`outgoing_disc_pres` is re-proved.** Its proof called `link_ent_outList`, an `Admitted` protocol lemma that pass 1 found [false](../2026-10-14-proof-completion-pass-1/lemmas/EntAuxResults.md#link_ent_outlist): its input disjunct is stated at a level of the timed lists where no input rule exists. The result itself is true, because buffering only prepends to the output list, so it now rests on two new language results: `outList_buff_pres` in `InterfaceLanguage.v` (buffering keeps every element of an output list) and `stepEnt_disc_pres_out_pos` in `EntityLanguage.v` (a discrete entity step keeps every outgoing message with a positive timestamp), the twin of the existing `stepEnt_disc_pres_notif_pos`. `link_ent_outList` was in the cone of `safety` only through `outgoing_disc_pres`, so it leaves `make assumptions`: 83 entries, down from 84, and nothing is added. With nothing left using it, and its statement false, it is **deleted** with human approval (decision 2 below).
- `outList_in_input_pres` in `InterfaceLanguage.v` is **deleted**. It was the lemma that `outgoing_disc_pres` used on the input disjunct, proved vacuously because its premise can never hold, and `outList_buff_pres` does its job. Nothing else used it.
- **What stays in the protocol, and why.** `incomingNetNotif_del` needs `reachableNet` in its statement and the protocol's `del_listening_net` and `listening_AN_prot` in its proof. The unproved results about the moved notions stay too: `transGuard_disc_pres` and `transGuard_del` are [false](../2026-10-14-proof-completion-pass-1/lemmas/NetAuxBasics.md#transguard_disc_pres), and `inPos_ent_net`, `currMode_intro`, `currMode_ent_ex` and `nextMode_ent_ex` wait on the `Parameter` stubs. Inside the language's section a `Conjecture` would be generalised to every instance of the language, which changes what it claims, so they wait for steps 21 and 22. The network tactics `fwd_track_net_tac`, `netState_auto_pre`, `netState_ent_net_tac`, `backtrack_net_pre` and `state_pred_elim_net` stay where their only uses are, as `src/lang/AGENTS.md` asks; most of them also assume the protocol's triple.
- **Nothing else changes.** [`print_statements.py`](../../../helper-scripts/print_statements.py) printed every statement and definition before and after. The diff is the moved and added entries, and the users of the moved names in the protocol, whose lines differ only in a module path. The moved entries are also printed with the same notations in scope on both sides, and differ only by the instance binders the section adds. The [evidence](evidence/README.md) has all of it.
- **Rocq in sandboxed sessions.** Agents kept finding that `rocq` isn't on the `PATH` in their sandboxed sessions, where there is no Docker daemon and opam's repository is blocked. `helper-scripts/install_rocq.sh` downloads the CI image's layers straight from Docker Hub and unpacks its Rocq to the path it has in the image, in about 80 seconds. The top-level `AGENTS.md` says when to run it, and now also carries the permanent rule that nothing in the repository is specific to one agent or vendor: instructions live in `AGENTS.md` files and setup lives in plain scripts, with no vendor hooks, settings or skills.

## Decisions needed from a human

1. **`incomingEnt` moved too**, although step 17 listed only the eight network notions. It is the entity-level twin of `incomingNet`, and `incoming_net_ent` and `incoming_ent_net` relate the two. **Decided:** keep the move.
2. **`link_ent_outList`** is now used by nothing and is false as stated. Step 19 planned to fix its statement as a quick fix in the cone; it is no longer in the cone. **Decided:** delete it, in this PR. Step 19 no longer lists it.

## What changed, by file

| File | Change |
|---|---|
| `src/lang/InterfaceLanguage.v` | `outList_buff_pres` added; `outList_in_input_pres` deleted. |
| `src/lang/EntityLanguage.v` | `incomingEnt` moved in; `stepEnt_disc_pres_out_pos` added. |
| `src/lang/NetworkLanguage.v` | The eight notions and 21 results moved in, at the end of the section; `inposdp` after it. `outgoing_disc_pres` re-proved; the other proofs are as before, except that four call the linking lemmas directly where they used tactics that are declared after the section. |
| `src/protocol/NetAuxBasics.v`, `src/protocol/EntAuxDefs.v` | The moved definitions, results and tactic removed. Nothing else changes; the other protocol files compile unchanged. |
| `src/protocol/EntAuxResults.v` | `link_ent_outList` deleted, with human approval. |
| `src/lang/README.md`, `src/protocol/README.md` | The two files' descriptions updated. |
| `helper-scripts/install_rocq.sh` | Rocq for sandboxed sessions, as above, with the rules in `AGENTS.md` and `helper-scripts/AGENTS.md` and the `README.md`s updated. |

## Where to go next

| Document | Read it when |
|---|---|
| [`evidence/README.md`](evidence/README.md) | Checking that no statement changed, or re-running the checks. |
| [Pass-1 write-up of `link_ent_outList`](../2026-10-14-proof-completion-pass-1/lemmas/EntAuxResults.md#link_ent_outlist) | Checking why it was false, now that it is gone. |
