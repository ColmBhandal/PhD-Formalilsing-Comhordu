# Report: extracting language results from the proved protocol results

| | |
|---|---|
| **Date** | 2026-10-15 |
| **Workstream** | [Rocq upgrade & proof completion](../../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md), step 15 |
| **Result** | Every proved protocol result whose content is about the language now rests on a general result in `src/lang/`. 63 protocol lemmas are gone, 63 language results exist, and `safety` still rests on the same 84 assumptions. |

## What a reader most needs to know

- The protocol files held many copies of the same language fact. The worst case, "a name applied to arguments is bisimilar to its unfolded body", was proved nine times across two files. Each such fact is now one result in `src/lang/`, and the protocol proofs use it.
- A handful of abstractions did most of the work. One result, `parTriple_disc_inv`, replaces the fourteen `link_par_triple_*` lemmas, which are now one-line corollaries. One result, `ent_del_sync_mState_not`, closes nine urgency proofs that each used to extract the no-synchronisation condition by hand.
- Nothing that stays changed. [`print_statements.py`](../../../helper-scripts/print_statements.py) printed every statement and definition in `src/` before and after; the only differences are the additions to `src/lang/` and the removals in [`removals.md`](removals.md). `make assumptions` lists the same 84 entries. The [evidence](evidence/README.md) has both outputs.
- The protocol files shrank from 8,780 to 7,756 lines. The language files grew from 7,022 to 7,805.

## Decisions needed from a human

1. **Generic network notions.** `inPosNet`, `distNet`, `outgoing`, `incomingNet`, `incomingNetNotif`, `mState_in_net`, `transGuard` and `liftEntNet` are defined in `protocol/NetAuxBasics.v`, so the results about them stay there, although nothing in them is about Comhordú. Step 15 keeps every definition where it is, so moving them needs a decision. If they move to `lang/NetworkLanguage.v`, about 25 more results follow them.
2. **`goMsg_gotRange_track_tot`** in `ProtAuxResults.v` has a language-only statement, but it exists only to show that the range `gotMsg` computes by subtraction can never be tested by `bPossInc` ([root cause 5](../2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#5-range-typing-esubtract-vs-bpossinc)). It stays next to its one use until step 21 fixes the typing.

## The general results

Each row is one new result and what it stands in for. Moves keep their statement and name, so the protocol tactics that use them work unchanged.

| Principle | Where | What it says | What it replaced |
|---|---|---|---|
| `bisim_step_disc`, `bisim_step_del` | `ProcEquiv.v` | A bisimulation transfers a step to the other side, with bisimilar derivatives. | `bisim_disc_match` (now a corollary), three helper copies, one tactic, and hand-rolled inversions in a dozen tracking and anti-activation proofs. |
| `app_bisim`, `app_bisim_def`, `app_bisim_nil` | `ProcEquiv.v` | A name applied to arguments is bisimilar to its unfolding. | Nine copies. |
| `outPrefix_bisim_context`, `inPrefix_bisim_context`, `del_bisim_context` | `ProcEquiv.v` | Bisimilarity is a congruence for the prefixes and the delay guard. | Three helpers under `ovReady_prev`. |
| `del_bisim_guard` | `ProcEquiv.v` | A delay guard matters only through its value, including an ill-formed one. | Two helpers under `bc_outProc_out`, which needed both guards to evaluate. |
| `bisim_del_pres` with `del_self_nil/outPrefix/inPrefix/sum` and `del_self_tac` | `ProcEquiv.v`, `SoftwareLanguage.v` | Bisimilarity to a process that delays only to itself survives delays. | The `ovReady_del_pres_tac` tactic and its eight uses, and "sleeping delays only to itself". |
| `par_disc_inv`, `parTriple_disc_inv` | `SoftwareLanguage.v` | The complete case split of a step of a parallel pair or triple: one component steps, or two synchronise. | The fourteen `link_par_triple_*` lemmas, now corollaries, and the tau analysis in `link_reach_triple_tau`. |
| `par_del_inv`, `parTriple_del_inv` | `SoftwareLanguage.v` | A parallel composition delays by every component delaying. | `link_par_triple_delEx`, `link_par_triple_del`, the inversions in `net_del_elim`. |
| `par_del_sync_not`, `parTriple_del_sync_not_12/_13/_23` | `SoftwareLanguage.v` | No delay while two components can synchronise. | The sort-based arguments in `tfsBc_urgent`, `switchBc_urgent`, `tfsListen_urgent`, `switchListen_urgent`. |
| `invert_disc_prefixes` (tactic) | `SoftwareLanguage.v` | Inverts a discrete step out of prefixes, sums, guards and conditionals. | Three identical tactics. |
| `ent_del_noSyncNow`, `ent_del_sync_mState_not`, `ent_del_sync_inter_not` | `EntityLanguage.v` | A delaying entity offers no synchronisation, so a software action with a matching mode-state or interface action rules out delay. | The hand extraction of `noSync` in nine urgency proofs at entity and network level. |
| `ent_del_mCurr_in_not`, `ent_del_mStable_mNext_in_not` | `EntityLanguage.v` | Software that reads the current mode, or stability and the next mode, cannot let time pass. | The two instances pass 1 proved for `gotRange` and `currComp`. |
| `stepEnt_disc_pres_notif_pos` with `timedList_del_ge`, `timedList_out_pres_pos`, `notifList_in_pres`, `notifList_out_pres_pos`, `notifList_in_hd` | `EntityLanguage.v`, `InterfaceLanguage.v` | Timed-list and notification-list facts about delays, inputs and outputs. | Six helpers under `outgoing_del`, `incomingNetNotif_disc_pres` and `outNet_incomingNetNotif`. |
| `stepDiscNet_nonTau_pres_proc` | `NetworkLanguage.v` | A non-silent network step keeps every entity's software component. | Two copies; `procNeq_tau_net` is now a corollary. |
| `link_net_ent_disc_fwd_ex` | `NetworkLanguage.v` | An index occupied before a discrete step is occupied after it. | `inRange_acc_input_fwd_ex`. |
| Moves | `SoftwareLanguage.v`, `EntityLanguage.v`, `ModeStateLanguage.v`, `NetworkLanguage.v` | `subProc_id_eq`, `dae_outPfx`, `dae_inPfx`, `stepDpApp_alt`, `link_ent_soft_disc`, `link_ent_proc_neq_disc`, `mst_tout_mCurr_in`, `procNeq_tau_net`, `link_net_ent_disc`, `del_net_ent`, `inRange_acc_input`, `curr_switch_ent_tau`, `net_del_elim`. | Their protocol copies, and two more copies of `link_ent_soft_disc`. |

## What stays in the protocol

Three proved results have language-only statements and stay: `goMsg_gotRange_track_tot` (above), `delApp` in `ProtocolBridge.v`, which holds only for this protocol's definitions, and `maxAnTrans_positive` in `NARTop.v`, a fact about the model's constants. Everything else that stays mentions a protocol definition.

## Where to go next

| Document | Read it when |
|---|---|
| [`removals.md`](removals.md) | Reviewing each removed protocol lemma and the general result that does its job now. |
| [`evidence/README.md`](evidence/README.md) | Re-running the statement and assumption checks. |
