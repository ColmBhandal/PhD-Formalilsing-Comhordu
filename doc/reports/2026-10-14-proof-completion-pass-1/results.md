# Results

[← Proof completion, pass 1](README.md)

## Overall

| Outcome | Targets | In `safety`'s cone |
|---|---|---|
| Proved and merged | 123 | 57 |
| Proved but held back, because the proof depends on an inconsistent admitted lemma | 25 | 12 |
| Can't be proved as stated, so written up | 108 | 31 |
| **Total** | **256** | **100** |

`Print Assumptions safety` went from 134 entries to 85. 50 of the 85 are still-unproved project lemmas, down from 100. The rest are model axioms, `Parameter` stubs and stdlib axioms.

## Why the unprovable ones fail

Each write-up was checked by an independent auditor. The auditor recompiled every claimed refutation against the target's exact statement and ran `Print Assumptions` on it. All of the evidence compiled, and the auditors corrected several verdicts in both directions. Every target got exactly one verdict:

| Verdict | Meaning | Count |
|---|---|---|
| INCONSISTENT | Refuted in Rocq from the model axioms and stdlib alone, sometimes given any inhabitant of `Mode`. Admitting it makes the whole development inconsistent. | 43 (8 in cone) |
| CONTRADICTS-ADMITTED | Refuted only together with other admitted lemmas or stubs. Jointly inconsistent, so the blame is shared. | 8 (2 in cone) |
| FALSE-IN-INTENDED-MODEL | Can't be refuted from the axioms, but false under the intended reading, e.g. once there are two distinct modes or a stub has its intended definition. | 11 (6 in cone) |
| FALSE-ARGUED | False by a careful paper argument, but not mechanised. | 6 (2 in cone) |
| NEEDS-HYPOTHESIS | False as stated in degenerate models, true with a named extra hypothesis. | 4 (0 in cone) |
| BLOCKED-ON-STUB | Unprovable while a `Parameter` stub stays opaque. True under the [suggested definition](root-causes-and-fixes.md#parameter-stubs). | 17 (9 in cone) |
| BLOCKED-ON-DEFINITION | Needs a definition change, or rests on an inconsistent lemma. A conditional proof exists. | 4 (2 in cone) |
| Not audited | Write-ups from the last two cloud provers (`NARNonFS_currSince`, NAR-small), which arrived after the audit started. Prover verdict only. | 15 (2 in cone) |

**INCONSISTENT is the dangerous class**, because admitting such a lemma lets you prove `False`. The harness rejected any proof whose assumptions included one, so no **new** proof in this pass rests on them. Results that were already `Qed` before this pass still can, though. `safety` itself is one ([why that matters](why-safety-is-vacuous.md)). Another is `SoftwareLanguage.delAddSoft`, which goes through `delProc_minus_guard`.

The full list of inconsistent and jointly-inconsistent lemmas is [`evidence/inconsistent-or-contradicting.txt`](evidence/inconsistent-or-contradicting.txt). Each lemma's verdict and write-up is in the [lemma index](lemmas/README.md).

## Held-back proofs

These 25 proofs compile, but each rests on at least one lemma from the inconsistent list, so none of them is merged. Once the lemmas they depend on are fixed, they can be re-checked and merged in pass 2. Each target links to its proof script, in the harness format described in [evidence](evidence/README.md).

| Target | Inconsistent dependencies |
|---|---|
| [`EntAuxResults.abortOvlpStateEnt_urgent`](evidence/held-back/EntAuxResults.abortOvlpStateEnt_urgent.v) | `reachableProt_triple` |
| [`EntAuxResults.del_listening`](evidence/held-back/EntAuxResults.del_listening.v) | `paused_switch`, `reachableProt_triple` |
| [`EntAuxResults.del_listening_pre`](evidence/held-back/EntAuxResults.del_listening_pre.v) | `reachableProt_triple` |
| [`EntAuxResults.del_ovlp`](evidence/held-back/EntAuxResults.del_ovlp.v) | `reachableProt_triple` |
| [`EntAuxResults.tfsStart_next_ent`](evidence/held-back/EntAuxResults.tfsStart_next_ent.v) | `tfsStart_next` |
| [`EntityLanguage.timeSplit_ent`](evidence/held-back/EntityLanguage.timeSplit_ent.v) | `delProc_minus_guard` |
| [`NARIncomp.incomp_tfs`](evidence/held-back/NARIncomp.incomp_tfs.v) | `currComp_listening_track_ent`, `currComp_next`, `currComp_nextPincCheck_track_ent`, `gotMessage_next`, `gotMsgStateEnt_urgent`, `gotMsg_state`, `gotRange_currPincCheck_track_ent`, `gotRange_next`, `inList_pres_input`, `msgAbort_modeState_eq`, `msgBadPathNet_urgent`, `ovWait_del_pres`, `reachableProt_triple`, `switchBc_nextMode_net` |
| [`NARInsuff.nextSince_next`](evidence/held-back/NARInsuff.nextSince_next.v) | `ovWait_del_pres`, `switchBc_nextMode_net` |
| [`NARInsuff.notifAbort_not_nextSince`](evidence/held-back/NARInsuff.notifAbort_not_nextSince.v) | `currOK_listening_track`, `nextEq_mode`, `nextMode_ent_mState`, `notifAbort_modeState_eq`, `reachableProt_triple` |
| [`NARMisc.currModeNet_switch_states`](evidence/held-back/NARMisc.currModeNet_switch_states.v) | `mState_switch_states` |
| [`NARMisc.nextSince_ovReaddy_modeEq`](evidence/held-back/NARMisc.nextSince_ovReaddy_modeEq.v) | `ovReady_del_pres_bkwd_net`, `ovReady_prev_net` |
| [`NARMisc.nextSince_ovWait_modeEq`](evidence/held-back/NARMisc.nextSince_ovWait_modeEq.v) | `mState_switch_states`, `nextMode_ent_mState`, `switchBc_nextMode_net` |
| [`NARMisc.nextSince_switchBc_modeEq`](evidence/held-back/NARMisc.nextSince_switchBc_modeEq.v) | `mState_switch_states`, `nextMode_ent_mState`, `switchBc_nextMode_net` |
| [`NARMisc.ovWait_nextSince_time`](evidence/held-back/NARMisc.ovWait_nextSince_time.v) | `ovWait_del_pres`, `ovWait_del_pres_bkwd_net_strong`, `ovWait_prev_net` |
| [`NARMisc.tfsNext_tfs_mode_eq`](evidence/held-back/NARMisc.tfsNext_tfs_mode_eq.v) | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `mState_switch_states`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| [`NARMisc.tfsNext_tfs_zero`](evidence/held-back/NARMisc.tfsNext_tfs_zero.v) | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| [`NARMisc.tfsStart_tfs_zero`](evidence/held-back/NARMisc.tfsStart_tfs_zero.v) | `del_pres_bkwd_tfsStart`, `tfsStart_prev_net`, `tfsState_del_pres_net` |
| [`NARMisc.tfs_bound`](evidence/held-back/NARMisc.tfs_bound.v) | `del_pres_bkwd_tfsNext`, `del_pres_bkwd_tfsStart`, `mState_switch_states`, `reachableProt_triple`, `tfsCurrStateNet_bktrk_net`, `tfsCurrState_del_pres_net`, `tfsListen_paused`, `tfsNext_prev_ent`, `tfsStart_prev_net`, `tfsState_del_pres_net`, `transGuard_del` |
| [`NARMisc.tfs_rel_state`](evidence/held-back/NARMisc.tfs_rel_state.v) | `tfsState_del_pres_net` |
| [`NARTop.ovWait_del_pres_bkwd_net_strong`](evidence/held-back/NARTop.ovWait_del_pres_bkwd_net_strong.v) | `ovWait_del_pres_bkwd_net_strong` |
| [`NetAuxBasics.del_listening_net`](evidence/held-back/NetAuxBasics.del_listening_net.v) | `reachableProt_triple` |
| [`NetAuxBasics.del_pres_bkwd_tfsNext`](evidence/held-back/NetAuxBasics.del_pres_bkwd_tfsNext.v) | `del_pres_bkwd_tfsNext`, `tfsState_del_pres_net` |
| [`NetAuxBasics.ovReady_prev_net`](evidence/held-back/NetAuxBasics.ovReady_prev_net.v) | `ovReady_prev_net`, `ovReady_prev_net_strong` |
| [`NetAuxBasics.ovWait_ovReady_nextMode_net`](evidence/held-back/NetAuxBasics.ovWait_ovReady_nextMode_net.v) | `init_nextMode_net`, `ovReady_del_pres_bkwd_net`, `ovReady_prev_net_strong`, `ovWait_del_pres_bkwd_net_strong`, `ovWait_prev_net_strong` |
| [`NetAuxBasics.paused_switch_net`](evidence/held-back/NetAuxBasics.paused_switch_net.v) | `paused_switch` |

Some cloud provers also finished proofs that rest on inconsistent lemmas. Notes on those are in [`evidence/conditional/`](evidence/conditional/).
