## Assumptions under `safety`

**83** assumptions in total.

| Kind | Count |
|---|---|
| Unproved project lemmas (Admitted / Conjecture) | 48 |
| Parameter stubs | 4 |
| Model axioms (ComhBasics, deliberate) | 25 |
| Standard-library axioms | 6 |

Whole codebase: **119** `Admitted`, **12** `Conjecture`.

<details><summary>Unproved lemmas under safety, by file</summary>

- `NARMisc`: 15
- `NetAuxBasics`: 14
- `EntAuxResults`: 6
- `NARInsuff`: 4
- `NARTop`: 3
- `ProtAuxResults`: 2
- `EntityLanguage`: 1
- `NARNonFS_currSince`: 1
- `NAROvlpTime`: 1
- `NARIncomp`: 1

</details>

<details><summary>Full list</summary>

```
ComhBasics.waitSurplus
ComhBasics.transMaxBound
ComhBasics.transMax
ComhBasics.trans
EntityLanguage.timeSplit_ent
NARMisc.tfs_rel_state
NARMisc.tfs_bound
NARMisc.tfsState_not_currSince
EntAuxResults.tfsStart_next_ent
NetAuxBasics.tfsListen_failSafe_net
EntAuxResults.tfsBc_failSafe
NetAuxBasics.switch_states_mState
NARMisc.switchCurr_nextSince_nextMode_net
NARNonFS_currSince.switchCurr_nextSince
NARMisc.switchBc_nextMode_net
ComhBasics.speedMax_pos
ComhBasics.speedMax
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
NetAuxBasics.reachable_net_ent
ProtAuxResults.reachableProt_triple
EntAuxDefs.reachableEnt
NARMisc.rangeBad_notifBad_net
NetAuxBasics.rangeBad_next_net
ProofIrrelevance.proof_irrelevance
ComhBasics.period_positive
ComhBasics.period
NetAuxBasics.paused_switch_net
NARTop.ovWait_sent
NetAuxBasics.ovWait_ovReady_nextMode_net
NARMisc.ovWait_nextSince_time
ProtAuxResults.ovWait_del_pres
EntAuxResults.ovReady_pos
EntAuxResults.ovReady_ovWait_track_ent
NARMisc.outgoing_timeout_disc
NARMisc.notifBadPathNet_urgent
NARInsuff.notifAbort_not_nextSince
NAROvlpTime.nextSince_switchCurr_lower
NARMisc.nextSince_switchBc_modeEq
NARMisc.nextSince_ovWait_modeEq
NARMisc.nextSince_ovReaddy_modeEq
NARInsuff.nextSince_next
NetAuxBasics.nextSince_del_ovWait
NetAuxBasics.nextModeNet
ComhBasics.msgLatency_positive
ComhBasics.msgLatency
NARMisc.msgBad_disc_net
ComhBasics.modeTransTime
ComhBasics.modeTransRelDec
ComhBasics.modeTransRel
ComhBasics.minDistCompSymmetric
ComhBasics.minDistCompFS
ComhBasics.minDistComp
ComhBasics.maxMinDistCompBound
ComhBasics.maxMinDistComp
NARInsuff.insuff_incomingNotif_bad
NARInsuff.insuff_incomingNotif_abort
NARIncomp.incomp_tfs
NetAuxBasics.inPos_ent_net
EntAuxDefs.inPosEnt
FunctionalExtensionality.functional_extensionality_dep
ComhBasics.fsDecMode
ComhBasics.failSafeSucc
ComhBasics.failSafe
Eqdep.Eq_rect_eq.eq_rect_eq
ComhBasics.eqDecMode
NetAuxBasics.del_listening_net
NARTop.currSince_del_bcWait
NetAuxBasics.currMode_pres_bkwd
NetAuxBasics.currMode_intro
NetAuxBasics.currMode_ent_ex
NARMisc.currModeNet_switch_states
NetAuxBasics.currModeNet_del_pres
NetAuxBasics.currModeNet
Classical_Prop.classic
NARTop.bcWait_currSince_time
NARMisc.bcWait_bktrk_net
NetAuxBasics.bcWaitNet_del_bkwd
EntAuxResults.bcReady_pos
ComhBasics.adaptNotif_positive
ComhBasics.adaptNotif
EntAuxResults.abortOvlpStateEnt_urgent
ComhBasics.Mode
```
</details>
