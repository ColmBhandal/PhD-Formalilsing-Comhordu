# Lemma index: the 108 targets that could not be proved as stated

[← Proof completion, pass 1](../README.md)

The verdicts are explained in [results](../results.md#why-the-unprovable-ones-fail), and the root causes in [root causes and fixes](../root-causes-and-fixes.md).

| Lemma | Module | In cone | Audit verdict | Root cause |
|---|---|---|---|---|
| [`link_ent_outList`](EntAuxResults.md#link_ent_outlist) | EntAuxResults | yes | INCONSISTENT | other:wrong-step-relation (input disjunct uses -tl- ?? which has no rules; buffering is -ol- ??) |
| [`notifBadPathNet_urgent`](NARMisc.md#notifbadpathnet_urgent) | NARMisc | yes | INCONSISTENT | missing-reachability |
| [`outgoing_timeout_disc`](NARMisc.md#outgoing_timeout_disc) | NARMisc | yes | INCONSISTENT | other:message-position-universally-quantified |
| [`bcWaitNet_del_bkwd`](NetAuxBasics.md#bcwaitnet_del_bkwd) | NetAuxBasics | yes | INCONSISTENT | missing-reachability; noSyncNow-missing-pos-clause |
| [`nextSince_del_ovWait`](NetAuxBasics.md#nextsince_del_ovwait) | NetAuxBasics | yes | INCONSISTENT | missing-reachability; noSyncNow-missing-pos-clause |
| [`listening_AN_prot`](ProtAuxResults.md#listening_an_prot) | ProtAuxResults | yes | INCONSISTENT | listener-arity |
| [`ovWait_del_pres`](ProtAuxResults.md#ovwait_del_pres) | ProtAuxResults | yes | INCONSISTENT | other:timers-count-down-under-delay |
| [`reachableProt_triple`](ProtAuxResults.md#reachableprot_triple) | ProtAuxResults | yes | INCONSISTENT | incomplete-definition (overlapState/listenerState) |
| [`insuff_incomingNotif_bad`](NARInsuff.md#insuff_incomingnotif_bad) | NARInsuff | yes | CONTRADICTS-ADMITTED | missing-reachability |
| [`switchBc_nextMode_net`](NARMisc.md#switchbc_nextmode_net) | NARMisc | yes | CONTRADICTS-ADMITTED | missing-reachability |
| [`tfsBc_failSafe`](EntAuxResults.md#tfsbc_failsafe) | EntAuxResults | yes | FALSE-IN-INTENDED-MODEL | missing-reachability |
| [`insuff_incomingNotif_abort`](NARInsuff.md#insuff_incomingnotif_abort) | NARInsuff | yes | FALSE-IN-INTENDED-MODEL | missing-reachability |
| [`rangeBad_notifBad_net`](NARMisc.md#rangebad_notifbad_net) | NARMisc | yes | FALSE-IN-INTENDED-MODEL | other:missing-currModeNet-hypothesis |
| [`rangeBad_next_net`](NetAuxBasics.md#rangebad_next_net) | NetAuxBasics | yes | FALSE-IN-INTENDED-MODEL | stub; missing-reachability; mode-chan-internal-sync |
| [`switch_states_mState`](NetAuxBasics.md#switch_states_mstate) | NetAuxBasics | yes | FALSE-IN-INTENDED-MODEL | stub; missing-reachability; mode-chan-internal-sync |
| [`tfsListen_failSafe_net`](NetAuxBasics.md#tfslisten_failsafe_net) | NetAuxBasics | yes | FALSE-IN-INTENDED-MODEL | stub; missing-reachability |
| [`bcWait_bktrk_net`](NARMisc.md#bcwait_bktrk_net) | NARMisc | yes | FALSE-ARGUED | other:sent-on-wrong-network + missing chanWake predecessor case |
| [`bcWait_currSince_time`](NARTop.md#bcwait_currsince_time) | NARTop | yes | FALSE-ARGUED | other:wake-up-corner-case (bcWait m 0 right after switchBc) |
| [`bcReady_pos`](EntAuxResults.md#bcready_pos) | EntAuxResults | yes | BLOCKED-ON-STUB | stub |
| [`ovReady_pos`](EntAuxResults.md#ovready_pos) | EntAuxResults | yes | BLOCKED-ON-STUB | stub |
| [`switchCurr_nextSince_nextMode_net`](NARMisc.md#switchcurr_nextsince_nextmode_net) | NARMisc | yes | BLOCKED-ON-STUB | stub |
| [`currModeNet_del_pres`](NetAuxBasics.md#currmodenet_del_pres) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`currMode_ent_ex`](NetAuxBasics.md#currmode_ent_ex) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`currMode_intro`](NetAuxBasics.md#currmode_intro) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`currMode_pres_bkwd`](NetAuxBasics.md#currmode_pres_bkwd) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`inPos_ent_net`](NetAuxBasics.md#inpos_ent_net) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`reachable_net_ent`](NetAuxBasics.md#reachable_net_ent) | NetAuxBasics | yes | BLOCKED-ON-STUB | stub |
| [`currSince_del_bcWait`](NARTop.md#currsince_del_bcwait) | NARTop | yes | BLOCKED-ON-DEFINITION | incomplete-definition (overlapState/listenerState) |
| [`ovWait_sent`](NARTop.md#ovwait_sent) | NARTop | yes | BLOCKED-ON-DEFINITION | incomplete-definition (overlapState/listenerState) |
| [`switchCurr_nextSince`](NARNonFS_currSince.md#switchcurr_nextsince) | NARNonFS_currSince | yes | unaudited |  |
| [`nextSince_switchCurr_lower`](NAROvlpTime.md#nextsince_switchcurr_lower) | NAROvlpTime | yes | unaudited |  |
| [`currComp_listening_track_ent`](EntAuxResults.md#currcomp_listening_track_ent) | EntAuxResults | no | INCONSISTENT | mode-chan-internal-sync |
| [`currComp_nextPincCheck_track_ent`](EntAuxResults.md#currcomp_nextpinccheck_track_ent) | EntAuxResults | no | INCONSISTENT | mode-chan-internal-sync |
| [`gotRange_currPincCheck_track_ent`](EntAuxResults.md#gotrange_currpinccheck_track_ent) | EntAuxResults | no | INCONSISTENT | bisim-state-param-tracking |
| [`tfsListen_paused`](EntAuxResults.md#tfslisten_paused) | EntAuxResults | no | INCONSISTENT | other:false-invariant (listener is not paused on the fail-safe path) |
| [`tfsNext_prev_ent`](EntAuxResults.md#tfsnext_prev_ent) | EntAuxResults | no | INCONSISTENT | missing-reachability |
| [`inList_pres_input`](InterfaceLanguage.md#inlist_pres_input) | InterfaceLanguage | no | INCONSISTENT | other:missing-non-delay-hypothesis (stepIlDel empties any input list) |
| [`inList_received_in`](InterfaceLanguage.md#inlist_received_in) | InterfaceLanguage | no | INCONSISTENT | typo (copy-paste from outList_received_in: stepIlBuff stamps zeroTime, not msgLatency) |
| [`msgBadPathNet_urgent`](NARMisc.md#msgbadpathnet_urgent) | NARMisc | no | INCONSISTENT | missing-reachability |
| [`del_pres_bkwd_tfsStart`](NetAuxBasics.md#del_pres_bkwd_tfsstart) | NetAuxBasics | no | INCONSISTENT | missing-reachability; incomplete-definition (overlapState) |
| [`mState_switch_states`](NetAuxBasics.md#mstate_switch_states) | NetAuxBasics | no | INCONSISTENT | stepDeTest-env-mode-change |
| [`ovReady_del_pres_bkwd_net`](NetAuxBasics.md#ovready_del_pres_bkwd_net) | NetAuxBasics | no | INCONSISTENT | missing-reachability; incomplete-definition (overlapState) |
| [`ovReady_prev_net_strong`](NetAuxBasics.md#ovready_prev_net_strong) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`ovWait_del_pres_bkwd_net_strong`](NetAuxBasics.md#ovwait_del_pres_bkwd_net_strong) | NetAuxBasics | no | INCONSISTENT | missing-reachability; noSyncNow-missing-pos-clause |
| [`ovWait_del_pres_net`](NetAuxBasics.md#ovwait_del_pres_net) | NetAuxBasics | no | INCONSISTENT | other:timer-params-not-delay-invariant; missing-reachability |
| [`ovWait_prev_net`](NetAuxBasics.md#ovwait_prev_net) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`ovWait_prev_net_strong`](NetAuxBasics.md#ovwait_prev_net_strong) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`tfsCurrStateNet_bktrk_net`](NetAuxBasics.md#tfscurrstatenet_bktrk_net) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`tfsCurrState_del_pres_net`](NetAuxBasics.md#tfscurrstate_del_pres_net) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`tfsStart_prev_net`](NetAuxBasics.md#tfsstart_prev_net) | NetAuxBasics | no | INCONSISTENT | other:missing-dormant-predecessor; missing-reachability |
| [`tfsState_del_pres_net`](NetAuxBasics.md#tfsstate_del_pres_net) | NetAuxBasics | no | INCONSISTENT | missing-reachability |
| [`transGuard_del`](NetAuxBasics.md#transguard_del) | NetAuxBasics | no | INCONSISTENT | other:no-urgency-hypothesis (expired mode-state guard can delay when software offers no chanMCurr!) |
| [`transGuard_disc_pres`](NetAuxBasics.md#transguard_disc_pres) | NetAuxBasics | no | INCONSISTENT | other:expired-guard-switch (stepDeCurrWrite+stepMsSwitch turns </m,m',0/> into sing m') |
| [`msgAbort_modeState_eq`](NetAuxDefs.md#msgabort_modestate_eq) | NetAuxDefs | no | INCONSISTENT | stepDeTest-env-mode-change |
| [`msgBad_modeState_eq`](NetAuxDefs.md#msgbad_modestate_eq) | NetAuxDefs | no | INCONSISTENT | stepDeTest-env-mode-change |
| [`notifAbort_modeState_eq`](NetAuxDefs.md#notifabort_modestate_eq) | NetAuxDefs | no | INCONSISTENT | stepDeTest-env-mode-change |
| [`notifBad_modeState_eq`](NetAuxDefs.md#notifbad_modestate_eq) | NetAuxDefs | no | INCONSISTENT | stepDeTest-env-mode-change |
| [`evalBoolExpFalseTot`](ProcEquiv.md#evalboolexpfalsetot) | ProcEquiv | no | INCONSISTENT | other:ill-formed-expression-evaluates-to-false |
| [`currComp_next`](ProtAuxResults.md#currcomp_next) | ProtAuxResults | no | INCONSISTENT | untyped-input |
| [`currOK_listening_track`](ProtAuxResults.md#currok_listening_track) | ProtAuxResults | no | INCONSISTENT | other:nextEq-else-branch-returns-to-listening (plus untyped-input) |
| [`gotMessage_next`](ProtAuxResults.md#gotmessage_next) | ProtAuxResults | no | INCONSISTENT | eSubtract-vs-bPossInc-typing |
| [`gotMsg_state`](ProtAuxResults.md#gotmsg_state) | ProtAuxResults | no | INCONSISTENT | other:missing-protocolState-hypothesis (p unconstrained) |
| [`gotRange_next`](ProtAuxResults.md#gotrange_next) | ProtAuxResults | no | INCONSISTENT | untyped-input |
| [`paused_switch`](ProtAuxResults.md#paused_switch) | ProtAuxResults | no | INCONSISTENT | other:reachableProt-allows-unsynchronised-internal-actions |
| [`tfsStart_next`](ProtAuxResults.md#tfsstart_next) | ProtAuxResults | no | INCONSISTENT | untyped-input |
| [`delProc_minus_guard`](SoftwareLanguage.md#delproc_minus_guard) | SoftwareLanguage | no | INCONSISTENT | other:unconstrained-guard-expression |
| [`gotMsgStateEnt_urgent`](EntAuxResults.md#gotmsgstateent_urgent) | EntAuxResults | no | CONTRADICTS-ADMITTED | noSyncNow-missing-pos-clause |
| [`nextEq_mode`](EntAuxResults.md#nexteq_mode) | EntAuxResults | no | CONTRADICTS-ADMITTED | bisim-state-param-tracking |
| [`nextModeEnt_not_stable`](EntAuxResults.md#nextmodeent_not_stable) | EntAuxResults | no | CONTRADICTS-ADMITTED | typo |
| [`nextMode_ent_mState`](EntAuxResults.md#nextmode_ent_mstate) | EntAuxResults | no | CONTRADICTS-ADMITTED | stub |
| [`tfsCurr_failSafe`](EntAuxResults.md#tfscurr_failsafe) | EntAuxResults | no | CONTRADICTS-ADMITTED | missing-reachability |
| [`init_nextMode_net`](NARMisc.md#init_nextmode_net) | NARMisc | no | CONTRADICTS-ADMITTED | missing-reachability |
| [`currEq_mode`](EntAuxResults.md#curreq_mode) | EntAuxResults | no | FALSE-IN-INTENDED-MODEL | missing-reachability |
| [`gotMsg_gotRange_track_ent`](EntAuxResults.md#gotmsg_gotrange_track_ent) | EntAuxResults | no | FALSE-IN-INTENDED-MODEL | eSubtract-vs-bPossInc-typing |
| [`tfsNext_currMode`](EntAuxResults.md#tfsnext_currmode) | EntAuxResults | no | FALSE-IN-INTENDED-MODEL | bisim-state-param-tracking |
| [`notifList_received_in`](InterfaceLanguage.md#notiflist_received_in) | InterfaceLanguage | no | FALSE-IN-INTENDED-MODEL | typo (copy-paste: stepNlBuff stamps adaptNotif, not msgLatency) |
| [`tfsNext_currModeNet_eq`](NetAuxBasics.md#tfsnext_currmodenet_eq) | NetAuxBasics | no | FALSE-IN-INTENDED-MODEL | missing-reachability |
| [`msgBad_disc_net`](NARMisc.md#msgbad_disc_net) | NARMisc | no | FALSE-ARGUED | other:msgBadPathEnt-does-not-exclude-tfs-overlap |
| [`currSince_bc_state`](NARTop.md#currsince_bc_state) | NARTop | no | FALSE-ARGUED | other:new-transition-wakes-broadcaster-in-new-mode |
| [`ovReady_wait_track_net`](NetAuxBasics.md#ovready_wait_track_net) | NetAuxBasics | no | FALSE-ARGUED | bisim-state-param-tracking |
| [`ovWait_track_net`](NetAuxBasics.md#ovwait_track_net) | NetAuxBasics | no | FALSE-ARGUED | bisim-state-param-tracking |
| [`tfsState_not_currSince`](NARMisc.md#tfsstate_not_currsince) | NARMisc | no | NEEDS-HYPOTHESIS | other:failSafeSucc-may-be-identity |
| [`tfs_zero_disc_pres`](NARMisc.md#tfs_zero_disc_pres) | NARMisc | no | NEEDS-HYPOTHESIS | other:modeTransTime-may-be-zero |
| [`tfsBc_not_currSince`](NARTop.md#tfsbc_not_currsince) | NARTop | no | NEEDS-HYPOTHESIS | other:failSafeSucc-may-be-identity |
| [`rangeBad_next`](ProtAuxResults.md#rangebad_next) | ProtAuxResults | no | NEEDS-HYPOTHESIS | untyped-input |
| [`ovAbort_unstable`](EntAuxResults.md#ovabort_unstable) | EntAuxResults | no | BLOCKED-ON-STUB | stub |
| [`reachable_ent_prot`](EntAuxResults.md#reachable_ent_prot) | EntAuxResults | no | BLOCKED-ON-STUB | stub |
| [`switchCurr_mState`](EntAuxResults.md#switchcurr_mstate) | EntAuxResults | no | BLOCKED-ON-STUB | stub |
| [`currMode_pres_fwd`](NetAuxBasics.md#currmode_pres_fwd) | NetAuxBasics | no | BLOCKED-ON-STUB | stub |
| [`init_nextMode_net`](NetAuxBasics.md#init_nextmode_net) | NetAuxBasics | no | BLOCKED-ON-STUB | stub |
| [`nextModeNet_del_pres`](NetAuxBasics.md#nextmodenet_del_pres) | NetAuxBasics | no | BLOCKED-ON-STUB | stub |
| [`nextMode_ent_ex`](NetAuxBasics.md#nextmode_ent_ex) | NetAuxBasics | no | BLOCKED-ON-STUB | stub |
| [`nextMode_pres_fwd_net`](NetAuxBasics.md#nextmode_pres_fwd_net) | NetAuxBasics | no | BLOCKED-ON-STUB | stub; missing-WRITE-STBL-rule |
| [`tfs_state_rel`](NARInsuff.md#tfs_state_rel) | NARInsuff | no | BLOCKED-ON-DEFINITION | incomplete-definition (overlapState/listenerState) |
| [`init_ovWait_track_net`](NARTop.md#init_ovwait_track_net) | NARTop | no | BLOCKED-ON-DEFINITION | other:missing-bisimulation-injectivity-infrastructure (not a failure) |
| [`ovReady_ovWait_track_ent`](EntAuxResults.md#ovready_ovwait_track_ent) | EntAuxResults | no | unaudited |  |
| [`incomingNet_urgent`](NARIncomp.md#incomingnet_urgent) | NARIncomp | no | unaudited |  |
| [`incomp_incomingNet_abort`](NARIncomp.md#incomp_incomingnet_abort) | NARIncomp | no | unaudited |  |
| [`ovReady_nextSince_pending`](NARNonFS_currSince.md#ovready_nextsince_pending) | NARNonFS_currSince | no | unaudited |  |
| [`ovWait_nextSince_pending`](NARNonFS_currSince.md#ovwait_nextsince_pending) | NARNonFS_currSince | no | unaudited |  |
| [`ovWait_zero_nextSince`](NARNonFS_currSince.md#ovwait_zero_nextsince) | NARNonFS_currSince | no | unaudited |  |
| [`pending_urgent`](NARNonFS_currSince.md#pending_urgent) | NARNonFS_currSince | no | unaudited |  |
| [`switchBc_nextSince`](NARNonFS_currSince.md#switchbc_nextsince) | NARNonFS_currSince | no | unaudited |  |
| [`nextSince_ovWait_ovReady_time`](NAROvlpTime.md#nextsince_ovwait_ovready_time) | NAROvlpTime | no | unaudited |  |
| [`nextSince_switchBc_lower`](NAROvlpTime.md#nextsince_switchbc_lower) | NAROvlpTime | no | unaudited |  |
| [`pending_time1`](NAROvlpTime.md#pending_time1) | NAROvlpTime | no | unaudited |  |
| [`pending_time2`](NAROvlpTime.md#pending_time2) | NAROvlpTime | no | unaudited |  |
| [`pending_urgent`](NAROvlpTime.md#pending_urgent) | NAROvlpTime | no | unaudited |  |

**Per module:** [EntAuxResults](EntAuxResults.md) (21) · [InterfaceLanguage](InterfaceLanguage.md) (3) · [NARIncomp](NARIncomp.md) (2) · [NARInsuff](NARInsuff.md) (3) · [NARMisc](NARMisc.md) (11) · [NARNonFS_currSince](NARNonFS_currSince.md) (6) · [NAROvlpTime](NAROvlpTime.md) (6) · [NARTop](NARTop.md) (6) · [NetAuxBasics](NetAuxBasics.md) (33) · [NetAuxDefs](NetAuxDefs.md) (4) · [ProcEquiv](ProcEquiv.md) (1) · [ProtAuxResults](ProtAuxResults.md) (11) · [SoftwareLanguage](SoftwareLanguage.md) (1)
