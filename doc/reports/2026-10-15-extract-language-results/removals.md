[← Report](README.md)

# Removed protocol lemmas

Every protocol lemma or tactic removed, with the general result that does its job now. A *move* keeps the statement and the name, so callers compile unchanged. A *helper* is a lemma pass 1 added for one protocol result; its job was a special case of the general result.

## `src/protocol/ProtAuxResults.v`

| Removed | Kind | Replaced by |
|---|---|---|
| `subProc_id_eq` | move | `SoftwareLanguage.subProc_id_eq` |
| `dae_outPfx`, `dae_inPfx` | move | `SoftwareLanguage.dae_outPfx`, `dae_inPfx` |
| `stepDpApp_alt` | move | `SoftwareLanguage.stepDpApp_alt` |
| `bisim_disc_match` | move | `ProcEquiv.bisim_disc_match`, now a corollary of `bisim_step_disc` |
| `bisim_dae` | duplicate | `ProcEquiv.bisim_dae`, which already existed |
| `link_par_triple_discEx`, `link_par_triple_delEx`, `link_par_triple_out`, `link_par_triple_in`, `link_par_triple_del`, `link_par_triple_discW_1/2/3`, `link_par_triple_out_neq1/2/3`, `link_par_triple_in_neq1/2/3` | move | The same names in `SoftwareLanguage.v`, each a corollary of `parTriple_disc_inv` or `parTriple_del_inv` |
| `link_ent_soft_disc` | move | `EntityLanguage.link_ent_soft_disc` |
| `ovReady_prev_out_ctx`, `ovReady_prev_in_ctx`, `ovReady_prev_del_ctx` | helper | `outPrefix_bisim_context`, `inPrefix_bisim_context`, `del_bisim_context` |
| `ovReady_prev_app_unf`, `currEq_cond_true_app`, `nextPincCheck_cond_false_app`, `bc_outProc_out_app` | helper | `app_bisim_def` |
| `currOK_next_app_bisim`, `ovlp_abort_in_appbisim` | helper | `app_bisim` |
| `ovlp_abort_in_appbisim0` | helper | `app_bisim_nil` |
| `bc_outProc_out_del_sim`, `bc_outProc_out_del_bisim` | helper | `del_bisim_guard` |
| `ovlp_abort_in_bisim_step` | helper | `bisim_step_disc` |
| `ovlp_abort_in_notNextSince_aux` | helper | `bisim_disc_match` on `bisim_trans (bisim_symm _) _` |
| `listener_outProc_out_not_bisim_fwd` (tactic) | helper | `bisim_step_disc` |
| `link_reach_triple_tau_inv`, `prot_outProc_in_not_inv`, `ovlp_abort_in_notNextSince_inv` (tactics) | helper | `invert_disc_prefixes` |
| `link_reach_triple_tau_noact`, `link_reach_triple_tau_pick` (tactics) | helper | `prot_outProc_in_not_contra`, which stays; `parTriple_disc_inv`, whose six synchronisation cases are the goal's disjuncts |
| `ovReady_del_pres_tac` (tactic) | helper | `bisim_del_pres` with `del_self_tac` |
| `link_par_triple_discW_1_tac`, `link_par_triple_out_neq1_tac` (tactics) | helper | Nothing: they only proved the moved lemmas |

## `src/protocol/EntAuxResults.v`

| Removed | Kind | Replaced by |
|---|---|---|
| `mst_tout_mCurr_in` | move | `ModeStateLanguage.mst_tout_mCurr_in` |
| `link_ent_proc_neq_disc` | move | `EntityLanguage.link_ent_proc_neq_disc` |
| `gotRangeStateEnt_urgent_aux2` | helper | `ent_del_mCurr_in_not` |
| `currCompStateEnt_urgent_aux3` | helper | `ent_del_mStable_mNext_in_not` |
| `tfsNext_next_ent_app`, `tfsCurr_next_ent_app_bisim` | helper | `app_bisim_def`, `app_bisim` |
| `tfsNext_next_ent_soft`, `tfsCurr_next_ent_soft` | helper | `link_ent_soft_disc` |
| `tfsNext_next_ent_par` | helper | `link_par_triple_discEx` with `link_par_triple_discW_2` |
| `tfsCurr_next_ent_par2` | helper | `link_par_triple_discW_2` |
| `tfsCurr_next_ent_bisim_step` | helper | `bisim_step_disc` |

## `src/protocol/NetAuxBasics.v`

| Removed | Kind | Replaced by |
|---|---|---|
| `procNeq_tau_net`, `link_net_ent_disc`, `del_net_ent`, `inRange_acc_input`, `curr_switch_ent_tau`, `net_del_elim` | move | The same names in `NetworkLanguage.v` |
| `procNeq_tau_net_aux1`, `procNeq_tau_net_aux2`, `switchCurr_switchListen_net_link_aux1` | helper | `stepDiscNet_nonTau_pres_proc` |
| `outgoing_del_aux1` | helper | `timedList_del_ge` |
| `incomingNetNotif_disc_pres_aux1`, `_aux2`, `_aux3` | helper | `timedList_out_pres_pos`, `notifList_in_pres`, `notifList_out_pres_pos` |
| `incomingNetNotif_disc_pres_aux4` | helper | `stepEnt_disc_pres_notif_pos` |
| `inRange_acc_input_fwd_ex` | helper | `link_net_ent_disc_fwd_ex` |
| `outNet_incomingNetNotif_aux` | helper | `notifList_in_hd` |
| `link_net_prot_reach_aux1` | duplicate | `initialNet_ent`, which already existed in the file and now sits before its first use |

## Imports

`NetAuxBasics.v`, `EntAuxResults.v`, `NARMisc.v` and `NARMsgPosition.v` now import `ComhCoq.lang.ProcEquiv`, whose results they reached through `ProtAuxResults.v` before.
