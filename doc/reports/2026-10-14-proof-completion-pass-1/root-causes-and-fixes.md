# Root causes and proposed fixes

[← Proof completion, pass 1](README.md)

Almost all of the 108 targets that can't be proved as written fail for one of twelve reasons. The ones that matter most to `safety` come first.

**Every fix here changes a statement, a definition or the axioms, so each one needs human approval.** None of them has been applied.

The "Affected lemmas" lists come from the 93 audited write-ups. The 15 unaudited ones are marked in the [lemma index](lemmas/README.md). A lemma can appear under more than one cause, and "(cone)" marks lemmas that `safety` depends on.

## 1. Incomplete component-state predicates

**What's wrong.** `overlapState` and `listenerState` are marked `INCOMPLETE` in the source, and they only list some of the states. For example, they leave out `tfsStart` and `paused`. So `reachableProt_triple`, which says "every reachable protocol process is a triple of component states", is false. One `chanBad?` step from the initial process already escapes `overlapState`. That lemma is in the cone and many others lean on it, so this is the most structural problem.

**Fix.** Define each component predicate as "reachable from that component's initial process", e.g. `overlapState := compReach dormant`. Lemmas that consume these predicates then need to be re-proved by induction on `compReach` instead of by case analysis.

**Checked?** Yes. A prover proved `reachableProt_triple` under this definition, using model axioms only. See `reachableProt_triple_fix` in [`evidence/fixes/`](evidence/fixes/reachableProt_triple_fix.v).

<details><summary>Affected lemmas (6, 3 in the cone)</summary>

[`currSince_del_bcWait`](lemmas/NARTop.md#currsince_del_bcwait) (cone), [`ovWait_sent`](lemmas/NARTop.md#ovwait_sent) (cone), [`reachableProt_triple`](lemmas/ProtAuxResults.md#reachableprot_triple) (cone), [`tfs_state_rel`](lemmas/NARInsuff.md#tfs_state_rel), [`del_pres_bkwd_tfsStart`](lemmas/NetAuxBasics.md#del_pres_bkwd_tfsstart), [`ovReady_del_pres_bkwd_net`](lemmas/NetAuxBasics.md#ovready_del_pres_bkwd_net)

</details>

## 2. Missing reachability hypotheses

**What's wrong.** This is the most frequent cause. State predicates are bisimilarity classes, so an unreachable term also satisfies them: `del 1 X`, a `nilProc` component, or a bare `chanPos?` prefix. Such terms break the backtracking, delay-preservation and urgency lemmas.

**Fix.** Add `reachableNet n`, `reachableProt p` or `reachableEnt e`, as appropriate. In almost every case the caller already has that hypothesis in scope, so the change doesn't ripple far.

**Checked?** For several lemmas, the fixed statement is proved. Each write-up says which.

<details><summary>Affected lemmas (27, 10 in the cone)</summary>

[`tfsBc_failSafe`](lemmas/EntAuxResults.md#tfsbc_failsafe) (cone), [`insuff_incomingNotif_abort`](lemmas/NARInsuff.md#insuff_incomingnotif_abort) (cone), [`insuff_incomingNotif_bad`](lemmas/NARInsuff.md#insuff_incomingnotif_bad) (cone), [`notifBadPathNet_urgent`](lemmas/NARMisc.md#notifbadpathnet_urgent) (cone), [`switchBc_nextMode_net`](lemmas/NARMisc.md#switchbc_nextmode_net) (cone), [`bcWaitNet_del_bkwd`](lemmas/NetAuxBasics.md#bcwaitnet_del_bkwd) (cone), [`nextSince_del_ovWait`](lemmas/NetAuxBasics.md#nextsince_del_ovwait) (cone), [`rangeBad_next_net`](lemmas/NetAuxBasics.md#rangebad_next_net) (cone), [`switch_states_mState`](lemmas/NetAuxBasics.md#switch_states_mstate) (cone), [`tfsListen_failSafe_net`](lemmas/NetAuxBasics.md#tfslisten_failsafe_net) (cone), [`currEq_mode`](lemmas/EntAuxResults.md#curreq_mode), [`tfsCurr_failSafe`](lemmas/EntAuxResults.md#tfscurr_failsafe), [`tfsNext_prev_ent`](lemmas/EntAuxResults.md#tfsnext_prev_ent), [`init_nextMode_net`](lemmas/NARMisc.md#init_nextmode_net), [`msgBadPathNet_urgent`](lemmas/NARMisc.md#msgbadpathnet_urgent), [`del_pres_bkwd_tfsStart`](lemmas/NetAuxBasics.md#del_pres_bkwd_tfsstart), [`ovReady_del_pres_bkwd_net`](lemmas/NetAuxBasics.md#ovready_del_pres_bkwd_net), [`ovReady_prev_net_strong`](lemmas/NetAuxBasics.md#ovready_prev_net_strong), [`ovWait_del_pres_bkwd_net_strong`](lemmas/NetAuxBasics.md#ovwait_del_pres_bkwd_net_strong), [`ovWait_del_pres_net`](lemmas/NetAuxBasics.md#ovwait_del_pres_net), [`ovWait_prev_net`](lemmas/NetAuxBasics.md#ovwait_prev_net), [`ovWait_prev_net_strong`](lemmas/NetAuxBasics.md#ovwait_prev_net_strong), [`tfsCurrStateNet_bktrk_net`](lemmas/NetAuxBasics.md#tfscurrstatenet_bktrk_net), [`tfsCurrState_del_pres_net`](lemmas/NetAuxBasics.md#tfscurrstate_del_pres_net), [`tfsNext_currModeNet_eq`](lemmas/NetAuxBasics.md#tfsnext_currmodenet_eq), [`tfsStart_prev_net`](lemmas/NetAuxBasics.md#tfsstart_prev_net), [`tfsState_del_pres_net`](lemmas/NetAuxBasics.md#tfsstate_del_pres_net)

</details>

## 3. Untyped process inputs

**What's wrong.** A process can input a `Time` on a channel meant for a `Mode`. That reaches stuck states, so the forward-tracking `*_next` lemmas are false. Thesis Remark 4.1 leaves channels untyped on purpose.

**Fix.** Either give channels sorts (arities and types), or add a well-typed-input hypothesis to these lemmas.

<details><summary>Affected lemmas (5, 0 in the cone)</summary>

[`currComp_next`](lemmas/ProtAuxResults.md#currcomp_next), [`currOK_listening_track`](lemmas/ProtAuxResults.md#currok_listening_track), [`gotRange_next`](lemmas/ProtAuxResults.md#gotrange_next), [`rangeBad_next`](lemmas/ProtAuxResults.md#rangebad_next), [`tfsStart_next`](lemmas/ProtAuxResults.md#tfsstart_next)

</details>

## 4. Listener notification arity (also in the thesis)

**What's wrong.** The interface delivers notifications as `⟨r, m, l⟩`, per IFWD-OUT and Remark 4.15. But `listening` inputs `chanAN⟨r, m''⟩`, which is also how thesis p.134 has it. By PFX-IN-MSG an input only consumes a message of the same length (|~v| = |~x|), so the listener can never consume a real notification. That silently disables the coverage-degradation → `rangeBad` safety mechanism. `listening_AN_prot`, which is in the cone, is false.

**Fix.** `chanAN⟨r, m'', l'⟩?`. The proof script for the 3-field version is ready.

<details><summary>Affected lemmas (1, 1 in the cone)</summary>

[`listening_AN_prot`](lemmas/ProtAuxResults.md#listening_an_prot) (cone)

</details>

## 5. Range typing: `eSubtract` vs `bPossInc`

**What's wrong.** `gotMsg` computes the range with `eSubtract`, which yields a `baseNonneg`. But `bPossInc` only evaluates on a `baseDistance`. So after handling any message, the listener gets stuck at `currPincCheck`, and the incompatibility-detection path never reaches `badOvlp`.

**Fix.** Make `bPossInc` accept any non-negative value, or convert in `gotMsg`.

<details><summary>Affected lemmas (2, 0 in the cone)</summary>

[`gotMsg_gotRange_track_ent`](lemmas/EntAuxResults.md#gotmsg_gotrange_track_ent), [`gotMessage_next`](lemmas/ProtAuxResults.md#gotmessage_next)

</details>

## 6. `noSyncNow` is missing the thesis's position-read clause

**What's wrong.** Thesis Def 4.22 forbids delay while a process can read its position. The formal `noSyncNow` leaves that clause out. So an entity that can read on `chanPos` can still let time pass, which means `gotMsg`, `pending` and `ovWait` with `y = 0` aren't urgent. Several urgency lemmas are false as a result.

**Fix.** Restore the clause in `noSyncNow`/`stepTeDel`.

**Checked?** Yes, on a local copy. With the clause restored, `gotMsgStateEnt_urgent` proves in a few lines. See [`evidence/fixes/gotMsgStateEnt_urgent_noSyncNow.v`](evidence/fixes/gotMsgStateEnt_urgent_noSyncNow.v).

<details><summary>Affected lemmas (4, 2 in the cone)</summary>

[`bcWaitNet_del_bkwd`](lemmas/NetAuxBasics.md#bcwaitnet_del_bkwd) (cone), [`nextSince_del_ovWait`](lemmas/NetAuxBasics.md#nextsince_del_ovwait) (cone), [`gotMsgStateEnt_urgent`](lemmas/EntAuxResults.md#gotmsgstateent_urgent), [`ovWait_del_pres_bkwd_net_strong`](lemmas/NetAuxBasics.md#ovwait_del_pres_bkwd_net_strong)

</details>

## 7. `stepDeTest` changes the mode state without the process

**What's wrong.** `stepDeTest` models an environment mode request. It changes the mode state without the process taking part, which breaks the four `NetAuxDefs.*_modeState_eq` lemmas and `mState_switch_states`.

**Fix.** Weaken those lemmas to "the mode state is preserved, or the process is unchanged and the mode state was stable", and adjust their two callers. Alternatively, re-model mode requests.

<details><summary>Affected lemmas (5, 0 in the cone)</summary>

[`mState_switch_states`](lemmas/NetAuxBasics.md#mstate_switch_states), [`msgAbort_modeState_eq`](lemmas/NetAuxDefs.md#msgabort_modestate_eq), [`msgBad_modeState_eq`](lemmas/NetAuxDefs.md#msgbad_modestate_eq), [`notifAbort_modeState_eq`](lemmas/NetAuxDefs.md#notifabort_modestate_eq), [`notifBad_modeState_eq`](lemmas/NetAuxDefs.md#notifbad_modestate_eq)

</details>

## 8. Missing WRITE-STBL rule

**What's wrong.** The thesis has a WRITE-STBL rule, but `stepDiscEnt` doesn't. So a process's `chanMStable!` never synchronises with the mode state, and neither `ovAbort` nor the `tfsNext` self-loop can ever abort a transition.

**Fix.** Add the rule.

<details><summary>Affected lemmas (1, 0 in the cone)</summary>

[`nextMode_pres_fwd_net`](lemmas/NetAuxBasics.md#nextmode_pres_fwd_net)

</details>

## 9. Internal synchronisation on mode-state channels

**What's wrong.** Two components can synchronise with each other on `chanMNext`/`chanMStable` and bypass the mode state. That breaks `currComp`/`currOK` tracking.

**Fix.** Add a `~ modeStateChan c` premise to `stepDpSyncLR`/`stepDpSyncRL`.

<details><summary>Affected lemmas (4, 2 in the cone)</summary>

[`rangeBad_next_net`](lemmas/NetAuxBasics.md#rangebad_next_net) (cone), [`switch_states_mState`](lemmas/NetAuxBasics.md#switch_states_mstate) (cone), [`currComp_listening_track_ent`](lemmas/EntAuxResults.md#currcomp_listening_track_ent), [`currComp_nextPincCheck_track_ent`](lemmas/EntAuxResults.md#currcomp_nextpinccheck_track_ent)

</details>

## 10. Parameter tracking under bisimulation

**What's wrong.** Time subtraction is truncated at zero, so `ovWait m t x y` is bisimilar to `ovWait m t' x y` whenever both `t` and `t'` are at most `period m`. So lemmas that conclude `t = t'` are false. Similarly, timers count down under delay, so lemmas that claim they're preserved are false.

**Fix.** Weaken the conclusions to what callers actually use, usually `m = m'` and `y = period m`, or an existential over the timer values.

<details><summary>Affected lemmas (7, 1 in the cone)</summary>

[`ovWait_del_pres`](lemmas/ProtAuxResults.md#ovwait_del_pres) (cone), [`gotRange_currPincCheck_track_ent`](lemmas/EntAuxResults.md#gotrange_currpinccheck_track_ent), [`nextEq_mode`](lemmas/EntAuxResults.md#nexteq_mode), [`tfsNext_currMode`](lemmas/EntAuxResults.md#tfsnext_currmode), [`ovReady_wait_track_net`](lemmas/NetAuxBasics.md#ovready_wait_track_net), [`ovWait_del_pres_net`](lemmas/NetAuxBasics.md#ovwait_del_pres_net), [`ovWait_track_net`](lemmas/NetAuxBasics.md#ovwait_track_net)

</details>

## 11. Gaps in the model axioms

**What's wrong.** Nothing in the axioms forbids `failSafeSucc m = m`, `modeTransTime = 0`, or a `Mode` type with only one element. Some lemmas are false in those degenerate models.

**Fix.** Prefer adding a `~ failSafe m` hypothesis to the affected lemmas. Where these lemmas have callers, the callers already have it in scope. For the `modeTransTime` case, either add `0 < modeTransTime m m' p` as an axiom, or add the `currSince` hypothesis that the only caller already has.

**A caution on the axiom route.** An axiom `failSafeSucc m <> m` would also fix the first case. But it forces at least two distinct fail-safe modes, and the non-degenerate model in [`src/ModelConsistency.v`](../../../src/model/ModelConsistency.v) doesn't satisfy it, because there `failSafeSucc Safe = Safe`. `0 < modeTransTime` is fine, since that model sets every transition time to 1.

<details><summary>Affected lemmas (3, 0 in the cone)</summary>

[`tfsState_not_currSince`](lemmas/NARMisc.md#tfsstate_not_currsince), [`tfs_zero_disc_pres`](lemmas/NARMisc.md#tfs_zero_disc_pres), [`tfsBc_not_currSince`](lemmas/NARTop.md#tfsbc_not_currsince)

</details>

## 12. Small statement bugs

**What's wrong, and the fix, one at a time:**

- `nextModeEnt_not_stable` has `m2 : ModeState` where `Mode` was meant, which makes it say "never". Annotate `(m2 : Mode)`. With the `nextModeEnt` stub defined, the fixed lemma is `intro H; inversion H`.
- `delProc_minus_guard` is missing `evalExpFunTime e = Some t`. It underlies `delAddSoft`, which is already `Qed`, and through that `timeSplit_ent` and `timeSplit_net`. Add the hypothesis.
- `outgoing_timeout_disc` quantifies the message position universally instead of existentially. Move it into the existential. The fixed version is fully proved.
- `link_ent_outList` uses `-tl-` where `-ol-` was meant. The fixed version is proved.
- `evalBoolExpFalseTot` is an iff that fails on ill-formed expressions. Keep only the `->` direction, which is re-proved, or add `evalBoolExpFun e <> None`.
- `inList_received_in` and `notifList_received_in` were copied from `outList_received_in` and kept its `msgLatency` timestamp. Buffering actually stamps `zeroTime` and `adaptNotif` respectively. Correct the timestamp, which is proved, or delete them, since neither has any users.

<details><summary>Affected lemmas (7, 2 in the cone)</summary>

[`link_ent_outList`](lemmas/EntAuxResults.md#link_ent_outlist) (cone), [`outgoing_timeout_disc`](lemmas/NARMisc.md#outgoing_timeout_disc) (cone), [`nextModeEnt_not_stable`](lemmas/EntAuxResults.md#nextmodeent_not_stable), [`inList_received_in`](lemmas/InterfaceLanguage.md#inlist_received_in), [`notifList_received_in`](lemmas/InterfaceLanguage.md#notiflist_received_in), [`evalBoolExpFalseTot`](lemmas/ProcEquiv.md#evalboolexpfalsetot), [`delProc_minus_guard`](lemmas/SoftwareLanguage.md#delproc_minus_guard)

</details>

## Parameter stubs

Several lemmas can't be proved simply because the predicate they mention is an opaque `Parameter`. These are suggested definitions, which haven't been applied. Most were checked in explore mode against the lemmas they unblock.

| Stub | Suggested definition | What it unblocks |
|---|---|---|
| `reachableEnt` (EntAuxDefs) | The inductive closure of `initialEnt` under discrete and delay entity steps. It has to move below `initialEnt`. | `reachable_net_ent`, `reachable_ent_prot` and others. Checked in explore mode. |
| `currModeNet m i n` (NetAuxBasics) | `exists e, e @ i .: n /\ currModeEnt e = m`, or equivalently `liftEntNet (fun e => currModeEnt e = m)`. | `currMode_intro`, `currMode_pres_*`, `currMode_ent_ex` and `currModeNet_del_pres`. Several were checked. |
| `nextModeNet m i n` | `liftEntNet (nextModeEnt m)` | `nextMode_ent_ex`, `nextModeNet_del_pres` |
| `nextModeEnt m e` (EntAuxDefs) | A one-constructor inductive over `<\| m0, m, t \|>`, or `EntityLanguage.nextModeEnt e = Some m`. The two were proved equivalent. | `nextMode_ent_mState` and others |
| `inPosEnt l e` | A one-constructor inductive saying `[\|p, l, h, k\|]` is at `l` | `inPos_ent_net`, which becomes a one-liner |

<details><summary>Lemmas blocked on a stub (21, 12 in the cone)</summary>

[`bcReady_pos`](lemmas/EntAuxResults.md#bcready_pos) (cone), [`ovReady_pos`](lemmas/EntAuxResults.md#ovready_pos) (cone), [`switchCurr_nextSince_nextMode_net`](lemmas/NARMisc.md#switchcurr_nextsince_nextmode_net) (cone), [`currModeNet_del_pres`](lemmas/NetAuxBasics.md#currmodenet_del_pres) (cone), [`currMode_ent_ex`](lemmas/NetAuxBasics.md#currmode_ent_ex) (cone), [`currMode_intro`](lemmas/NetAuxBasics.md#currmode_intro) (cone), [`currMode_pres_bkwd`](lemmas/NetAuxBasics.md#currmode_pres_bkwd) (cone), [`inPos_ent_net`](lemmas/NetAuxBasics.md#inpos_ent_net) (cone), [`rangeBad_next_net`](lemmas/NetAuxBasics.md#rangebad_next_net) (cone), [`reachable_net_ent`](lemmas/NetAuxBasics.md#reachable_net_ent) (cone), [`switch_states_mState`](lemmas/NetAuxBasics.md#switch_states_mstate) (cone), [`tfsListen_failSafe_net`](lemmas/NetAuxBasics.md#tfslisten_failsafe_net) (cone), [`nextMode_ent_mState`](lemmas/EntAuxResults.md#nextmode_ent_mstate), [`ovAbort_unstable`](lemmas/EntAuxResults.md#ovabort_unstable), [`reachable_ent_prot`](lemmas/EntAuxResults.md#reachable_ent_prot), [`switchCurr_mState`](lemmas/EntAuxResults.md#switchcurr_mstate), [`currMode_pres_fwd`](lemmas/NetAuxBasics.md#currmode_pres_fwd), [`init_nextMode_net`](lemmas/NetAuxBasics.md#init_nextmode_net), [`nextModeNet_del_pres`](lemmas/NetAuxBasics.md#nextmodenet_del_pres), [`nextMode_ent_ex`](lemmas/NetAuxBasics.md#nextmode_ent_ex), [`nextMode_pres_fwd_net`](lemmas/NetAuxBasics.md#nextmode_pres_fwd_net)

</details>

## Smaller decisions

- **Package the model axioms as a `Module Type`.** Turn `ComhBasics`'s axioms into `Module Type ComhParams` and make each downstream file a functor over it. Alternatively, put the whole development in one `Section` with the parameters as variables.
  - `safety` would then read "for every valid instantiation", and `ModelConsistency.concrete_model` becomes the witness that one exists.
  - **Cost:** mechanical but broad, since 22 source files use these parameters.
  - **Risk:** functor boilerplate, and notation scoping across functor boundaries.
  - **Lighter option:** keep the global axioms and keep stating the relationship through `global_model`, as now.
- **Prune duplicates of stdlib lemmas.** Some project lemmas duplicate stdlib ones:
  - `not_Rle_lt` = `Rnot_le_lt`
  - `RltMinusBothSides` = `Rlt_Rminus`
  - `Rle_zero_plus` = `Rplus_le_le_0_compat`
  - `Rmult_lt_0` = `Rmult_lt_0_compat`
  - and so on.

  About 30 more are now one-line `lra` facts. Separately, the project's own `Rplus_lt_reg_l`/`_r` shadow the stdlib lemmas of the same names, with the sides swapped, which is a trap for anyone reading the code.
- **Fix or delete unused false lemmas.** Several of the false lemmas have no users at all. Deleting them is simpler than fixing them, but deleting results is a human decision.
