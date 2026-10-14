# Unproved lemmas in `NARInsuff`

[← Lemma index](README.md) · [Report summary](../README.md)

3 lemmas here could not be proved as stated, 2 of them in `safety`'s assumption cone. Each section gives the lemma's intent, why it fails, how the failure ripples up towards `safety`, and a suggested fix.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `insuff_incomingNotif_abort`

- **Where:** `src/NARInsuff.v` line 133 · **Theorem** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Add (rn : reachableNet n); both callers have p : reachableNet n in scope. Fixed version only argued (in reachable nets it holds trivially via the left disjunct because of the chanAN arity bug; after fixing listening arity it also needs mode-transition irreflexivity or a notifBadPathNet disjunct).

- **Status:** FALSE (counterexample), given the intended definition of the `nextModeNet` stub; with the stub left opaque it is also BLOCKED-ON-STUB (`nextModeNet`). The missing hypothesis is `reachableNet n`.
- **Intent:** Entity `i` has next mode `m` and holds a pending notification `<r, m, l>` with timestamp 0 whose coverage `r` is insufficient for `m`. After any discrete step, either the notification is still pending at timestamp 0, or the step consumed it and entity `i` is now on the notification-abort path.
- **Failure:** The statement quantifies over **all** networks `n`, not just reachable ones. So the process at `i` can be any term, including one that consumes the notification and then does nothing.
  Counterexample, checked in Rocq (`insuff_incomingNotif_abort_cex` in `NARInsuff.insuff_incomingNotif_abort.v`, `--explore` rc=0):
  `n = [ [| chanAN<[vR,vM'',vL]>? nilProc, l0, (inList [], outList [], notifList [<([r,m,l], 0)>]), <|m, m, 0|> |] ]`
  `n' = [ [| nilProc, l0, (inList [], outList [], notifList []), <|m, m, 0|> |] ]`
  with `a = anTau` (built with `stepDnTauHead`/`stepDeNotif`/`stepDpIn`/`stepIntFwdNotif`).
  Here `nextModeMState <|m,m,0|> = Some m`, and the notification is incoming at time 0 in `n`. In `n'` the notification list is empty, so it is not incoming, and `nilProc` is not a listener state, so `notifAbortPathNet 0 n'` fails.
  `insuff_incomingNotif_abort_refuted` lifts this to a refutation of the target for **every** interpretation `NM` of `nextModeNet` that contains "lift `nextModeEnt`" (`e @ i .: n -> nextModeMState (mstEnt e) = Some m -> NM m i n`), which is the documented intent of both stubs. `insuff_incomingNotif_abort_insuff_zero` shows that the `~sufficient m r` premise is satisfiable for every `m` (take `r = 0`).
  While the stub stays opaque, no proof is possible either: no admitted fact that is allowed for use gives an elimination principle for `nextModeNet` (see `NetAuxBasics.nextMode_ent_ex.fail.md`).
- **Ripple-up:** In the safety cone. Used by `instant_insuff_abort` (NARInsuff.v:343) and `instant_insuff_bad` (NARInsuff.v:468). In both callers `p : reachableNet n` for the pre-state `n` of the step `w` is in scope (`instant_insuff_abort` already passes `p` to `notifAbort_not_nextSince`, and `instant_insuff_bad` uses `p` for `paused_switch_net` on `n`). So adding reachability costs the callers nothing.
- **Suggested fix:**
  ```coq
  Theorem insuff_incomingNotif_abort (n n' : Network) (a : ActDiscNet) (m : Mode)
    (r : Distance) (l : Position) (i : nat) (rn : reachableNet n) :
    nextModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
    incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
    incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
    notifAbortPathNet i n'.
  ```
  The callers change as follows. At line 343, `eapply (insuff_incomingNotif_abort _ _ _ _ _ _ _ p). apply Q.` At line 468, `lets IIA : insuff_incomingNotif_abort p NM w H0 IL.`
  Why the fix is provable, and a caveat: in a reachable network, entity `i` runs a protocol process. The **only** `chanAN` input in the protocol is `listening`'s `chanAN<[vR, vM'']>?` (SoftwareLanguage.v:169), which is 2-ary, and `stepDpIn` requires `length l1 = length l2`. The 3-ary notification `[r, m, l]` can therefore never be consumed. Every discrete step keeps it in the notification list (`stepNotifList` only appends or removes the consumed head), so the fixed statement holds via the **left** disjunct. That is a consequence of the arity mismatch already reported in `ProtAuxResults.listening_AN_prot.fail.md`, not of the protocol's design. Once `listening` is fixed to input `[vR, vM'', vL]`, the right disjunct is reached through `checkRange` → `rangeBad m`, which is `napRng`. But `napRng` also needs `currModeMState k <> m`. The model axioms do not make `-mtr->` irreflexive, so a mode state `<|m, m, t|>` is reachable if `m -mtr-> m`. That case would additionally need either an irreflexivity axiom for `modeTransRel` or `\/ notifBadPathNet i n'` in the conclusion.
- **Partial proof:** `NARInsuff.insuff_incomingNotif_abort.v` holds the counterexample (`_cex`), the satisfiability lemma (`_insuff_zero`) and the generic refutation (`_refuted`). They are for demonstration and not for splicing. The PROOF section is `Admitted`. The work builds on steal-3's earlier attempt; I fixed two elaboration errors in `_refuted`.

## `insuff_incomingNotif_bad`

- **Where:** `src/NARInsuff.v` line 361 · **Theorem** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add (rn : reachableNet n); only caller instant_insuff_bad has p in scope.

- **Status:** FALSE (counterexample, machine-checked; needs the hypothesis `reachableNet n`)
- **Intent:** Entity `i` is in current mode `m` and has a zero-stamped notification `<r, m, l>` on its AN queue, where `r` is insufficient for `m`. After any discrete step, either the notification is still pending at time 0, or the listener consumed it and the entity is now on the notification-bad path (`checkRange` → `rangeBad m`).
- **Failure:** The statement does not require `n` to be reachable, so the process of entity `i` can be any term. Counterexample, for any `m : Mode`:
  - `n = [ [| inPrefix chanAN [vR, vM'', vL] nilProc, (0,0), {[], [], [<([r0, m, (0,0)], 0)>]}, sing m |] ]` with `r0 = mkDistance 0`.
  - `currModeNet m 0 n` holds by `currMode_intro` (the conjecture that states the intended meaning of the stub).
  - `~ sufficient m r0` holds because `maxMinDistComp m + 2*speedMax*(...) > 0`.
  - The notification is incoming at time 0.
  - `n -NA- anTau -NA> n'` holds via `stepDnTauHead`/`stepDeNotif`, where the process reads the 3-element notification on `chanAN` (`stepDpIn`, lengths 3 = 3) and becomes `nilProc`, and the notif list becomes empty (`stepIntFwdNotif`/`stepNlLift`/`stepTlFwdHd`).
  - In `n'`, the notification is gone, and `notifBadPathEnt` needs a process of the form `p1 $||$ p2 $||$ p3` (`liftListen`), which `nilProc` is not. Both disjuncts fail.

  Verified in Rocq as `insuff_incomingNotif_bad_cex (m : Mode) : ~ (statement)` in `w1b-15/NARInsuff.insuff_incomingNotif_bad.v`, which compiles with `Qed`. `Print Assumptions` shows only model axioms, stdlib classical/FE/PI, `currModeNet`, and `currMode_intro`. So the target plus `currMode_intro` proves `False` once any `Mode` exists.
- **Ripple-up:** Used once, in `NARInsuff.instant_insuff_bad` (line 484: `lets IIB : insuff_incomingNotif_bad CMN w H0 IH0`). That lemma is on the path to `safety` (target is `in_safety_cone=True`). `currMode_intro` is also used directly by `Main.safety`, so this target must not stay admitted alongside it.
- **Suggested fix:** Add reachability:
  ```coq
  Theorem insuff_incomingNotif_bad (n n' : Network) (a : ActDiscNet) (m : Mode)
    (r : Distance) (l : Position) (i : nat) (rn : reachableNet n) :
    currModeNet m i n -> n -NA- a -NA> n' -> ~sufficient m r ->
    incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n ->
    incomingNetNotif [baseDistance r, baseMode m, basePosition l] zeroTime i n' \/
    notifBadPathNet i n'.
  ```
  The only caller has `p : reachableNet n` in context (the `deliveredDisc` predecessor; it is already used there as `paused_switch_net i p`). The call becomes `lets IIB : insuff_incomingNotif_bad p CMN w H0 IH0.` The sibling `insuff_incomingNotif_abort` (line 133) has the same shape. The same counterexample, with `nextModeNet`, likely breaks it too; it should get the same hypothesis.
- **Provability of the fixed statement / further findings:**
  1. **Arity mismatch in the protocol (likely modelling bug).** `SoftwareLanguage.listening` reads AN notifications as `chanAN$<[vR, vM'']>$?`, which takes **2** variables. The interface enqueues `(baseDistance r) :: v` with `v = [baseMode m, basePosition l]`, which has **3** values (`stepIntFwdOut`, `outNet_incomingNetNotif`). `stepDpIn` needs `length l1 = length l2`. So in any reachable network the listener can never consume such a notification. Because no synchronisation is possible, `noSync` holds, and the notification list's `stepNlDrop` rule silently drops the zero-stamped entry on the next delay. The insufficient-coverage notification therefore never reaches the listener, and the `checkRange`/`rangeBad` path is dead code in the current model. This matters for the safety argument and should be checked against the thesis. With the model as it stands, the fixed lemma is true through the left disjunct alone, since a discrete step cannot remove the entry. Proving it, though, needs an invariant over every reachable process that nothing inputs a 3-element list on `chanAN`.
  2. If the listener is fixed to `chanAN$<[vR, vM'', vL]>$?` (or the interface stops sending the position), the intended proof goes through `checkRange` → `rangeBad m''` with `nbpRng`. That needs `currModeMState k = m`, i.e. an **elimination** rule for the stub: `currModeNet m i n -> e @ i .: n -> currModeEnt e = m`. That holds if `currModeNet m := liftEntNet (fun e => currModeEnt e = m)`, which with entity uniqueness in the network also gives back `currMode_intro`. Right now only the intro direction exists, so the fixed statement is also BLOCKED-ON-STUB (`currModeNet`) for the intended proof route.
- **Partial proof:** `w1b-15/NARInsuff.insuff_incomingNotif_bad.v` holds the machine-checked counterexample (HELPERS) and `Proof. Admitted.`

## `tfs_state_rel`

- **Where:** `src/NARInsuff.v` line 34 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `incomplete-definition (overlapState/listenerState)`
- **Fix (audit summary):** Add net-level backtracking lemmas tfsBc_prev_net/tfsListen_prev_net with reachableNet; prove them via a compReach-style overlapState (reachableProt_triple fix).

- **Status:** BLOCKED-ON-DEFINITION (`overlapState` is incomplete, so no sound reachability invariant exists to backtrack `tfsBc`/`tfsListen`). The lemma is believed true. Proved modulo two missing backtracking lemmas.
- **Intent:** in a reachable network, if entity `i` is in some tfs state, then the `tfs m t i n p` history relation holds for some mode `m` and time `t`, along the given reachability derivation `p`.
- **Failure:** the proof is by induction on `p : reachableNet n`. Everything except two cases goes through (see partial proof):
  - *Init:* there is no tfs state in an initial network. This is proved honestly: the overlap component is literally `dormant`, and `dormant` is not bisimilar to `tfsStart` (it has an `chanAbort*?` that `tfsStart` lacks) nor to `tfsNext`/`tfsCurr`/`tfsBc`/`tfsListen` (each has an output that `dormant` lacks). Helpers `tfs_state_rel_dormant_not_tfs` and `tfs_state_rel_init_not_tfs` compile with `Qed`.
  - *Delay:* `tfsState_del_pres_net` + IH + `tfsDel`.
  - *Discrete:* split on `tfsState_elim_net` at `n'`:
    - `tfsStart`: use `tfsBase` with `currMode_intro`.
    - `tfsNext`: `tfsNext_prev_net`, IH, `tfsDisc`.
    - `tfsCurr`: `tfsCurrStateNet_bktrk_net`, IH, `tfsDisc`.
    - **`tfsBc` and `tfsListen`: no backtracking lemma exists** at the process, entity or net level. These cases need "the previous state of `i` was a tfs state".
  - These two backtracking facts can't be derived honestly from the current development. Backtracking needs to know the *shape* of the predecessor's overlap component, i.e. a reachability invariant. The only one available, `ProtAuxResults.reachableProt_triple`, is **inconsistent**: it proves `False` from the model axioms alone (see `w1b-03/ProtAuxResults.reachableProt_triple.inconsistent.cex.v`, explore rc=0). The cause is that `overlapState` has only the `dormant`/`ovWait` constructors (marked `INCOMPLETE` at ProtAuxDefs.v:126). Using it would make the proof vacuous, so I didn't.
- **Ripple-up:** used only at NARInsuff.v:87, inside the commented-out proof of `currModeNet_notifBad_pres_bkwd` (which is `Admitted (*R*)`). Not in the safety cone.
- **Suggested fix:** add the two missing net-level backtracking lemmas (same `#lift-track-net` family as `tfsStart_prev_net`/`tfsNext_prev_net`, but *with* reachability, which they genuinely need):
  ```coq
  Lemma tfsBc_prev_net i n n' a : reachableNet n ->
    tfsBcStateNet i n' -> n -NA- a -NA> n' ->
    tfsBcStateNet i n \/ tfsCurrStateNet i n.
  Lemma tfsListen_prev_net i n n' a : reachableNet n ->
    tfsListenStateNet i n' -> n -NA- a -NA> n' ->
    tfsListenStateNet i n \/ tfsBcStateNet i n.
  ```
  These are true by inspection of SoftwareLanguage.v. The only overlap process with a step into `tfsBcN` is `tfsCurr` (`chanMCurr!tfsBcN`). Into `tfsListenN` there are only `tfsBc` (`chanTrans!`) and `tfsListen` (`chanAbort?`/`chanBad?` self-loops). To prove them for real, complete `overlapState` with all 13 overlap states and prove `reachableProt_triple` (closure of each component's state set under the step relations). With these two lemmas, the partial proof below closes with `Qed`. Replace the two `tfs_state_rel_*_prev` admitted helpers with `tfsStateNet` lifts of the disjuncts.
- **Partial proof:** `w1b-03/NARInsuff.tfs_state_rel.v` (explore rc=0). The whole induction is complete. The only `Admitted` items are the helpers `tfs_state_rel_tfsBc_prev` and `tfs_state_rel_tfsListen_prev`, each stated as `reachableNet n -> tfs{Bc,Listen}StateNet i n' -> n -NA- a -NA> n' -> tfsStateNet i n`. It also relies on these existing admitted lemmas: `tfsNext_prev_net` (via `tfsNext_prev_ent`), `tfsCurrStateNet_bktrk_net`, `tfs*_tfs_net`, `tfsState_del_pres_net`, `currMode_intro`.
