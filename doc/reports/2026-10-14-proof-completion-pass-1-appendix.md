# Appendix: per-lemma write-ups (pass 1)

One section per target that could not be proved as stated. "Audit" is the verified
classification (see the main report for the classes); the body is the prover's write-up.
Where several provers wrote up the same target, all write-ups are included.

## NetAuxBasics

### `NetAuxBasics.switch_states_mState`

- **Where:** `src/NetAuxBasics.v` line 201 · **Lemma** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `stub; missing-reachability; mode-chan-internal-sync`
- **Fix (audit summary):** Define the currModeNet/nextModeNet stubs and add `reachableNet n ->` (call site NARMisc.currSince_curr has p; `try assumption` closes it). Fixed version only argued.

- **Status:** BLOCKED-ON-STUB (`currModeNet`, `nextModeNet`). It also NEEDS-HYPOTHESIS `reachableNet n`: even with the intended stub definitions the statement is false without it. The counterexample is checked in Rocq.
- **Intent:** if entity `i` moves its overlap component from `switchCurr` to `switchListen` in one discrete network step, and its next mode was `m`, then its current mode afterwards is `m`. The step is the `chanMCurr` write that makes the mode state finalise the switch (thesis Def. 6.11, base case of `currSince`).

## Failure

1. **Stub.** The conclusion is `currModeNet m i n'`, and `currModeNet` is an opaque `Parameter` (NetAuxBasics.v:56). In lines 1–201 of NetAuxBasics.v the stubs appear only in their own declarations (lines 56 and 65). No imported module can mention them. So nothing visible constrains `currModeNet` or `nextModeNet`.
   - Interpret `currModeNet := fun _ _ _ => False` and `nextModeNet := fun _ _ _ => True`. The statement then says that no `switchCurr -> switchListen` step exists.
   - Such steps exist for every mode: see the construction below with `m0 = m`.
   - So the statement is independent of the visible context. It is unprovable unless one uses an inconsistent admitted lemma.
2. **Missing reachability (Rocq-verified).** Take the intended definitions
   ```coq
   currModeNet m i n := exists e, e @ i .: n /\ currModeEnt e = m
   nextModeNet m i n := exists e, e @ i .: n /\ nextModeMState (mstEnt e) = Some m
   ```
   The statement still fails. `liftOverlap` puts no constraint on the broadcast and listener slots.
   - Take `p := (chanMCurr ? nilProc) $||$ switchCurr $||$ nilProc` and mode state `k := <|m0, m, 0|>`.
   - Slot 1 inputs `chanMCurr []` and synchronises with the overlap's output `chanMCurr ;! []` (`stepDpSyncRL`). The entity takes a plain `stepDeProcTau`, so `k` is unchanged.
   - Network `[e] -NA- anTau -NA> [e']`: the overlap goes `switchCurr -> switchListen` and the next mode is `m`, but the current mode afterwards is still `m0`.
   - `work/w1b-08/NetAuxBasics.switch_states_mState.cex.v` proves `switch_states_mState_cex : switch_states_mState_stmt -> forall m0 m : Mode, m0 = m`, where `_stmt` is the target with the intended definitions substituted.
   - It compiles in `--explore`. `Print Assumptions` lists only the ComhBasics model axioms plus the stdlib reals, proof irrelevance and functional extensionality. It uses no admitted lemma.
   - The model axioms allow `Mode` to have two elements, so the target is false in such models.

## Ripple-up

- The target is in the safety cone.
- Its only user is `NARMisc.currSince_curr` (NARMisc.v:260, base case). That result is used in NARIncomp.v:402 and NARInsuff.v:483 and 593.
- `currSince_curr` already has `p : reachableNet n` in scope, so the fix costs nothing upstream.

## Suggested fix

1. Define the stubs as above. For `nextModeNet`, the EntAuxDefs `Parameter nextModeEnt` shadows `EntityLanguage.nextModeEnt : Entity -> option Mode`, so write the definition through `nextModeMState (mstEnt e)`.
2. Add reachability to the statement, matching the neighbouring `mState_switch_states`:
   ```coq
   Lemma switch_states_mState : forall (n n' : Network) (i : nat) (a : ActDiscNet)
     (m : Mode), reachableNet n -> n -NA- a -NA> n' -> switchCurrStateNet i n ->
     switchListenStateNet i n' -> nextModeNet m i n -> currModeNet m i n'.
   ```
   The call site `eapply switch_states_mState; try apply w; try assumption.` in `currSince_curr` still works unchanged, because `try assumption` closes `reachableNet n` with `p`.

## Proof plan for the fixed statement under the intended definitions

1. Destruct the hypotheses into `e = [|p,l,h,k|] @ i .: n` (switchCurr overlap, `nextModeMState k = Some m`, by `entInNetUnique`) and `e' = [|p',l',h',k'|] @ i .: n'` (switchListen overlap).
2. Apply `link_net_ent_disc_fwd`. Either `e = e'`, or `e -EA- b ->> e'`.
   - In the `e = e'` case, and in every entity rule that keeps `p`, the overlap would be bisimilar to both `switchCurr` and `switchListen`. That is impossible: `switchCurr` enables `chanMCurr *!` (`switchCurr_mCurr_out`) and `switchListen` does not.
3. `reachableProt p` (`link_net_prot_reach`) makes slots 1 and 3 broadcast and listener states. Neither can input `chanMCurr []` (the listener reads `chanMCurr ;? [m]`, which has a different arity). So the overlap changed by its own output `chanMCurr *!`.
4. The only entity rule that consumes `chanMCurr *!` is `stepDeCurrWrite`, giving `k -ms- chanMCurr @? -ms> k'`.
5. Invert with `stepMsSwitch`: `k = <|m0,m',0|>` and `k' = m'`. With `nextModeMState k = Some m` this gives `m' = m`, so `currModeEnt e' = m`.

Missing auxiliary facts:
- a process lemma "switchCurr-overlap triple steps to switchListen-overlap ⇒ action is `chanMCurr *!`, or a tau sync with slot 1 or 3 on `chanMCurr []`";
- "reachable broadcast and listener states are not enabled on `chanMCurr *?`".

## Partial proof

Not applicable: the target's conclusion is the opaque stub. The validation script is in the `.cex.v` file next to this note.

### `NetAuxBasics.rangeBad_next_net`

- **Where:** `src/NetAuxBasics.v` line 300 · **Lemma** · 2015 label: `D- rangeBad_next_ent` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `stub; missing-reachability; mode-chan-internal-sync`
- **Fix (audit summary):** Define the currModeNet stub and add `reachableNet n ->` (in scope at NARInsuff.notifBad_pres_tfs); add prot-level rangeBad_track and entity-level rangeBad_next_ent (the cited rangeBad_next_ent does not exist).

- **Status:** BLOCKED-ON-STUB (currModeNet). It also NEEDS-HYPOTHESIS (`reachableNet n`) once the stub is defined, and the named dependency `rangeBad_next_ent` does not exist anywhere in the development.
- **Intent:** a listener in `rangeBad m''` either stays there or reads the current mode `m` from the mode state and moves to `currEq m m''`.
- **Failure:**
  1. `currModeNet` is an opaque `Parameter`, and nothing visible before this lemma relates it to entities. With `currModeNet := fun _ _ _ => True` the lemma claims the derivative is `currEq m m''` for *every* `m`. That is false whenever the real read value `m0` differs from `m` and the condition `m =b= m''` distinguishes them (e.g. `m0 = m'' <> m`: `currEq m0 m''` ~ `badOvlp` offers `chanBad!`, `currEq m m''` ~ `currOK m''` does not).
  2. Even with `currModeNet m i n <-> exists e, e @ i .: n /\ currModeEnt e = m`, the lemma is false for unreachable networks. Take the entity process `sleeping $||$ (chanMCurr $<[baseMode m'' as Exp]>$! nilProc) $||$ rangeBad m''` with mode state `sing m`, `m <> m''`. The internal `stepDpSyncRL` tau of overlap-slot output and listener input (`stepDeProcTau`) moves the listener to `currEqN [m'', m'']` ~ `badOvlp`. That is neither `rangeBad m''` nor ~ `currEq m m''`. In reachable networks this cannot happen, because overlap/broadcast components only output `mCurr` with an empty payload (`switchCurr`, `tfsCurr`), so the only mCurr read is `stepDeCurrRead`, which reads `currModeMState k`.
  3. `ProtAuxResults.rangeBad_next` only gives `exists m, currEqState m m'' p'`, which does not link `m` to the action. A tracking lemma tying the read value to the derivative is needed.
- **Ripple-up:** used in `NARInsuff.notifBad_pres_tfs` (line ~406), which has `rn : reachableNet n` in scope. In the safety cone.
- **Suggested fix:** define `currModeNet` as above (see also `tfsListen_failSafe_net.fail.md`) and state
  ```
  Lemma rangeBad_next_net m m'' i n n' a : reachableNet n ->
    n -NA- a -NA> n' -> rangeBadStateNet m'' i n -> currModeNet m i n ->
    rangeBadStateNet m'' i n' \/ currEqStateNet m m'' i n'.
  ```
  (caller passes `rn`). Supporting lemmas to add:
  - prot level: `rangeBad_track m'' p p' a : rangeBadState m'' p -> p -PA- a -PA> p' -> exists m, a = chanMCurr ;? [baseMode m] /\ currEqState m m'' p'`
  - entity level: `rangeBad_next_ent : reachableEnt e -> e -EA- a ->> e' -> rangeBadStateEnt m'' e -> rangeBadStateEnt m'' e' \/ currEqStateEnt (currModeEnt e) m'' e'` (via `link_ent_soft_disc`, `link_par_triple_discW_3`, and `reachableProt_triple` to exclude internal mCurr syncs, with `stepDeCurrRead` / `stepMsOutCurr*` giving `m = currModeMState k`)
  The network lift then follows the pattern of `badOvlp_next_net`, proved in this fan-out.

### `NetAuxBasics.tfsListen_failSafe_net`

- **Where:** `src/NetAuxBasics.v` line 339 · **Lemma** · 2015 label: `#inter-component-lift-net` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `stub; missing-reachability`
- **Fix (audit summary):** Define the currModeNet stub and add `reachableNet n ->` here and to tfs_currMode_disc_pres (its only caller chain, NARInsuff.v:594, has p). Fixed version only argued.

- **Status:** BLOCKED-ON-STUB (currModeNet). It also NEEDS-HYPOTHESIS (`reachableNet n`) once the stub is defined.
- **Intent:** while the overlap component is in `tfsListen` (after transitioning to fail-safe), the entity's current mode is fail-safe.
- **Failure:** `currModeNet` is an uninterpreted `Parameter`, and nothing before this lemma constrains it (`currMode_intro` / `currMode_ent_ex` come later in the file and are not visible). Any proof would also go through with `currModeNet := fun _ _ _ => True`, under which the lemma says every mode is fail-safe as soon as some entity is in `tfsListen`. That fails in any model with a non-fail-safe mode.
  Even with the intended definition `currModeNet m i n <-> exists e, e @ i .: n /\ currModeEnt e = m` (cf. `currMode_ent_ex`), it is false for **unreachable** networks. Counterexample: `[ [| sleeping $||$ tfsListen $||$ listening, l, h, sing m |] ]` with `~ failSafe m` satisfies both premises (`tfsListenState` by `bisim_refl`).
- **Ripple-up:** sole user is `NetAuxBasics.tfs_currMode_disc_pres` (line ~370, the tfsListen case). Its sole user is `NARInsuff.v:594`, inside an induction on `currSince ... p` with `p : reachableNet n` in scope. In the safety cone.
- **Suggested fix:**
  1. Define the stub: `Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop := exists e, e @ i .: n /\ currModeEnt e = m.` (equivalently `liftEntNet (fun e => currModeEnt e = m)`). This makes `currMode_ent_ex` / `currMode_intro` immediate.
  2. Add reachability:
  ```
  Lemma tfsListen_failSafe_net m i n :
    reachableNet n -> tfsListenStateNet i n -> currModeNet m i n -> failSafe m.
  Lemma tfs_currMode_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode) :
    reachableNet n -> n -NA- a -NA> n' -> currModeNet m i n -> ~ failSafe m ->
    tfsStateNet i n -> tfsStateNet i n'.
  ```
  (NARInsuff.v:594 passes `p`.) Proof idea: an entity-level invariant over `reachableEnt` / `reachableNet`. `tfsListen` is only entered from `tfsBc`, which is only entered from `tfsCurr` via `mCurr!` synchronised with `stepMsSwitch`, making the current mode the `failSafeSucc` written by `tfsNext` (`failSafeSuccFS`). In `tfsBc` / `tfsListen` no component can output `mCurr!` / `mStable!`, and `stepDeTest` only moves a stable state into a transition state without changing the current mode. This is the same reasoning as `EntAuxResults.tfsBc_failSafe` (labelled C there, also lacking reachability).

### `NetAuxBasics.bcWaitNet_del_bkwd`

- **Where:** `src/NetAuxBasics.v` line 378 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `missing-reachability; noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n -> zeroTime < x ->` (both in scope at NARTop.bcWait_sent: p and H0); the pos-read urgency gap (noSyncNow) is a separate semantic issue for x = 0.

- **Status:** FALSE (counterexample, machine-checked in Rocq)
- **Intent:** if entity `i` is in broadcast state `bcWait m x` after a delay `d`, then before the delay it was in `bcWait m (x + d)` (the broadcast timer runs down linearly).
- **Failure:** the statement has no reachability hypothesis, so the source entity may run an arbitrary process that delays *into* something bisimilar to `bcWait m x` without itself being bisimilar to `bcWait m (x+d)`.
  Counterexample (any `m : Mode`), single-entity networks, `T1 = 1`, `D1 = 1`, `X = bcWait m zeroTime`:
  - `n  = [ [| del T1 X $||$ (nilProc $||$ nilProc), origin, h0, sing m |] ]`
  - `n' = [ [| del (1-1) X $||$ (nilProc $||$ nilProc), origin +p+ origin, h0, sing m |] ]`, with `h0` the interface with three empty lists.
  - `n -ND- D1 -ND> n'`: `stepTpDelSub` on the prefix, nils delay to themselves, the interface and stable mode state delay to themselves, displacement 0, and `noSync` holds vacuously because no strict delay-derivative of the process has any discrete action (the guard is still positive).
  - `bcWaitStateNet m zeroTime 0 n'`: `del e X ~ X` whenever `e` evaluates to `zeroTime` (bisimulation proved directly).
  - `~ bcWaitStateNet m (zeroTime +dt+ D1) 0 n`: `bcWait_trans_in` says any process bisimilar to a `bcWait` can input on `chanTrans` now. But `del T1 X` with `T1 > 0` has no discrete transition (`stepDpTimeOut` needs the guard to evaluate to zero).
  The Rocq proof is in `NetAuxBasics.bcWaitNet_del_bkwd.counterexample.v` (HELPERS section, lemma `bcWaitNet_del_bkwd_cx`):
  `Lemma bcWaitNet_del_bkwd_cx (m : Mode) : exists n n' x i d, n -ND- d -ND> n' /\ bcWaitStateNet m x i n' /\ ~ bcWaitStateNet m (x +dt+ d) i n.`
  It checks in `--explore` mode (to re-run, copy it to `NetAuxBasics.bcWaitNet_del_bkwd.v`). `Print Assumptions` shows only model axioms and the trusted stdlib axioms (proof_irrelevance, functional_extensionality, ClassicalDedekindReals). It uses **no** admitted lemma.
- **Second problem, even for reachable networks (x = 0):** `noSync` (EntityLanguage.v) only forbids synchronisation with the interface and the mode state. Position reads (`stepDePosRead`, channel `chanPos`) are **not urgent**. So a reachable entity in `bcWait m x'` with `x' < d` can delay by `d`. Its broadcast component becomes `trans?.. + pos?bcReady.. + wake?..` (the `del` prefix is consumed by `stepTpDelAdd`), which is bisimilar to `bcWait m 0`. The lemma would then claim `bcWait m x' ~ bcWait m d`, which is false (pos? becomes enabled at different times). So `zeroTime < x` is also needed. (Side observation for the owner: because `chanPos` is not in `noSync`, an entity can sit in `bcWait m 0` / `ovWait .. y=0` forever without broadcasting. This looks like a modelling gap with respect to the thesis's maximal-progress assumption, and could bite the periodic-broadcast lemmas in NARTop.)
- **Ripple-up:** used only in `NARTop.bcWait_sent` (line ~321, delay case of the induction on `p : reachableNet n`). In the safety cone. Nothing else uses it.
- **Suggested fix:**
  ```
  Lemma bcWaitNet_del_bkwd (n n' : Network) (m : Mode) (x : Time)
    (i : nat) (d : Delay) : reachableNet n -> zeroTime < x -> n -ND- d -ND> n' ->
    bcWaitStateNet m x i n' -> bcWaitStateNet m (x +dt+ d) i n.
  ```
  Sufficient for the user: in `bcWait_sent`'s delay case, `p : reachableNet n` (the predecessor) and `H0 : zeroTime < x` are both in context, so the call becomes `bcWaitNet_del_bkwd p H0 s H`.
  Why provable: by `link_net_ent_del_bkwd` + `link_net_prot_reach` + `reachableProt_triple`, the source broadcast component `p1` is a `broadcastState` and delays by `d` to `p1' ~ bcWait m x`. Case on `broadcastState p1`:
  - `bcReady`: delays to itself and can output on `chanOutProc`, unlike `bcWait`. Not bisimilar.
  - `sleeping`: delays to itself and never offers `pos?`, unlike `bcWait m x` after `x`. Not bisimilar; see `initial_not_bcWait_net_aux*`, proved in this fan-out.
  - `bcWait m' x'`: if `d <= x'` it delays to `bcWait m' (x'-d)`, and a small injectivity lemma (`bcWait m1 x1 ~ bcWait m2 x2 -> m1 = m2 /\ x1 = x2`, via the time at which `pos?` becomes enabled and the mode output by `bcReady`) gives `x' = x + d`. If `d > x'` the derivative is bisimilar to `bcWait m' 0`, which offers `pos?` now while `bcWait m x` (`x > 0`) does not. Contradiction.
- **Partial proof:** none for the target. The verified counterexample and its reusable helpers (`del e P ~ P` when `e` evaluates to 0, etc.) are in the `.counterexample.v` file.

### `NetAuxBasics.nextSince_del_ovWait`

- **Where:** `src/NetAuxBasics.v` line 424 · **Lemma** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `missing-reachability; noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Needs a semantics change (make chanPos reads urgent, e.g. extra clause in noSyncNow / stepTeDel premise; owner approval) AND `reachableNet n ->` (in scope at NARTop.nextSince_periodic_sent).

- **Status:** FALSE (counterexample, machine-checked in Rocq; uses no admitted lemma)
- **Intent:** if entity `i` is in a `nextSince` overlap state (ovWait / ovReady / switchBc / switchCurr) and the network can delay by `d`, then the overlap component is `ovWait m t X Y` with both timers `X, Y >= d` (written `x +dt+ d`, `y +dt+ d`). In words: the only nextSince state that can idle is ovWait, and it can idle at most as long as its timers.

## Failure

Two independent problems.

**(a) No reachability hypothesis.** The statement quantifies over arbitrary networks, so the
other components of the entity can be anything. Counterexample (checked in Rocq, see
`NetAuxBasics.nextSince_del_ovWait.v`, lemma `nextSince_del_ovWait_cex`):

```
n  := [ [| nilProc $||$ ovWait m 0 0 0 $||$ nilProc, origin, emptyInterface, sing m |] ]
d  := 0 +dt+ d1            (any delay)
```
* `n -ND- d -ND> n'` holds: the inputs and the expired `$<0>$` prefixes are patient, `nilProc`
  has an empty sort so the parallel side-conditions hold, the empty interface and the stable mode
  state delay, and `noSync` holds because the process only uses channels
  abort/bad/pos/pause, which neither the interface (IOEnv/OutProc/InProc/AN) nor the mode state
  (MCurr/MNext/MStable) ever offer.
* `nextSinceStateNet 0 n` holds (`nexsOvwSt` with `bisim_refl`).
* But any `ovWait m1 t1 (x+d) (y+d)` with `x+d > 0` is **not** bisimilar to `ovWait m 0 0 0`:
  the latter can output on `chanPause` immediately (`stepDpTimeOut` with timer 0), the former
  can't (`stepDpTimeOut` needs the guard to evaluate to `zeroTime`).

```
Lemma nextSince_del_ovWait_cex (m : Mode) (d1 : Delay) :
  ~ (forall (n n' : Network) (i : nat) (d : Delay),
     n -ND- d -ND> n' -> nextSinceStateNet i n ->
     exists m t x y, ovWaitStateNet m t (delToTime (x +dt+ d)) (delToTime (y +dt+ d)) i n).
```
`Print Assumptions nextSince_del_ovWait_cex` lists only model axioms (`Mode`, `speedMax`, …),
`proof_irrelevance`, `functional_extensionality_dep` and the classical-reals axioms. No admitted lemma.

**(b) Even with `reachableNet n` the statement is false in the current semantics:
position reads are not urgent.** The only entity rule that consumes `chanPos` is
`stepDePosRead`, and the delay rule `stepTeDel` only forbids synchronisation of the process with
the **interface** and the **mode state** (`noSync`). Nothing forces a pending `chanPos` input to
fire. In a *reachable* run (not mechanised; every step is a single rule application):
1. initial entity `[|procProtocol, l, h0, sing mF|]` (`mF` fail-safe, `h0` empty);
2. `stepDeTest`: mode state takes `chanMNext .? m'` (any `mF -mtr-> m'`);
3. `stepDeNextRead`: `dormant` reads `m'` and becomes `init m'`;
4. `stepDeCurrRead`: `init m'` reads the current mode and becomes
   `ovWaitN [m', T, 0]`, i.e. `ovWait m' T T 0` with `T = waitTime + period m' > 0`.
   **The position timer `y` is 0 on entry to ovWait.**
5. Delay by any `0 < d <= T` is allowed: `chanPause!` is guarded by `$<T>$` (that's the only
   synchronisation with `listening`), the expired `chanPos` input has no partner, and the
   mode state offers only `chanMCurr .!`, `chanMNext .!`, `chanMStable @?`, none of which
   the process can match.
At step 5 the state is nextSince, but the only ovWait it is bisimilar to has `y = 0 < d`.

## Ripple-up
* Used once: `NARTop.v:196` in `nextSince_periodic_sent` (in the safety cone), in the delay
  case of an induction on `nextSince`. There `reachableNet n` is available (`p`). The user
  needs only `0 < y + d` (to call `ovWait_sent`) and `m0 = m`.
* With the lemma false, `nextSince_periodic_sent`'s delay case has no justification: the
  position timer may sit at 0 while time passes, so "a message was sent within the last
  period" can fail. This is a genuine modelling gap, not just a missing hypothesis.

## Suggested fix
1. **Semantics (definition change, needs owner approval):** make position reads urgent at the
   entity level, e.g. strengthen `noSyncNow` in `EntityLanguage.v`:
   ```
   Definition noSyncNow (a : DiscAct) (p : ProcTerm) (i : Interface) (k : ModeState) : Prop :=
     discActEnabled p a ->
     ~discActEnabledInter (a^) i /\ ~discActEnabledMState (a^) k /\
     (forall l, a <> chanPos ;? [basePosition l]).
   ```
   (or add an explicit premise `forall d' <= d ... ~discActEnabled p' (chanPos ;? [basePosition l'])`
   to `stepTeDel`). This matches the thesis' intent that GPS reads happen immediately.
2. **Statement:** add reachability:
   ```
   Lemma nextSince_del_ovWait (n n' : Network) (i : nat) (d : Delay) :
     reachableNet n -> n -ND- d -ND> n' -> nextSinceStateNet i n ->
     exists m t x y, ovWaitStateNet m t (delToTime (x +dt+ d)) (delToTime (y +dt+ d)) i n.
   ```
   With (1), it should be provable: ovReady (outProc output, always accepted by the interface,
   `interface_outProc_in`), switchBc (wake output vs sleeping/bcWait, or bcReady urgent) and
   switchCurr (mode state `<|m,m',0|>` accepts `chanMCurr @?`, `switchCurr_mState`) are urgent;
   in ovWait, `y >= d` by urgency of the read (fix 1) and `x >= d` because during a delay the
   listener is `listening` (`del_listening*`), which accepts `chanPause`. The only user
   (`nextSince_periodic_sent`) already has `reachableNet n` in scope, so the change is local.

## Partial proof
None of the target. The counterexample script is the HELPERS section of
`NetAuxBasics.nextSince_del_ovWait.v` (compiles in `--explore`; the target itself is left `Admitted`).

### `NetAuxBasics.currMode_pres_bkwd`

- **Where:** `src/NetAuxBasics.v` line 581 · **Theorem** · 2015 label: `7` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define the currModeNet stub (Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop := exists e, e @ i .: n /\ currModeEnt e = m (or liftEntNet (fun e => currModeEnt e = m))); proof under it compiles with no admitted deps (currMode_pres_bkwd_stub via proved link_net_ent_disc_bkwdW).

- **Status:** BLOCKED-ON-STUB (currModeNet)
- **Intent:** If entity `i` has some current mode in `n'` and `n -NA- a -NA> n'`, then entity `i` also has some current mode in `n`. In other words, entity `i` was already in the source network, and every entity has a current mode.
- **Failure:** `currModeNet : Mode -> nat -> Network -> Prop` is an opaque `Parameter` (NetAuxBasics.v:56). The only earlier statement that concludes `currModeNet` is `switch_states_mState`. It needs `switchCurrStateNet i n`, `switchListenStateNet i n'` and `nextModeNet m i n`, which are not available here. No hypothesis can produce `currModeNet _ i n`. The goal after `intros ST CM` is `exists m, currModeNet m i n`, with `CM : currModeNet m' i n'` as the only fact about the stub (confirmed via `--explore`).
- **Ripple-up:** In the safety cone. Used in `NARInsuff.v:61` (`currModeNet_notifBad_pres_bkwd`) and `NARNonFS_currSince.v:145`. The statement is true under the intended definition (see below), so nothing upstream breaks. It is only waiting for the stub.
- **Suggested fix (stub definition, not a statement change):**
  ```coq
  Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
    exists e, e @ i .: n /\ currModeEnt e = m.
  ```
  This makes the later conjecture `currMode_ent_ex` (NetAuxBasics.v:902) hold by `iff_refl`. An equivalent alternative is an `Inductive` with a single witness constructor `cmnWitness e : e @ i .: n -> currModeEnt e = m -> currModeNet m i n`, in the style of `inPosNet`.
- **Proof under that definition** (checked in Rocq against the frozen build, with the stub replaced by a local `Definition currMode_pres_bkwd_cmn`; see `stub_validation.currModeNet_reachableEnt.v`):
  ```coq
  Proof.
    intros ST [e' [EIN _]].
    destruct (link_net_ent_disc_bkwdW n n' e' i a ST EIN) as [e EIN0].
    exists (currModeEnt e). exists e. split; [assumption | reflexivity].
  Qed.
  ```
  It uses only the proved `link_net_ent_disc_bkwdW`.

### `NetAuxBasics.currMode_intro`

- **Where:** `src/NetAuxBasics.v` line 729 · **Conjecture** · 2015 label: `-` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define the currModeNet stub: Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop := exists e, e @ i .: n /\ currModeEnt e = m (or liftEntNet (fun e => currModeEnt e = m)); then the proof is one line (compiles: currMode_intro_stub, closed).

- **Status:** BLOCKED-ON-STUB (currModeNet)
- **Intent:** This is the introduction rule for `currModeNet`: if `e @ i .: n`, then `currModeNet (currModeEnt e) i n`.
- **Failure:** `currModeNet` is an opaque `Parameter` (NetAuxBasics.v:56). Nothing can introduce it, because no earlier axiom or lemma concludes `currModeNet` from `e @ i .: n`.
- **Ripple-up:** In the safety cone. It is used by the top-level proof in `Main.v:190-191`. It is true under the intended definition, so nothing upstream breaks.
- **Suggested fix (stub definition):**
  ```coq
  Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
    exists e, e @ i .: n /\ currModeEnt e = m.
  ```
- **Proof under that definition** (checked in Rocq with a local copy of the definition; see `stub_validation.currModeNet_reachableEnt.v`):
  ```coq
  Proof. intros m e i n EQ EIN. exists e. split; [assumption | symmetry; assumption]. Qed.
  ```

### `NetAuxBasics.reachable_net_ent`

- **Where:** `src/NetAuxBasics.v` line 745 · **Conjecture** · 2015 label: `-` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt as the closure of initialEnt under -EA-/-ED- (moved below initialEnt in EntAuxDefs.v); proof under it compiles with no admitted deps.

- **Status:** BLOCKED-ON-STUB (reachableEnt)
- **Intent:** Every entity of a reachable network is itself reachable.
- **Failure:** `reachableEnt : Entity -> Prop` is an opaque `Parameter` (EntAuxDefs.v:143). No imported or earlier lemma concludes `reachableEnt`; `grep reachableEnt` shows it only ever appears as a hypothesis. Under the opaque stub the goal `reachableEnt e` cannot be introduced.
- **Ripple-up:** In the safety cone. It is used in `NARMisc.v:359-371` and `NARMisc.v:518` (the urgency contradictions) and in `NARMsgPosition.v:242,251`. It is true under the intended definition.
- **Suggested fix (stub definition):** use the reflexive-transitive closure of `initialEnt` under entity transitions, as the "Idea" comment in EntAuxDefs.v says:
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' d : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  `initialEnt` is defined only after the stub, so the stub has to move below `initialEnt` (EntAuxDefs.v:156).
- **Proof under that definition** (checked in Rocq against the frozen build with a local copy `reachable_net_ent_RE` of the inductive; see `stub_validation.currModeNet_reachableEnt.v`):
  ```coq
  Proof.
    intros n e i RN. revert e i.
    induction RN as [n0 INIT | n0 n1 a0 RN0 IH ST | n0 n1 d0 RN0 IH ST]; intros e1 i1 EIN.
    - apply reachEntInit. eapply initialNet_ent; eassumption.
    - destruct (link_net_ent_disc_bkwd _ _ _ _ _ ST EIN) as [e0 [EIN0 [EQ | [a' STE]]]].
      + subst. eapply IH; eassumption.
      + eapply reachEntDisc; [eapply IH; eassumption | eassumption].
    - destruct (link_net_ent_del_bkwd _ _ _ _ _ ST EIN) as [e0 [EIN0 STE]].
      eapply reachEntDel; [eapply IH; eassumption | eassumption].
  Qed.
  ```
  It uses only the proved `initialNet_ent`, `link_net_ent_disc_bkwd` and `link_net_ent_del_bkwd`. The validated helper takes `n e i` as section-style arguments, so the `intros` line differs slightly.

### `NetAuxBasics.currModeNet_del_pres`

- **Where:** `src/NetAuxBasics.v` line 815 · **Conjecture** · 2015 label: `-` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define the currModeNet stub (Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop := exists e, e @ i .: n /\ currModeEnt e = m (or liftEntNet (fun e => currModeEnt e = m))); proof under it compiles (currModeNet_del_pres_under_def; rests on admitted link_net_ent_del_fwd).

- **Status:** BLOCKED-ON-STUB (currModeNet)
- **Intent:** A time delay does not change the current mode of any entity: `currModeNet m i n <-> currModeNet m i n'` whenever `n -ND- d -ND> n'`.
- **Failure:** `currModeNet` is an opaque `Parameter` (NetAuxBasics.v:56). Before line 815 the only facts about it are `currMode_intro` (introduction only), `currMode_pres_bkwd`/`currMode_pres_fwd` (discrete steps, existential), and lemmas that use it only as a hypothesis next to a state predicate that forces an entity at `i` (`rangeBad_next_net`, `tfsListen_failSafe_net`, `tfs_currMode_disc_pres`), plus `switch_states_mState` (conclusion only). None of them eliminates `currModeNet`, and none mentions delay.
  **Independence model:** interpret `currModeNet m i n := (exists e, e @ i .: n /\ currModeEnt e = m) \/ (length n <= i /\ exists e, In e n /\ posEnt e = origin)`. Every visible constraint still holds. The second disjunct is invisible to every lemma that also needs an entity at `i`, and discrete steps preserve both length and positions (`stepDiscPresPos`), so `currMode_pres_bkwd`/`fwd` still hold. But a delay can move the origin entity, which breaks the `<->` for an out-of-range `i`.
  **Warning (important):** the visible context *does* prove this statement by an illegitimate route. `transGuard_del` and `transGuard_disc_pres` (both earlier Conjectures) each imply `Mode -> False` (see their .fail.md, verified in Rocq), and this statement binds `m : Mode`. So `intros; exfalso; exact (transGuard_del_refute transGuard_del m)` would "prove" it. I deliberately did NOT do this. The lead should reject any accepted proof in NetAuxBasics or downstream that reaches `False` through `transGuard_del` or `transGuard_disc_pres`.
- **Ripple-up:** used in `NARMisc.currSince_curr` (delay case: `erewrite <- currModeNet_del_pres`). That lemma feeds `NARIncomp` (l.402) and `NARInsuff` (l.483, l.593). In the safety cone.
- **Suggested fix:** define the stub, as `currMode_ent_ex` (l.~916) already specifies:
  ```coq
  Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
    exists e, e @ i .: n /\ currModeEnt e = m.
  ```
  (Equivalently `liftEntNet (fun e => currModeEnt e = m) i n`.) With this definition the statement is provable. Verified in Rocq (explore mode, all helpers end in `Qed`) using a local copy `currModeNet_del_pres_def`:
  ```coq
  Lemma currModeNet_del_pres_ent : forall (e e' : Entity) (d : Delay),
    e -ED- d ->> e' -> currModeEnt e = currModeEnt e'.
  Proof.
    intros e e' d D. inversion D; subst. cbn.
    match goal with K : _ -ms- _ -ms> _ |- _ => inversion K; subst; reflexivity end.
  Qed.

  Lemma currModeNet_del_pres_under_def : forall (n n' : Network) (d : Delay)
    (m : Mode) (i : nat), n -ND- d -ND> n' ->
    (currModeNet_del_pres_def m i n <-> currModeNet_del_pres_def m i n').
  Proof.
    intros n n' d m i ND. unfold currModeNet_del_pres_def. split.
    - intros [e [E CM]].
      destruct (link_net_ent_del_fwd n n' e i d ND E) as [e' [E' D]].
      exists e'. split; [exact E' | ].
      rewrite <- CM. symmetry. eapply currModeNet_del_pres_ent. exact D.
    - intros [e' [E' CM]].
      destruct (link_net_ent_del_bkwd n n' e' i d ND E') as [e [E D]].
      exists e. split; [exact E | ].
      rewrite <- CM. eapply currModeNet_del_pres_ent. exact D.
  Qed.
  ```
  This relies only on `link_net_ent_del_fwd` (admitted, NetworkLanguage) and `link_net_ent_del_bkwd` (proved). The key fact is that every mode-state delay rule preserves `currModeMState`. The same definition also makes `currMode_intro`, `currMode_ent_ex` and `currMode_del_pres_bkwd` immediate.
- **Partial proof:** see `NetAuxBasics.currModeNet_del_pres.v` (explore file with the demonstration above).

### `NetAuxBasics.inPos_ent_net`

- **Where:** `src/NetAuxBasics.v` line 851 · **Conjecture** · 2015 label: `-` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define inPosEnt (Inductive ipeWitness, or posEnt e = l) in EntAuxDefs.v; proof is one line (compiles, closed).

- **Status:** BLOCKED-ON-STUB (`inPosEnt`, EntAuxDefs.v:149)
- **Intent:** if entity `e` is at position `l` (`inPosEnt l e`) and `e` is entity number `i` of `n`, then `inPosNet l i n`.
- **Failure:** `inPosNet l i n` requires `[|p, l, h, k|] @ i .: n`, i.e. `posEnt e = l`. `inPosEnt` is an opaque `Parameter`. No visible lemma or conjecture has `inPosEnt` as a *hypothesis* (it only appears as the conclusion of `bcReady_pos` and `ovReady_pos` in EntAuxResults). So nothing links `inPosEnt l e` to `posEnt e`. The statement can't be derived: interpreting `inPosEnt` as `fun _ _ => True` is consistent with every visible assumption and makes the statement false for any `e` with `posEnt e <> l`.
- **Ripple-up:** in the safety cone. Used in NARMsgPosition.v:246 and :254 (with `bcReady_pos` / `ovReady_pos` and `inPos_unique`) to show that the broadcast position equals the sender's position.
- **Suggested fix:** complete the stub in EntAuxDefs.v, following its "Idea" comment (analogous to nextModeEnt):
  ```coq
  Inductive inPosEnt (l : Position) : Entity -> Prop :=
    | ipeWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
      inPosEnt l ([|p, l, h, k|]).
  ```
  (or `Definition inPosEnt l e := posEnt e = l`). The statement is unchanged. With this definition the proof is
  `Proof. intros l e i n H E. destruct H. econstructor. eassumption. Qed.`
  This was checked in --explore against a local copy of the definition (`inPos_ent_net_inPosEnt` / `inPos_ent_net_with_def` in NetAuxBasics.inPos_ent_net.v). `bcReady_pos` and `ovReady_pos` stay meaningful under it.
- **Partial proof:** see the HELPERS of NetAuxBasics.inPos_ent_net.v. Those helpers are a demonstration only and are not for splicing.

### `NetAuxBasics.currMode_ent_ex`

- **Where:** `src/NetAuxBasics.v` line 901 · **Conjecture** · 2015 label: `-` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define the currModeNet stub (Inductive cmnWitness or liftEntNet form); statement becomes iff_refl-like (compiles, closed).

- **Status:** BLOCKED-ON-STUB (`currModeNet`, NetAuxBasics.v:56)
- **Intent:** `currModeNet m i n` holds iff entity `i` of `n` exists and has current mode `m`. This is the characterisation of the (intended) lift of `currModeEnt`.
- **Failure:** the `<-` direction follows from the visible Conjecture `currMode_intro`. The `->` direction can't be proved. `currModeNet` is an opaque `Parameter`, and no visible lemma or conjecture eliminates it into an entity: `currModeNet_del_pres`, `currModeNet_dec`, `currMode_pres_bkwd/fwd`, `tfsListen_failSafe_net`, `rangeBad_next_net` and `tfs_currMode_disc_pres` all need extra structure or conclude other `currModeNet` facts. Interpreting `currModeNet` as `fun _ _ _ => True` is consistent with every visible assumption and refutes `->` on `n = []`.
- **Ripple-up:** in the safety cone. Used directly in NARIncomp.v:78, NARMisc.v:534 and NARNonFS_currSince.v:132,149,150, via the tactic `currMode_ent_ex_tac`. It is also the key step of the corrected `tfsNext_currModeNet_eq`.
- **Suggested fix:** complete the stub. `liftEntNet` is defined after line 56, so either move the declaration below `liftEntNet` and write
  `Definition currModeNet (m : Mode) := liftEntNet (fun e => currModeEnt e = m).`
  or define it in place, in the style of `inPosNet`:
  ```coq
  Inductive currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
    | cmnWitness (e : Entity) : e @ i .: n -> currModeEnt e = m -> currModeNet m i n.
  ```
  The statement is unchanged. Proof: `split; [intros [e E C]; exists e; auto | intros [e [E C]]; econstructor; eassumption]`. This was checked in --explore against a local copy, together with its equivalence to the `liftEntNet` form. See `currMode_ent_ex_with_def` and `currMode_ent_ex_def_lift` in NetAuxBasics.currMode_ent_ex.v. The definition also makes `currMode_intro` trivial. `currModeNet_del_pres` becomes a matter of delays preserving `currModeMState`.
- **Partial proof:** see the HELPERS (demonstration only, not for splicing).

### `NetAuxBasics.tfsCurrStateNet_bktrk_net`

- **Where:** `src/NetAuxBasics.v` line 168 · **Lemma** · 2015 label: `6` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (available in NARMisc.tfs_transGuard via the tfs constructor); argued, needs tfsNext_currMode + reachable_net_ent and a tfsCurr backtracking lemma.

- **Status:** FALSE (counterexample). Fix: NEEDS-HYPOTHESIS `reachableNet n`.
- **Intent:** backtracking for `tfsCurr` at network level. If entity `i` is in `tfsCurr` after a discrete network step, then either it was already in `tfsCurr`, or it was in `tfsNext m` and the step was the `chanMNext<failSafeSucc m>!` write. That write leaves the mode state at `<| m, mF, modeTransTime m mF p |>` with `mF` fail-safe.
- **Failure:** the statement has no reachability or protocol-shape hypothesis on `n`, so the overlap slot of entity `i` may hold any process term that steps into `tfsCurr`. **Counterexample (compiled with `--explore` at the target's position; first found by NetAuxBasics-1, re-checked by w1b-09):** for any `m : Mode`, take
  `n  = [[| nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc, l, h, sing m |]]` and
  `n' = [[| nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m |]]`,
  where `l = mkPosition 0 0` and `h` is the empty interface. Then `n -NA- anTau -NA> n'` holds by `stepDnTauHead`/`stepDePosRead`, and `tfsCurrStateNet 0 n'` holds. But entity 0 of `n` is neither in `tfsCurr` nor in `tfsNext _`: an `inPrefix chanPos` term enables neither `chanMCurr *!` (`tfsCurr_mCurr_out`) nor `chanMStable *!` (`tfsNext_mStable_out`), so it is bisimilar to neither. Rocq script:
  ```coq
  Lemma tfsCurrStateNet_bktrk_net_cex (m : Mode) :
    ~ (forall (n n' : Network) (i : nat) (a : ActDiscNet),
    tfsCurrStateNet i n' -> n -NA- a -NA> n' ->
    tfsCurrStateNet i n \/
    (exists m mF, exists p,
    tfsNextStateNet m i n /\ failSafe mF /\
    mState_in_net (<| m, mF, modeTransTime m mF p |>) i n')).
  Proof.
    intro H.
    pose (l := mkPosition 0%R 0%R).
    pose (h := mkInterface (mkInputList []) (mkOutputList []) (mkNotifList [])).
    assert (PT : nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc
       -PA- chanPos ;? [basePosition l] -PA> nilProc $||$ tfsCurr $||$ nilProc).
    { change (nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc
       -PA- chanPos ;? [basePosition l] -PA> nilProc $||$
       (subProcTerm (listsToSub [vL] (listBaselistExp [basePosition l])) tfsCurr)
       $||$ nilProc).
      apply stepDpParR. apply stepDpParL. apply stepDpIn. reflexivity. }
    assert (ST : [[|nilProc $||$ inPrefix chanPos [vL] tfsCurr $||$ nilProc, l, h, sing m|]]
       -NA- anTau -NA> [[|nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m|]]).
    { apply stepDnTauHead. apply stepDePosRead. exact PT. }
    assert (TC : tfsCurrStateNet 0 [[|nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m|]]).
    { eapply lenWitness; [ | apply einConsLeft]. apply lifpe. apply lftOv.
      unfold tfsCurrState. apply ComhCoq.ProcEquiv.bisim_refl. }
    destruct (H _ _ _ _ TC ST) as [A | [m' [mF [pr [A _]]]]];
    destruct A as [e X E]; inversion E; subst;
    inversion X as [p0 l0 h0 k0 Y]; subst;
    inversion Y as [q1 q2 q3 Z]; subst.
    - lets D : tfsCurr_mCurr_out Z. destruct D as [q T]. inversion T.
    - lets D : tfsNext_mStable_out Z. destruct D as [q T]. inversion T.
  Qed.
  ```
  This uses only proved lemmas (`tfsCurr_mCurr_out`, `tfsNext_mStable_out`, `bisim_refl`).
  A second, independent gap remains even when every process term is a protocol state. The disjunct needs the mode state's *current* mode to equal the `m` of `tfsNext m`, because `stepDeNextWrite`/`stepMsInit` produce `<| currMode k, failSafeSucc m, _ |>`. That is the invariant `EntAuxResults.tfsNext_currMode` (`reachableEnt e -> tfsNextStateEnt m e -> currModeEnt e = m`). It holds only for reachable entities, so reachability is genuinely needed, not just a protocol-shape hypothesis.
- **Ripple-up:** **not** in the safety cone. Its only user is `NARMisc.tfs_transGuard` (NARMisc.v:308), in the `tfsDisc` case of `induction` on `tfs m t i n p`. That constructor carries `p : reachableNet n` for the pre-state `n`, so the corrected statement can be applied there without change to the caller's statement: `addHyp (tfsCurrStateNet_bktrk_net n n' i a p H w)`, with argument order as in the fix below.
- **Suggested fix (statement change; needs owner approval):**
  ```coq
  Lemma tfsCurrStateNet_bktrk_net : forall (n n' : Network) (i : nat) (a : ActDiscNet),
    reachableNet n -> tfsCurrStateNet i n' -> n -NA- a -NA> n' ->
    tfsCurrStateNet i n \/
    (exists m mF, exists p,
    tfsNextStateNet m i n /\ failSafe mF /\
    mState_in_net (<| m, mF, modeTransTime m mF p |>) i n').
  ```
  **Proof plan for the fixed statement:**
  1. Take entity `i` of `n'` (`liftEntNet`) and backtrack the network step to the entity at `i` in `n`. The step is either an identity on `i` (done: left disjunct) or an entity step `e -EA- a' ->> e'`. Use `link_net_ent_disc_bkwd`, which another prover proved and used in `reachable_net_ent.fail.md`.
  2. Process level: `link_net_prot_reach` gives `reachableProt` of `e`'s process. A protocol-level backtrack for `tfsCurr` gives that the overlap component was in `tfsCurr`, or in `tfsNext m` with action `chanMNext ;! [baseMode (failSafeSucc m)]`. That backtrack is not yet present; it is the dual of `tfsNext_next_ent` at EntAuxResults.v:551, a brute-force `#back-track-lift` lemma.
  3. Entity level: that output can only synchronise via `stepDeNextWrite`, so `k -ms- chanMNext .? failSafeSucc m -ms> k'`. Inverting `stepMsInit` gives `k = sing m0` and `k' = <| m0, failSafeSucc m, modeTransTime m0 _ p |>`.
  4. `m0 = m` by `tfsNext_currMode` (needs `reachableEnt e`, via `reachable_net_ent`, NetAuxBasics.v:745). Use `mF := failSafeSucc m`, with `failSafeSuccFS`.
  Because step 4 needs `reachable_net_ent` (declared later, at line 745), the fixed lemma should either move after it, or the induction on `reachableNet` for the mode-equality invariant should be inlined.
- **Partial proof:** none for the target; the counterexample above compiles.

### `NetAuxBasics.tfsCurrState_del_pres_net`

- **Where:** `src/NetAuxBasics.v` line 178 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (or split: unconditional forward lemma + reachable-only backward lemma; the backward proof needs reachable_net_ent/reachableEnt stub).

- **Status:** FALSE (counterexample, machine-checked; the backward direction needs `reachableNet n`)
- **Intent:** Delay neither creates nor destroys the `tfsCurr` state of the overlap component: `tfsCurrStateNet i n <-> tfsCurrStateNet i n'` when `n -ND- d -ND> n'`.
- **Failure:** The forward direction holds: `tfsCurr` delays only to itself, and `~p~` is a bisimulation over timed steps too. The **backward** direction fails for unreachable networks. Take the middle component `del (eBase (baseTime 1)) tfsCurr`. By `stepTpDelAdd` it delays by `1 +dt+ 1` to `tfsCurr`. It is *not* bisimilar to `tfsCurr`: `tfsCurr` can do `chanMCurr *!` now, and a `del` can only act through `stepDpTimeOut`, which needs the guard to evaluate to `0`.

  Concrete instance, for any `m : Mode`:
  - `n = [ [| nilProc $||$ del 1 tfsCurr $||$ nilProc, origin, emptyIface, sing m |] ]`
  - `n' = [ [| nilProc $||$ tfsCurr $||$ nilProc, origin +p+ origin, emptyIface, sing m |] ]`
  - `n -ND- (1 +dt+ 1) -ND> n'`.

  All `stepTeDel` premises are discharged, `noSync` included. Every delay derivative of the process can only do `chanAbort *?`, `chanBad *?` or `chanMCurr *!`. The interface never acts on those channels, and `sing m` cannot do `chanMCurr *?` (that needs `<|m, m', 0|>`). `tfsCurrStateNet 0 n'` holds and `tfsCurrStateNet 0 n` does not.

  Verified as `tfsCurrState_del_pres_net_cex (m : Mode) : ~ (statement)` in `w1b-15/NetAuxBasics.tfsCurrState_del_pres_net.v`, which compiles with `Qed`. `Print Assumptions` shows **only model axioms** (`Mode`, `speedMax`, …) and stdlib classical/FE/PI, with no admitted lemma. So this conjecture plus an inhabited `Mode` proves `False` outright.
- **Ripple-up:** Not in the safety cone. Users:
  - `NARMisc.tfs_transGuard` (proved, line 321) uses the **backward** direction in the `tfsDel` case, where `p : reachableNet n` is in scope.
  - `NARMisc.tfs_bound` (line 377, body commented out, `Admitted (*R*)`) uses the forward direction, again with `p : reachableNet n` in scope.
- **Suggested fix:**
  ```coq
  Lemma tfsCurrState_del_pres_net : forall (n n' : Network) (d : Delay) (i : nat),
    reachableNet n -> n -ND- d -ND> n' ->
    (tfsCurrStateNet i n <-> tfsCurrStateNet i n').
  ```
  Callers change to `addHyp (tfsCurrState_del_pres_net n n' d i p w)`. Alternatively, split it into an unconditional forward lemma and a reachable-only backward lemma. With reachability, the backward direction follows from `EntAuxResults.del_ovlp`: a reachable entity that can delay is dormant, tfsCurr or ovWait. You then rule out dormant/ovWait delaying to something bisimilar to `tfsCurr`. That depends on `reachable_net_ent`/`reachableEnt` (stub), so the fixed version is BLOCKED-ON-STUB (`reachableEnt`) until the stub is defined.
- **Partial proof:** The file contains the full counterexample and reusable helpers:
  - `_acts`: `tfsCurr`'s discrete actions.
  - `_tdel`: `tfsCurr` delays only to itself.
  - `_derP`, `_actsP`, `_nosyncC`.

### `NetAuxBasics.mState_switch_states`

- **Where:** `src/NetAuxBasics.v` line 185 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `unstable k ->` (shape supplied by the only caller NARMisc.tfs_transGuard). Fixed version compiles but rests on admitted link_net_prot_reach, reachableProt_triple (itself in blacklist_hard), ovlp_mCurr_out, bc_mCurr_out_not, listen_mCurr_out_not.

- **Status:** FALSE (counterexample). **It is inconsistent with the model axioms:** given any `m : Mode` it implies `False`. It should go on the known-inconsistent list next to `transGuard_del` / `transGuard_disc_pres`.
- **Intent:** in a reachable network, the mode state of entity `i` changes on a discrete step only in two ways: the overlap component finalises a switch (`switchCurr -> switchListen`), or it switches to fail-safe (`tfsCurr -> tfsBc`). Both are the `chanMCurr *!` / `chanMCurr @?` synchronisation (entity rule `stepDeCurrWrite`).
- **Failure:** the mode state can also change without the software. Entity rule `stepDeTest` (EntityLanguage.v:182) lets a *stable* mode state take `stepMsInit` (`m -ms- chanMNext .? m' -ms> <|m, m', modeTransTime m m' _|>`) with the process untouched. This is the environment/application starting a mode transition. `stepDeNextWrite` changes `k` the same way, through the overlap's `tfsNext` output. So with the initial network `n = [[|procProtocol, l, h, sing m0|]]`, where `m0 := failSafeSucc m` is fail-safe so `initialEnt` holds, the `anTau` step via `stepDeTest` to `[[|procProtocol, l, h, <|m0, m1, modeTransTime m0 m1 _|>|]]` (with `m1 := failSafeSucc m0`) satisfies every hypothesis. But `procProtocol`'s overlap is `dormant`, which is neither `tfsCurr` nor `switchCurr`. The disjuncts are refuted with `tfsCurr_mCurr_out` / `switchCurr_mCurr_out` plus `invert_trans` on `dormant`.
  **Verified in Rocq** (`--explore`, rc=0): `mState_switch_states_cex` in `NetAuxBasics.mState_switch_states.v` (HELPERS) proves
  `forall m : Mode, ~ (<statement of mState_switch_states>)`.
  `Print Assumptions mState_switch_states_cex` lists **only model axioms** (`Mode`, `failSafeSucc`, `failSafeSuccFS`, `failSafeSucc_successor`, `modeTransTime`, …) plus stdlib classical reals, `proof_irrelevance` and `functional_extensionality_dep`. It uses no admitted lemma. So the admitted statement plus `Mode` inhabited is inconsistent. (The counterexample was found by the earlier prover `NetAuxBasics-1`; I re-checked it and wrote it up.)
- **Ripple-up:** not in the safety cone (`show`: `in_safety_cone=False`). Its only user is `NARMisc.tfs_transGuard` (NARMisc.v:302), which instantiates it with `k = <| m1, m2, t' |>`, an *unstable* mode state. That proof also uses the already-banned `transGuard_del` (NARMisc.v:323), so it is tainted either way. `tfs_transGuard` is used at NARMisc.v:379.
- **Suggested fix:** add the hypothesis `unstable k`. That is exactly the shape the only caller supplies, and it rules out `stepMsInit` (via `stepDeTest`/`stepDeNextWrite`), which needs a stable source:
  ```coq
  Lemma mState_switch_states : forall (n n' : Network) (i : nat)
    (a : ActDiscNet) (k k' : ModeState), reachableNet n -> unstable k -> k <> k' ->
    n -NA- a -NA> n' -> mState_in_net k i n -> mState_in_net k' i n' ->
    (tfsCurrStateNet i n /\ tfsBcStateNet i n') \/
    (switchCurrStateNet i n /\ switchListenStateNet i n').
  ```
  **Proved** (`mState_switch_states_fixed` in the same file, explore rc=0). The proof goes as follows. Backtrack with `link_net_ent_disc_bkwd` and `entInNetUnique`. Invert the entity step and then the mode-state step. Every rule except `stepDeCurrWrite`/`stepMsSwitch` either leaves `k` unchanged or needs a stable `k`. In the remaining case, `reachableProt_triple` plus `link_par_triple_out` locate the `chanMCurr *!` output. `bc_mCurr_out_not` and `listen_mCurr_out_not` exclude broadcast and listener, and `ovlp_mCurr_out` gives the two disjuncts. It rests only on admitted lemmas that are not banned: `link_net_prot_reach`, `reachableProt_triple`, `ovlp_mCurr_out`, `bc_mCurr_out_not`, `listen_mCurr_out_not`. At the call site (NARMisc.v:302) the extra argument is `unstbl m1 m2 t'` (after `subst k`/`Heqk`).
  **Caveat for the semantics owner:** the fix works partly because no entity rule synchronises a process `chanMStable *!` output with the mode state's `stepMsAbort` (`chanMStable @?`). The only `chanMStable` entity rule, `stepDeRdStbl`, has the process *input* and the mode state *output*. But `ovAbort = chanMStable!dormantN` and `tfsNext`'s `chanMStable!tfsNextN` are process *outputs*, so as written `ovAbort` can never fire. If that direction mismatch is fixed by adding an abort rule, the corrected lemma needs a third disjunct, `(ovAbortStateNet i n /\ dormantStateNet i n')`, and a check of `tfsNext`.
- **Partial proof:** counterexample and fixed-statement proof are in `NetAuxBasics.mState_switch_states.v` (HELPERS; target left `Admitted`).

### `NetAuxBasics.tfsState_del_pres_net`

- **Where:** `src/NetAuxBasics.v` line 197 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Split: forward lemma tfsState_del_pres_net_fwd (compiles; rests on admitted ProtAuxResults.del_pres_tfsState) + backward lemma with `reachableNet n ->` (argued).

- **Status:** FALSE (counterexample, machine-checked). The backward direction needs `reachableNet n`. The conjecture is **inconsistent with the model axioms**: together with any `m : Mode` it proves `False`, and the proof uses no admitted lemma. Please add it to the known-inconsistent list.
- **Intent:** A delay neither creates nor destroys a tfs state (tfsStart, tfsNext, tfsCurr, tfsBc or tfsListen) of the overlap component of entity `i`.
- **Failure:** The **forward** direction holds. I proved it as `tfsState_del_pres_net_fwd` from `ProtAuxResults.del_pres_tfsState` and the delay-linking lemmas, with no reachability needed.
  The **backward** direction fails on unreachable networks. A delay prefix `$<e>$ Q` with guard `e` evaluating to `r > 0` delays by `r +dt+ d` straight to `Q` (`stepTpDelAdd`). It is not bisimilar to any of the five tfs reference terms, because each of those has an immediate discrete action, while a `del` can act only through `stepDpTimeOut`, which needs the guard to be `0`.
  Concrete instance, for any `m : Mode`, with `Q := tfsBc`, `r = 1` and `d = 1`:
  - `n  = [ [| nilProc $||$ ($<1>$ tfsBc) $||$ nilProc, origin, emptyIface, sing m |] ]`
  - `n' = [ [| nilProc $||$ tfsBc $||$ nilProc, origin +p+ origin, emptyIface, sing m |] ]`
  - `n -ND- (1 +dt+ 1) -ND> n'`

  All `stepTeDel` premises are discharged, `noSync` included: every delay derivative of the process can only do `chanTrans *!`, and neither the interface nor `sing m` can input on `chanTrans`. In this instance `tfsStateNet 0 n'` holds (`tfsBcSt`, `bisim_refl`) and `tfsStateNet 0 n` does not.
  Checked in `NetAuxBasics.tfsState_del_pres_net.v` (`--explore` rc=0, all helpers end in `Qed`):
  - `tfsState_del_pres_net_cexG` is the generic construction, for any `Q` that delays only to itself and whose actions cannot synchronise with the interface or with `sing m`.
  - `tfsState_del_pres_net_notfs` shows that a pending delay prefix is not `tfsState`.
  - `tfsState_del_pres_net_refuted (m : Mode) : ~ (statement)`.

  `Print Assumptions tfsState_del_pres_net_refuted` lists only the model axioms (`Mode`, `speedMax`, `adaptNotif`, …) plus stdlib classical reals, functional extensionality and proof irrelevance. No admitted lemma appears.
  The same construction with `Q := tfsCurr` (`tfsState_del_pres_net_refuted_curr`) refutes `tfsCurrState_del_pres_net` (NetAuxBasics.v:178). w1b-15 reached the same result independently (`w1b-15/NetAuxBasics.tfsCurrState_del_pres_net.fail.md`).
- **Ripple-up:** Not in the safety cone. Its only frozen-source use is NARMisc.v:86, which is inside a commented-out proof. Accepted wave-1 proofs that depend on it:
  - **`NetAuxBasics.del_pres_bkwd_tfsNext`** (NetAuxBasics-7, `.ok`) uses `proj2`, the **false** direction. That acceptance therefore rests on an inconsistent conjecture and should be re-examined. Its own statement can still hold under extra assumptions: for `Q := tfsNext m` the counterexample needs a stable mode `m0` with `~ m0 -mtr-> failSafeSucc m`, so it is not refuted by the model axioms alone.
  - **`NARMisc.tfs_rel_state`** (NARMisc-2, `.ok`) uses `proj1`, the true direction. It can be re-routed through `tfsState_del_pres_net_fwd`.
  - `NARInsuff.tfs_state_rel` (w1b-03, fail note) uses `proj2`.
- **Suggested fix:** Split the conjecture into two lemmas.
  ```coq
  (* proved here, no reachability needed *)
  Lemma tfsState_del_pres_net_fwd (n n' : Network) (i : nat) (d : Delay) :
    n -ND- d -ND> n' -> tfsStateNet i n -> tfsStateNet i n'.
  (* backward direction only for reachable networks *)
  Conjecture tfsState_del_pres_net_bkwd : forall (n n' : Network) (i : nat) (d : Delay),
    reachableNet n -> n -ND- d -ND> n' -> tfsStateNet i n' -> tfsStateNet i n.
  ```
  If the iff form is preferred, keep it and add `reachableNet n ->`.
  Why the backward lemma should be provable (believed, not proved): in a reachable network the overlap component is an `overlapState` (`reachable_net_prot` / `reachableProt_triple`). So it suffices that each non-tfs overlap state delays only into non-tfs states. Those states are dormant, ovWait, ovReady, switchBc, switchCurr, switchListen, ovAbort and init. Their bodies are prefix sums, plus `ovWait`'s guarded `$<x>$` branch, whose continuation is not a tfs term. The `$<r>$ tfs*` shape used in the counterexample never arises in the protocol.
- **Partial proof:** The file's PROOF section is `Admitted`. The helpers (counterexample, both refutations and the forward-direction lemma) all compile. Only `tfsState_del_pres_net_fwd` is meant for splicing, as the replacement forward lemma.

### `NetAuxBasics.init_nextMode_net`

- **Where:** `src/NetAuxBasics.v` line 445 · **Lemma** · 2015 label: `7` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define nextModeEnt/nextModeNet (and reachableEnt) stubs; then prove by induction on reachableNet (argued; needs an init backtracking lemma).

- **Status:** BLOCKED-ON-STUB (`nextModeNet`, NetAuxBasics.v:65; via `nextModeEnt`, EntAuxDefs.v:146)
- **Intent:** in a reachable network, if entity `i`'s overlap component is in `init m` (it has just read `m` as the pending mode with `chanMNext<vM'>?`), then the mode state of entity `i` is in transition with next mode `m`, i.e. `nextModeNet m i n`.
- **Failure:** `nextModeNet` is an opaque `Parameter`. Nothing visible before line 445 has `nextModeNet` in its conclusion. The only earlier mention is `switch_states_mState` (NetAuxBasics.v:201), where it is a hypothesis. The intro/elim facts (`nextMode_ent_ex`, NetAuxBasics.v:906, and the NARMisc lemmas) come later or in later modules. Reading `nextModeNet := fun _ _ _ => False` is consistent with every visible assumption. Under that reading the target is false for any reachable network with an entity in `init m`, and such networks exist: `dormant` reads `chanMNext<m'>?` once a `stepDeTest` has made the mode state `<|m0, m', _|>`. So the target is unprovable while the stub is opaque. (The duplicate `NARMisc.init_nextMode_net`, which lacks `reachableNet n`, is outright false; see `NARMisc-1/NARMisc.init_nextMode_net.fail.md`.)
- **Ripple-up:** not in the safety cone. The only user in a live proof position is the commented-out body of `ovWait_ovReady_nextMode_net` (NetAuxBasics.v:487-545, now `Admitted (*#bism-redo*)`). That lemma feeds `ovWaitState_nextMode_net` (NetAuxBasics.v:547) and then `NARInsuff.nextSince_next` (NARInsuff.v:159).
- **Suggested fix (stub definitions; statement unchanged), consistent with `NetAuxBasics-6/NetAuxBasics.nextMode_ent_ex.fail.md`:**
  ```coq
  (* EntAuxDefs.v *)
  Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
    | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
  (* NetAuxBasics.v, after liftEntNet *)
  Definition nextModeNet (m : Mode) := liftEntNet (nextModeEnt m).
  ```
  together with the `reachableEnt` closure from `reachable_net_ent.fail.md`.
- **Proof plan under those definitions:** induct on `reachableNet n` with the invariant `initStateNet m i n -> nextModeNet m i n`. Equivalently, at entity level, overlap in `init m` ⇒ `mstEnt e = <|_, m, _|>`.
  - *Init:* `initialProc` puts the overlap component in `dormant`, which is disjoint from `init` (state disjointness).
  - *Discrete step, overlap moved into `init m`:* the only predecessor is `dormant` with action `chanMNext ;? [baseMode m]`. That needs a backtracking lemma `init_prev` (missing; `#back-track-lift`). At entity level the input must synchronise via `stepDeNextRead` with `k -ms- chanMNext .! m -ms> k'`, and only `stepMsOutNext` provides that, so `k = k' = <|m0, m, t|>`.
  - *Discrete step, overlap already in `init m`:* the mode state can change only by (a) `stepMsSwitch`, which needs a process `chanMCurr *!`. Only `switchCurr`/`tfsCurr` emit it (`ovlp_mCurr_out`, `bc_mCurr_out_not`, `listen_mCurr_out_not`), and the overlap is in `init`, so this cannot happen. (b) `stepMsAbort`, which is currently unreachable because `stepDiscEnt` has no WRITE-STBL rule (see `w1b-09/EntAuxResults.ovAbort_unstable.fail.md`). With that rule, only `ovAbort`/`tfsNext` emit it, so it still cannot happen. (c) `stepMsInit`/`stepDeTest`, which need a stable `k`. Reads (`stepMsOutCurrTrans`, `stepMsOutNext`) leave `k` unchanged, so the next mode is preserved. The step `init --chanMCurr<vM>?--> ovWait` leaves `init`, so the claim is vacuous there.
  - *Delay step:* `init` is urgent, because `init` enables `chanMCurr ;? _` and every mode state offers `chanMCurr .! _`. Alternatively, all mode-state delays (`stepMsDelTout`/`DelGuard`/`Timeout`) keep the next mode, which gives `nextModeNet_del_pres` (NetAuxBasics.v:479) directly.
- **Partial proof:** none; nothing can be proved about the opaque `nextModeNet`.

### `NetAuxBasics.ovReady_prev_net_strong`

- **Where:** `src/NetAuxBasics.v` line 451 · **Lemma** · 2015 label: `#lift-track-net #strong` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (fixed version compiles; rests on admitted link_net_prot_reach, reachableProt_triple (blacklisted), ProtAuxResults.ovReady_prev). Apply the same fix to ovReady_prev_net.

- **Status:** FALSE (counterexample). **It is inconsistent with the model axioms:** for every `m : Mode`, `t : Time`, `l : Position` it implies `False`. It belongs on the known-inconsistent list.
- **Intent:** network-level backtracking. If entity `i`'s overlap component is in `ovReady m t l` after a discrete network step, then before the step it was already `ovReady m t l` or it was `ovWait m t x0 y0`, the state whose `$<y>$chanPos<vL>?` branch leads to `ovReady`. This is the lift of the process-level `ProtAuxResults.ovReady_prev`.
- **Failure:** the statement has no `reachableNet n` hypothesis, so the overlap slot of entity `i` in `n` can hold any process term. Take
  `q := inPrefix chanPos [vL] (ovReady m t l)` (a bare position read),
  `n := [ [| nilProc $||$ q $||$ nilProc, l, h, sing m |] ]`,
  `n' := [ [| nilProc $||$ ovReady m t l $||$ nilProc, l, h, sing m |] ]`, `i := 0`, `a := anTau`.
  The step `n -NA- anTau -NA> n'` is `stepDnTauHead` + `stepDePosRead` + `stepDpParR`/`stepDpParL`/`stepDpIn`. The substitution `[vL := l]` is the identity on the closed term `ovReady m t l`. In `n'` the overlap is literally `ovReady m t l` (`bisim_refl`). Neither disjunct holds in `n`:
  - `q ~p~ ovReady m t l` is impossible. `q` can do `chanPos ;? [basePosition l]`, but `ovReady` is an output prefix and has no input (`bisim_disc_match`, then `inversion`).
  - `q ~p~ ovWait m t x0 y0` is impossible for every `x0`, `y0`. `ovWait` can always do `chanAbort *?` (leftmost summand), and `q` cannot (`bisim_symm`, `bisim_disc_match`, `inversion`).

  **Verified in Rocq** (`--explore`, rc=0): `ovReady_prev_net_strong_cex : forall m t l, ~ (forall n n' i a, <statement>)` in `NetAuxBasics.ovReady_prev_net_strong.v`. `Print Assumptions` lists **only model axioms** and the stdlib/trust-base axioms; it uses no admitted lemma.
- **Ripple-up:** not in the safety cone. The live users are:
  - **`NetAuxBasics.ovReady_prev_net` (line 1018)** has the *identical* statement. It is recorded as `.ok` in `work/NetAuxBasics-7/` with the one-line proof `eapply ovReady_prev_net_strong`, so that "proof" rests on this inconsistent lemma (its `.ok` lists `ovReady_prev_net_strong` as an axiom). **That `.ok` should not be spliced as a real proof**: `ovReady_prev_net` is false by the same counterexample, and needs the same fix.
  - `NetAuxBasics.v:505` (`ovWait_ovReady_nextMode_net`) and `NARNonFS_currSince.v:59` (`ovReady_nextSince_pending`, via `ovReady_prev_net`) call it only inside commented-out proof scripts. Both contexts have `reachableNet n` available: induction on `reachableNet`, step case `reachNetDisc`.
  - Same family, same flaw: `ovWait_prev_net_strong` (line 456; w1b-08 independently wrote a cex), and very likely `tfsStart_prev_net`, `tfsNext_prev_net`, `ovWait_prev_net` (lines 1013–1072), plus any other `#lift-track-net` backtracking lemma that lacks `reachableNet n`. The same "bare input prefix in the overlap slot" construction refutes each of them.
- **Suggested fix:** add reachability of the source network (do the same for `ovReady_prev_net`):
  ```coq
  Lemma ovReady_prev_net_strong m t l n n' i a :
    reachableNet n ->
    ovReadyStateNet m t l i n' -> n -NA- a -NA> n' ->
    ovReadyStateNet m t l i n \/
    (exists x0 y0, ovWaitStateNet m t x0 y0 i n).
  ```
  **Proved** (`ovReady_prev_net_strong_fixed` in the same file, explore rc=0). It rests only on the admitted, not-banned `link_net_prot_reach` (has `.ok` in NetAuxBasics-1), `reachableProt_triple` and `ProtAuxResults.ovReady_prev`. Sketch:
  1. Use `link_net_ent_disc_bkwd` to get the source entity `e0` at `i`.
  2. `link_net_prot_reach` + `reachableProt_triple` show that `e0`'s process is `p1 $||$ p2 $||$ p3` with `overlapState p2`.
  3. Invert the entity step. Every rule either keeps the process or takes a process step on the triple.
  4. A helper `ovReady_prev_net_strong_mid` (inversion on the triple) shows the middle component either stayed (left disjunct) or stepped. In the stepped case `ovReady_prev` gives `ovWaitState m t x zeroTime p2` (right disjunct, `y0 := zeroTime`).

  The proof even gives `y0 = zeroTime`, so the conclusion could be sharpened. Both users have `reachableNet n` in scope.
- **Partial proof:** see `NetAuxBasics.ovReady_prev_net_strong.v` (HELPERS hold the cex and the fixed-statement proof; target left `Admitted`).

### `NetAuxBasics.ovWait_prev_net_strong`

- **Where:** `src/NetAuxBasics.v` line 457 · **Lemma** · 2015 label: `#lift-track-net #strong` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (argued; same proof route as ovWait_prev_net).

- **Status:** FALSE (counterexample, checked in Rocq). NEEDS-HYPOTHESIS `reachableNet n`.
- **Intent:** backward tracking for the overlap state `ovWait(m,t,x,y)` of entity `i`. If entity `i` is in `ovWait(m,t,x,y)` after a discrete network step, then before the step it was already in `ovWait(m,t,x,y)`, or in some `ovReady(m,t0,l0)`, or in `init(m)`. (Thesis: the overlap automaton is entered only from `init` and from `ovReady`.)

## Failure

The statement has no reachability hypothesis, and `liftOverlap` does not constrain the three slots of the software triple. So any process may sit in the overlap slot and step into `ovWait`.

Counterexample, for any `m : Mode` and `t x y : Time`:
- One entity, `e = [| (chanMCurr ? nilProc) $||$ (chanMCurr ! ovWait m t x y) $||$ nilProc, l, h, sing m |]`.
- Slot 1 inputs `chanMCurr []`, which synchronises with slot 2's output (`stepDpSyncRL`). The entity takes `stepDeProcTau`, and the network takes `stepDnTauHead`, giving `[e] -NA- anTau -NA> [e']` with overlap slot `ovWait m t x y`. So `ovWaitStateNet m t x y 0 [e']` holds by `bisim_refl`.
- In `[e]` the overlap slot `chanMCurr ! ovWait m t x y` only enables `chanMCurr ;! []`. None of `ovWait m t x y`, `ovReady m t0 l0` or `init m` can match this action:
  - `ovWait` enables only inputs on `chanAbort`, `chanBad` and `chanPos`, and an output on `chanPause`;
  - `ovReady` outputs on `chanOutProc`;
  - `init` inputs on `chanMCurr`.
- So all three disjuncts are false.

The `.cex.v` file `work/w1b-08/NetAuxBasics.ovWait_prev_net_strong.cex.v` proves two lemmas:
- `ovWait_prev_net_strong_cex m t x y : exists n n' a, ovWaitStateNet m t x y 0 n' /\ n -NA- a -NA> n' /\ ~(disjunction)`;
- `ovWait_prev_net_strong_refuted : (target statement) -> Mode -> False`.

It compiles in `--explore`. `Print Assumptions` lists only the ComhBasics model axioms plus the stdlib reals, proof irrelevance and functional extensionality. It uses no admitted lemma.

## Ripple-up

- The target is not in the safety cone.
- Its only textual uses are inside commented-out proofs:
  - `NetAuxBasics.ovWait_ovReady_nextMode_net` (NetAuxBasics.v:502). Its proof body is commented out and it ends `Admitted`.
  - `NARTop.ovWait_sent` (NARTop.v:127, also commented out).
- Both callers have reachability in scope. In each, the inductive `reachNetDisc` case has `reachableNet n` for the predecessor network.
- The same counterexample, with slot 2 = `chanMCurr ! ovReady m t l`, refutes the sibling `NetAuxBasics.ovReady_prev_net_strong` (line 451). It also refutes `ovWait_prev_net` (line 1072), which has the same shape and also lacks reachability.
- `ovReady_prev_net` (line 1018) has been accepted as a one-line consequence of `ovReady_prev_net_strong`, so it inherits that lemma's falsity. Its statement also lacks `reachableNet n`. Flagging this for the lead.

## Suggested fix

```coq
Lemma ovWait_prev_net_strong m t x y n n' i a :
  reachableNet n ->
  ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
  ovWaitStateNet m t x y i n \/
  (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
  initStateNet m i n.
```
(Make the same change to `ovReady_prev_net_strong`, `ovReady_prev_net` and `ovWait_prev_net`.)

## Why the fixed statement should be provable

1. `link_net_ent_disc_bkwd` gives an entity `e = [|p,l,h,k|]` at `i` in `n`, with either `e = e'` or `e -EA- b ->> e'`.
2. Reachability, through `reachable_net_prot` and `reachableProt_triple`, makes `p` a `protocolState` triple `p1 $||$ q $||$ p3`. Here `overlapState q`, and `p1` and `p3` are broadcast and listener states.
3. Invert the entity step and then the `parComp` step:
   - If `q` is unchanged, we get the first disjunct.
   - If `q -PA- a -PA> q'` (alone or as half of a sync), the process-level `ProtAuxResults.ovWait_prev` (Qed) gives `ovReadyState m (t + period m) l q` (second disjunct) or its init branch.

Caveat for whoever proves the fixed version: `ovWait_prev`'s init branch is stated as `initStateProt m p` (= `liftOverlap (initState m) p`) about the *overlap component* `p`. It should almost certainly say `initState m p`. As stated, that branch would need `q` itself to be a triple, so the third disjunct cannot be produced from it directly. It may be vacuous, since the lemma is Qed via `backtrack_weed`, but check this before relying on it.

## Partial proof

None. The counterexample settles the target as stated.

### `NetAuxBasics.nextMode_pres_fwd_net`

- **Where:** `src/NetAuxBasics.v` line 463 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub; missing-WRITE-STBL-rule`
- **Fix (audit summary):** Define nextModeNet stubs; if the thesis WRITE-STBL rule is added to stepDiscEnt, also exclude tfsNext in the hypothesis. Argued only.

- **Status:** BLOCKED-ON-STUB (`nextModeNet`, NetAuxBasics.v:65). Under the thesis semantics it also NEEDS-HYPOTHESIS (exclude `tfsNext`); see below.
- **Intent:** a discrete network step preserves entity `i`'s pending next mode `m`, unless entity `i` is in one of the states that can rewrite its mode state: `switchCurr`/`tfsCurr` (output `chanMCurr!`, which commits the switch) and `ovAbort` (output `chanMStable!`, which aborts it).
- **Failure (as stated, current Rocq code):** `nextModeNet` is an opaque `Parameter`, and the goal is `nextModeNet m i n'` from `nextModeNet m i n`. No visible lemma before line 463 produces `nextModeNet`; it occurs only as a hypothesis, in `switch_states_mState`, NetAuxBasics.v:201, and `init_nextMode_net`, :445, both admitted. Take `nextModeNet := fun _ _ n => n = n0`, for a fixed reachable `n0` that can take a discrete step to some `n1 <> n0` (e.g. any `stepDeTest` step) with no entity in `switchCurr`/`ovAbort`/`tfsCurr`, together with `currModeNet := fun _ _ _ => True`. That interpretation satisfies every visible assumption and refutes the target. So it can't be proved while the stub is opaque.
- **Second problem (semantic; matters once the stub is filled):**
  - The Rocq `stepDiscEnt` (EntityLanguage.v:127) lacks the thesis rule **WRITE-STBL** (`P --chanStable!--> P'`, `K --chanStable?--> K'` ⟹ `τ`; thesis.txt ≈5477). Currently no process output on `chanMStable` can ever reach the mode state.
  - Under the current code, then, the lemma is plausibly true: on an unstable mode state the only discrete mode-state change is `stepMsSwitch` via `stepDeCurrWrite`. That needs a `chanMCurr *!` output, and only `switchCurr`/`tfsCurr` produce one (`ovlp_mCurr_out`, `bc_mCurr_out_not`, `listen_mCurr_out_not`).
  - The excluded list contains `ovAbort`, though, which shows the author intended WRITE-STBL. **Once WRITE-STBL is restored, the statement is false**, because `tfsNext m0 = chanMNext<fsSucc m0>! tfsCurr + chanMStable! tfsNext m0` also emits `chanMStable!` ("the existing mode transition is cancelled via a self-loop outputting on chanStable", thesis §overlap). Concrete reachable run:
    1. Mode state `sing m0` with overlap `dormant`.
    2. `stepDeTest` gives mode state `<|m0, m', T|>`, so `nextModeNet m' i`.
    3. The listener emits `chanBad!`, and `dormant --chanBad?--> tfsStart`.
    4. `tfsStart --chanMCurr<m0>?--> tfsNext m0` (via `stepMsOutCurrTrans`, mode state unchanged).
    5. WRITE-STBL: `tfsNext m0 --chanMStable!--> tfsNext m0` with `<|m0,m',T|> --chanMStable?--> sing m0`.

    At step 5 the pre-state satisfies all hypotheses (`tfsNext` is not excluded), but `nextModeNet m' i n'` fails.
- **Ripple-up:** not in the safety cone. The only use is inside the commented-out proof of `ovWait_ovReady_nextMode_net` (NetAuxBasics.v:521, now `Admitted (*#bism-redo*)`). There the exclusion is discharged by state disjointness from `ovWait`/`ovReady`/`init`, so adding `tfsNext` to the exclusion costs nothing.
- **Suggested fix:**
  1. Stubs, as in `NetAuxBasics-6/NetAuxBasics.nextMode_ent_ex.fail.md`:
     `Inductive nextModeEnt (m' : Mode) : Entity -> Prop := nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).` and `Definition nextModeNet m := liftEntNet (nextModeEnt m).`
  2. If WRITE-STBL is (re)added to `stepDiscEnt`, strengthen the hypothesis (needs owner approval):
     ```coq
     Lemma nextMode_pres_fwd_net m i n n' a :
       reachableNet n -> nextModeNet m i n ->
       ~(switchCurrStateNet i n \/ ovAbortStateNet i n \/
         tfsCurrStateNet i n \/ (exists m0, tfsNextStateNet m0 i n)) ->
       n -NA- a -NA> n' -> nextModeNet m i n'.
     ```
- **Proof plan (with those definitions):**
  - Decompose the network step at `i`. Either entity `i` is unchanged (done), or it takes an entity step `e -EA- a' ->> e'` with `mstEnt e = <|m1, m, t|>`. Use `link_net_ent_disc_bkwd`.
  - Case on the `stepDiscEnt` rule. Every rule except `stepDeCurrWrite`, `stepDeRdStbl` and `stepDeTest` (plus `stepDeWrStbl` if added) keeps `k` unchanged, or keeps it via `stepMsOutCurrTrans`/`stepMsOutNext`.
    - `stepDeRdStbl` and `stepDeTest` need a stable `k` (`stepMsOutStable`/`stepMsInit`). Invert to get a contradiction.
    - `stepDeCurrWrite` needs `p -PA- chanMCurr *! -PA> p'`. Use `link_net_prot_reach` to get `reachableProt`, then the parTriple decomposition with `bc_mCurr_out_not`, `listen_mCurr_out_not` and `ovlp_mCurr_out`. These force `switchCurr` or `tfsCurr`, which contradicts the exclusion.
    - (`stepDeWrStbl`, if added: the same argument with `bc_mStable_out_not` and a listener analogue. The overlap must then be `ovAbort` or `tfsNext`, which are excluded.)
- **Partial proof:** none; nothing can be proved about the opaque `nextModeNet`.

### `NetAuxBasics.ovWait_del_pres_bkwd_net_strong`

- **Where:** `src/NetAuxBasics.v` line 471 · **Lemma** · 2015 label: `#del-pres-net #strong` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability; noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n -> 0 < y ->` (or the weaker `exists x0, ovWaitStateNet m t x0 (y +dt+ d) i n`); argued, not proved.

- **Status:** FALSE (counterexample, machine-checked in Rocq)
- **Intent:** if entity `i` is in the overlap state `ovWait m t x y` after a network delay `d`, then before the delay it was in `ovWait m t (x+d) (y+d)`. Both countdown timers run down linearly, and `m`, `t` are unchanged.
- **Failure:** the lemma has no reachability hypothesis. The source entity's overlap component can be any process that delays *into* something bisimilar to `ovWait m t x y` without being bisimilar to `ovWait m t (x+d) (y+d)`. This is the same mechanism as the (FALSE) `bcWaitNet_del_bkwd` write-up by NetAuxBasics-2, transplanted to the overlap (middle) component.
  Counterexample (any `m : Mode`), single-entity networks, with `T1 = 1`, `D1 = 1`, `X = ovWait m 0 0 0` and `h0` the interface with three empty lists:
  - `n  = [ [| nilProc $||$ (del T1 X $||$ nilProc), origin, h0, sing m |] ]`
  - `n' = [ [| nilProc $||$ (del (1-1) X $||$ nilProc), origin +p+ origin, h0, sing m |] ]`
  - `n -ND- D1 -ND> n'` holds:
    - `stepTpDelSub` delays the guard. The nils delay to themselves, and the `stepTpPar` sort conditions hold vacuously because `nilProc` has empty sort.
    - The empty interface and `sing m` delay to themselves, and the displacement is 0.
    - `noSync` holds vacuously: no strict delay-derivative of the process has a discrete action, because the guard stays positive.
  - `ovWaitStateNet m 0 0 0 0 n'` holds, because `del e Y ~p~ Y` whenever `e` evaluates to `zeroTime`.
  - `~ ovWaitStateNet m 0 (0 +dt+ D1) (0 +dt+ D1) 0 n`: any process bisimilar to an `ovWait` can input on `chanAbort` now (`activation_tac`). `del T1 X` with `T1 > 0` has no discrete transition.

  In `NetAuxBasics.ovWait_del_pres_bkwd_net_strong.v` (HELPERS, checks with `--explore`) these are proved:
  - `ovWait_del_pres_bkwd_net_strong_cx (m : Mode) : exists n n' d t x y i, n -ND- d -ND> n' /\ ovWaitStateNet m t x y i n' /\ ~ ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n`
  - `ovWait_del_pres_bkwd_net_strong_refuted : forall m, ~ (<the target statement>)`

  `Print Assumptions` lists only model axioms and the trusted stdlib axioms (proof_irrelevance, functional_extensionality_dep, ClassicalDedekindReals). No admitted lemma is used.
- **Second problem, even for reachable networks, when `y = 0`:** `noSync` (EntityLanguage.v) covers only interface and mode-state synchronisation. The position read on `chanPos` is not urgent (see the bcWait note). So a reachable entity in `ovWait m t x' y'` with `y' < d` can delay by `d`. Its derivative is bisimilar to `ovWait m t (x'-d) 0`, while the lemma would claim `y' = d`. So `0 < y` is needed. The `x` timer is probably urgent in reachable states, because the listener normally offers `chanPause?`, but proving that needs a cross-component invariant. Hence the conservative fix below quantifies `x` existentially.
- **Ripple-up:** the only user is `NARTop.ovWait_sent` (line ~154, the delay case of `induction p` on `p : reachableNet n`). NARTop also has a duplicate admitted copy of this statement at line 100, marked "DELETE ON RECOMPILE". The target is in the safety cone. In that delay case, `p : reachableNet n` (the predecessor) and `U0 : 0 < y` are in context. The induction hypothesis is quantified over every `x`, so the user never needs the precise `x`.
- **Suggested fix:**
  ```coq
  Lemma ovWait_del_pres_bkwd_net_strong n n' d m t x y i :
    reachableNet n -> 0 < y -> n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
    ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n.
  ```
  or, if the `chanPause` urgency invariant is not wanted, the weaker form below. It still suffices for `ovWait_sent`: `destruct (...) as [x0 OPB]. apply IHp in OPB`.
  ```coq
  Lemma ovWait_del_pres_bkwd_net_strong n n' d m t x y i :
    reachableNet n -> 0 < y -> n -ND- d -ND> n' -> ovWaitStateNet m t x y i n' ->
    exists x0, ovWaitStateNet m t x0 (y +dt+ d) i n.
  ```
  Why provable: link back to the entity and its overlap component `p`, which delays `p -d-> p'` with `p' ~ ovWait m t x y`. Reachability makes `p` an `overlapState`. Every non-`ovWait` overlap state either delays to itself and cannot be bisimilar to an `ovWait` (it lacks a timed `chanPos`), or is urgent. For `p ~ ovWait m0 t0 x0 y0`:
  - If `d <= x0, y0`, then `ProtAuxResults.ovWait_del_pres_strong` (proved by me in `ProtAuxResults.ovWait_del_pres.v` HELPERS) gives `p' ~ ovWait m0 t0 (x0-d) (y0-d)`.
  - If `d > y0`, then `p'` offers `chanPos?` now, which contradicts `0 < y`.
  - In the remaining cases you need a "timer shift" lemma, `ovWait m0 t0 a b ~ ovWait m t a' b' -> ovWait m0 t0 (a+d) (b+d) ~ ovWait m t (a'+d) (b'+d)`. Use bisimulation up to the delay prefix. Note that `t` is *not* recoverable from bisimilarity in general: `eSubtract t (period m)` is ill-defined below 0 and idles. So stick to shift-invariance rather than injectivity.
- **Partial proof:** none for the target. The verified counterexample and its reusable helpers (`del e Y ~ Y` for a zero guard, and no discrete action under a positive guard in the middle component) are in `NetAuxBasics.ovWait_del_pres_bkwd_net_strong.v`.

### `NetAuxBasics.ovReady_del_pres_bkwd_net`

- **Where:** `src/NetAuxBasics.v` line 475 · **Lemma** · 2015 label: `#del-pres-net` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability; incomplete-definition (overlapState)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (for reachable n the premise is in fact impossible); proof needs a complete overlapState for reachableProt_triple. Argued, not proved.

- **Status:** FALSE (counterexample, checked in Rocq, no admitted lemmas used). It also NEEDS-HYPOTHESIS `reachableNet n`.
- **Intent:** backward delay preservation. If entity `i` is in the overlap state `ovReady m t l` after a network delay, it was already in `ovReady m t l` before it.
- **Failure:** there is no reachability hypothesis, so the source entity can run any process that delays *into* something bisimilar to `ovReady m t l` without being bisimilar to it. This is the same construction as NetAuxBasics-2's verified counterexample for `bcWaitNet_del_bkwd`, moved to the overlap slot. Take any `m : Mode`, `T1 = 1`, `D1 = 1`, `X = ovReady m zeroTime origin`, and `h0` the interface with three empty lists:
  - `n  = [ [| nilProc $||$ (del T1 X $||$ nilProc), origin, h0, sing m |] ]`
  - `n' = [ [| nilProc $||$ (del (1-1) X $||$ nilProc), origin +p+ origin, h0, sing m |] ]`
  - `n -ND- D1 -ND> n'`: `stepTpDelSub` on the guard; the nils, the empty interface and the stable mode state delay to themselves; displacement is 0. `noSync` holds vacuously: no delay-derivative strictly before `D1` has any discrete action, because the guard is still positive and `stepDpTimeOut` needs it to be zero.
  - `ovReadyStateNet m zeroTime origin 0 n'`: `del e X ~ X` when `e` evaluates to `zeroTime` (bisimulation proved directly).
  - `~ ovReadyStateNet m zeroTime origin 0 n`: anything bisimilar to `ovReady m t l` can output `chanOutProc ;! [m, l]` now (`activation_tac`). `del T1 X` with `T1 > 0` has no discrete transition.

  The Rocq proof is in the HELPERS of `NetAuxBasics.ovReady_del_pres_bkwd_net.v` and passes `--explore`. It contains:
  - `ovReady_del_pres_bkwd_net_cx (m : Mode) : exists n n' d t l i, n -ND- d -ND> n' /\ ovReadyStateNet m t l i n' /\ ~ ovReadyStateNet m t l i n`
  - `ovReady_del_pres_bkwd_net_false : (statement) -> forall m : Mode, False`

  `Print Assumptions` shows only model axioms plus `proof_irrelevance`, `functional_extensionality_dep` and `ClassicalDedekindReals`.
- **Ripple-up:** `in_safety_cone=False`. The only use is inside the commented-out proof of `NetAuxBasics.ovWait_ovReady_nextMode_net` (line ~541, `Admitted (*#bism-redo*)`), in the delay case of an induction on `reachableNet n`, where the predecessor's reachability is in scope. `NARMisc.ovWait_ovReady_nextMode_net` is a separate admitted lemma and does not use it. Nothing proved depends on it.
- **Suggested fix:**
  ```coq
  Lemma ovReady_del_pres_bkwd_net n n' d m t l i : reachableNet n ->
    n -ND- d -ND> n' -> ovReadyStateNet m t l i n' -> ovReadyStateNet m t l i n.
  ```
  This is enough for the user (the IH's `reachableNet n` is in context there). For reachable `n` the premise is in fact impossible, so the conclusion holds vacuously, and a cleaner statement is `reachableNet n -> n -ND- d -ND> n' -> ovReadyStateNet m t l i n' -> False`. Why: the overlap component of a reachable entity is one of the overlap states. Each of them delays to itself, or (for `ovWait`'s guarded summands) to a sum that still offers `chanAbort?`/`chanBad?`. `ovReady` (a single `chanOutProc!` prefix) offers neither, so none of these is bisimilar to `ovReady` after a delay. `ovReady` itself can't be the source either: it can always output on `chanOutProc`, the interface can always input on `chanOutProc` (`stepIntBuffOut`), so `noSync` fails and an entity in `ovReady` can't delay at all (urgency).
  Caveat for the proof: it needs `reachableProt_triple` with a *complete* `overlapState`. The current `overlapState` has only the `dormant` and `ovWait` constructors (it is marked INCOMPLETE), and with that definition `reachableProt_triple` is itself false (e.g. `init` is reachable).
- **Partial proof:** none for the target; see the verified counterexample in the `.v` file.

### `NetAuxBasics.nextModeNet_del_pres`

- **Where:** `src/NetAuxBasics.v` line 479 · **Lemma** · 2015 label: `6` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define nextModeEnt/nextModeNet stubs; proof under them compiles (nextModeNet_del_pres_under_def; rests on admitted link_net_ent_del_fwd).

- **Status:** BLOCKED-ON-STUB (`nextModeNet`, NetAuxBasics.v:65; meaning via `nextModeEnt`, EntAuxDefs.v:146)
- **Intent:** delay does not change an entity's pending (next) mode: if entity `i` is mid-transition to `m`
  in `n` and `n -ND- d -ND> n'`, it is still mid-transition to `m` in `n'`.
- **Failure:** `nextModeNet` is an opaque `Parameter`. Before l.479 the only facts mentioning it are
  `switch_states_mState` (l.201, hypothesis only), `init_nextMode_net` (l.445, introduction from `initStateNet`)
  and `nextMode_pres_fwd_net` (l.463, discrete steps only). None eliminates `nextModeNet` or mentions delay.
  Independence: interpret `nextModeNet m i n := liftEntNet (nextModeEnt m) i n \/ (length n <= i /\ Q n)`
  with `Q` a network property preserved by discrete steps but not by delay (e.g. "some entity is at the
  origin", as in NetAuxBasics-5's currModeNet_del_pres write-up). Every visible lemma still holds:
  out-of-range `i` makes all state-predicate hypotheses false, and discrete steps preserve length and
  positions. Delay can falsify `Q`.
  The trap applies here too: `transGuard_del`/`transGuard_disc_pres` give `Mode -> False` and `m : Mode` is
  bound, but they are forbidden and were not used.
- **Ripple-up:** the only occurrence (NetAuxBasics.v:542) is inside the *commented-out* old proof of
  `NetAuxBasics.ovWait_ovReady_nextMode_net` (Admitted `#bism-redo`). So no live user. `show`:
  `in_safety_cone=False`.
- **Suggested fix:** complete the stubs, with the statement unchanged (same proposal as NetAuxBasics-6's
  `nextMode_ent_ex` write-up):
  ```coq
  (* EntAuxDefs.v *)
  Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
    | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
  (* NetAuxBasics.v *)
  Definition nextModeNet (m : Mode) := liftEntNet (nextModeEnt m).
  ```
  With these the target is provable. **Rocq-checked** in explore mode against local copies
  (`NetAuxBasics.nextModeNet_del_pres.demo.v`, all `Qed`, relying only on `link_net_ent_del_fwd`, which is
  admitted in NetworkLanguage):
  ```coq
  Lemma nextModeNet_del_pres_ent_del (e e' : Entity) (d : Delay) (m : Mode) :
    e -ED- d ->> e' -> nextModeNet_del_pres_ent m e -> nextModeNet_del_pres_ent m e'.
  Proof.
    intros D X. inversion X; subst. inversion D; subst.
    match goal with K : _ -ms- _ -ms> _ |- _ =>
      destruct (delMStatePresTrans _ _ _ _ _ K) as [t' E] end.
    subst. constructor.
  Qed.
  (* then: intros ND [e X E]; destruct (link_net_ent_del_fwd n n' e i d ND E) as [e' [E' D]];
     econstructor; [eapply nextModeNet_del_pres_ent_del; eassumption | exact E']. *)
  ```
  The key fact is `ModeStateLanguage.delMStatePresTrans`: delay keeps `<| m1, m2, _ |>` in transState form
  with the same `m2`.
- **Partial proof:** demonstration only (not for splicing), see `.demo.v`.

### `NetAuxBasics.currMode_pres_fwd`

- **Where:** `src/NetAuxBasics.v` line 592 · **Theorem** · 2015 label: `7` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define the currModeNet stub; proof under it compiles (currMode_pres_fwd_stub) but rests on admitted link_net_ent_disc_fwd.

- **Status:** BLOCKED-ON-STUB (currModeNet)
- **Intent:** If entity `i` has some current mode in `n` and `n -NA- a -NA> n'`, then it has some current mode in `n'`. In other words, discrete network steps preserve entities, and every entity has a current mode.
- **Failure:** `currModeNet` is an opaque `Parameter` (NetAuxBasics.v:56). No earlier lemma can produce `currModeNet _ i n'` from these hypotheses. The only earlier lemma that concludes `currModeNet`, `switch_states_mState`, needs switchCurr/switchListen/nextMode hypotheses that are not available.
- **Ripple-up:** Not in the safety cone. No uses in the frozen sources (`grep -n currMode_pres_fwd *.v` finds only its own declaration).
- **Suggested fix (stub definition):** the same as for `currMode_pres_bkwd`:
  ```coq
  Definition currModeNet (m : Mode) (i : nat) (n : Network) : Prop :=
    exists e, e @ i .: n /\ currModeEnt e = m.
  ```
- **Proof under that definition** (checked in Rocq with a local copy of the definition; see `stub_validation.currModeNet_reachableEnt.v`):
  ```coq
  Proof.
    intros ST [e [EIN _]].
    destruct (link_net_ent_disc_fwd n n' e i a ST EIN) as [e' [EIN' _]].
    exists (currModeEnt e'). exists e'. split; [assumption | reflexivity].
  Qed.
  ```
  It relies on `link_net_ent_disc_fwd` (NetworkLanguage.v:424), which is still `Admitted`.

### `NetAuxBasics.transGuard_disc_pres`

- **Where:** `src/NetAuxBasics.v` line 788 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:expired-guard-switch (stepDeCurrWrite+stepMsSwitch turns <|m,m',0|> into sing m')` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `0 < t ->` (fixed version compiles, rests on admitted link_net_ent_disc_fwd) or delete the unused conjecture.

- **Status:** FALSE (counterexample, verified in Rocq: the conjecture implies `Mode -> False`)
- **Intent:** A discrete action does not change the remaining guard `t` of a mode transition `<| m, m', t |>`.
- **Failure:** When the guard has expired (`t = zeroTime`), the entity rule `stepDeCurrWrite` together with `stepMsSwitch` (`<| m, m', zeroTime |> -ms- chanMCurr @? -ms> m'`) turns the transition state into the stable state `sing m'`. After that there is no `transGuard` at all.
  Counterexample (one-entity network, any `m : Mode`):
  `n = [ [| outPrefix chanMCurr [] nilProc, origin, emptyIface, <|m, m, zeroTime|> |] ]`, `n' = [ [| nilProc, origin, emptyIface, sing m |] ]`, with `n -NA- anTau -NA> n'` by `stepDnTauHead`/`stepDeCurrWrite`/`stepDpOut`/`stepMsSwitch`. Then `transGuard zeroTime 0 n` holds but `transGuard zeroTime 0 n'` does not.
  Verified (explore mode, `Qed`):
  ```coq
  Lemma transGuard_disc_pres_refute :
    (forall (n n' : Network) (a : ActDiscNet) (t : Time) (i : nat),
      n -NA- a -NA> n' -> transGuard t i n -> transGuard t i n') ->
    Mode -> False.
  ```
  (Full script in `NetAuxBasics.transGuard_disc_pres.v`.) Since `Mode` has no inhabitant among the model axioms, the context is not outright inconsistent. But any lemma that binds a `m : Mode` can be "proved" from this conjecture, so the lead must watch for that.
- **Ripple-up:** `grep` finds no user anywhere in the development. It is not in the safety cone, so nothing breaks.
- **Suggested fix:** add a positivity hypothesis on the guard (only `stepMsSwitch` changes a transition state under a discrete step, and it needs guard `zeroTime`):
  ```coq
  Lemma transGuard_disc_pres : forall (n n' : Network)
    (a : ActDiscNet) (t : Time) (i : nat),
    n -NA- a -NA> n' -> 0 < t -> transGuard t i n -> transGuard t i n'.
  ```
  Verified provable (explore mode, `Qed`, needs `Lra`, uses admitted `link_net_ent_disc_fwd`):
  ```coq
  Proof.
    intros n n' a t i ST POS TG. destruct TG as [p l h m m' E].
    destruct (link_net_ent_disc_fwd n n' _ i a ST E) as [e' [E' [EQ | [a' STE]]]].
    - subst e'. econstructor. exact E'.
    - inversion STE; subst;
      try (econstructor; exact E');
      try match goal with
          | K : <| _, _, _ |> -ms- _ -ms> _ |- _ =>
              inversion K; subst;
              first [ econstructor; exact E'
                    | simpl in POS; lra ]
          end.
  Qed.
  ```
  Alternatively, delete the conjecture, since it is unused.

### `NetAuxBasics.transGuard_del`

- **Where:** `src/NetAuxBasics.v` line 809 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:no-urgency-hypothesis (expired mode-state guard can delay when software offers no chanMCurr!)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `tfsCurrStateNet i n ->` (available at the only use, NARMisc.tfs_transGuard; argued, needs time-splitting proof) or use the proved weak form `exists t', transGuard t' i n' /\ ((t' = zeroTime /\ t < d) \/ t = t' +dt+ d)` (compiles, rests on admitted link_net_ent_del_fwd).

- **Status:** FALSE (counterexample, verified in Rocq: the conjecture implies `Mode -> False`)
- **Intent:** Delaying by `d` lowers a transition guard `t` to exactly `t - d`, with the proof obligation `d <= t`. In other words, no entity can delay past the expiry of its mode-transition guard.
- **Failure:** The mode-state semantics lets a transition state delay past its guard. `stepMsTimeout` covers `t < d` and gives `<|m,m',zeroTime|>`. `stepMsDelTout` lets `<|m,m',zeroTime|>` delay forever. At entity level, delay is blocked only by `noSync`, and that blocks only if the software can actually do `chanMCurr *!`. An entity whose software is `nilProc` (or anything not offering `chanMCurr *!`) delays freely. The conjecture has no reachability or state hypothesis.
  Counterexample (any `m : Mode`): `e = [| nilProc, origin, emptyIface, <|m, m, zeroTime|> |]` delays by `d = 1` to `[| nilProc, origin +p+ origin, emptyIface, <|m,m,zeroTime|> |]` (`stepTeDel` with `delta = origin`; `noSync` is vacuous for `nilProc`). Then `transGuard zeroTime 0 [e]` holds, and the conjecture would give a proof of `1 <= 0`.
  Verified (explore mode, `Qed`; full script in `NetAuxBasics.transGuard_del.v`):
  ```coq
  Lemma transGuard_del_refute :
    (forall (n n' : Network) (d : Delay) (t : Time) (i : nat),
      n -ND- d -ND> n' -> transGuard t i n ->
      exists p, transGuard (minusTime t d p) i n') ->
    Mode -> False.
  ```
  **Warning:** this conjecture sits before `currModeNet_del_pres`, `currModeNet_dec` and everything after it. Any of them that binds an `m : Mode` can be closed by `exfalso` via this refutation. Reject such proofs.
- **Ripple-up:** used only in `NARMisc.tfs_transGuard` (delay case, l.326), which feeds `NARMisc` l.379 (tfs bound for `tfsCurr`). Not in the safety cone. In that use site the entity is known to be in `tfsCurrStateNet i n` (hypothesis `H2` after `rewrite`).
- **Suggested fix:** two options.
  1. *Weakened, true for all networks* (verified provable in explore mode, `Qed`):
     ```coq
     Lemma transGuard_del : forall (n n' : Network) (d : Delay) (t : Time) (i : nat),
       n -ND- d -ND> n' -> transGuard t i n ->
       exists t', transGuard t' i n' /\ ((t' = zeroTime /\ t < d) \/ t = t' +dt+ d).
     Proof.
       intros n n' d t i ND TG. destruct TG as [p l h m m' E].
       destruct (link_net_ent_del_fwd n n' _ i d ND E) as [e' [E' D]].
       inversion D; subst.
       match goal with K : <| _, _, _ |> -ms- _ -ms> ?k' |- _ =>
         destruct (delMStatePresTrans _ _ _ _ _ K) as [t' Ek]; subst k';
         exists t'; split; [econstructor; exact E' | apply (delMStateTrans _ _ _ _ _ _ _ K)] end.
     Qed.
     ```
     This alone is not enough for `tfs_transGuard`, which needs the second disjunct.
  2. *What `tfs_transGuard` actually needs*: add the urgency context available at the call site:
     ```coq
     Conjecture transGuard_del : forall (n n' : Network) (d : Delay) (t : Time) (i : nat),
       n -ND- d -ND> n' -> tfsCurrStateNet i n -> transGuard t i n ->
       exists p, transGuard (minusTime t d p) i n'.
     ```
     I believe this is true. In `tfsCurr` the overlap component is bisimilar to `chanAbort? .. $+$ chanBad? .. $+$ chanMCurr!tfsBcN`, so the software offers `chanMCurr *!`. A mode state with expired guard offers `chanMCurr @?` (`stepMsSwitch`). So `noSync` forbids any delay that passes the guard's expiry: take `d' = t < d` for `t > 0`, or the immediate `noSyncNow` when `t = 0`. That forces `d <= t` and `stepMsDelGuard`. Proving it needs process-level time splitting and is a level-5-ish job. At the call site in `tfs_transGuard`, pass the `tfsCurrStateNet i n` hypothesis (`H2`).

### `NetAuxBasics.nextMode_ent_ex`

- **Where:** `src/NetAuxBasics.v` line 905 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define nextModeNet := liftEntNet (nextModeEnt m) and nextModeEnt as an Inductive on <| m, m', t |>; compiles.

- **Status:** BLOCKED-ON-STUB (`nextModeNet`, NetAuxBasics.v:65; also `nextModeEnt`, EntAuxDefs.v:146, for the meaning)
- **Intent:** `nextModeNet m i n` holds iff entity `i` of `n` exists and has next mode `m`. This lifts `nextModeEnt`.
- **Failure:** `nextModeNet` is an opaque `Parameter` with no introduction or elimination conjecture anywhere before the target. Neither direction is derivable: interpreting it as `fun _ _ _ => True` refutes `->` on `[]`, and as `fun _ _ _ => False` refutes `<-` whenever `nextModeEnt` holds of some entity. (`nextModeEnt` is itself a Parameter. The admitted lemmas `nextModeEnt_not_stable` and `nextMode_ent_mState` constrain it only in one direction.)
- **Ripple-up:** not in the safety cone. Its only user is the tactic `nextMode_ent_ex_tac` (NetAuxBasics.v:916), which is never invoked in the frozen sources.
- **Suggested fix:** complete the stubs, with the statement unchanged:
  ```coq
  (* NetAuxBasics.v, after liftEntNet (or as a one-constructor Inductive in place) *)
  Definition nextModeNet (m : Mode) := liftEntNet (nextModeEnt m).
  (* EntAuxDefs.v, per its 'Idea' comment *)
  Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
    | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
  ```
  With the first definition the target is proved by `split; [intros [e X E]; eauto | intros [e [E X]]; econstructor; eassumption]`, whatever `nextModeEnt` is. With the second, `nextModeEnt_not_stable` and `nextMode_ent_mState` (EntAuxResults) become one-line inversions. All of this was checked in --explore against local copies: `nextMode_ent_ex_with_def`, `nextMode_ent_ex_nextModeEnt_mState` and `nextMode_ent_ex_nextModeEnt_not_stable` in NetAuxBasics.nextMode_ent_ex.v.
- **Partial proof:** see the HELPERS (demonstration only, not for splicing).

### `NetAuxBasics.tfsNext_currModeNet_eq`

- **Where:** `src/NetAuxBasics.v` line 936 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Add `reachableNet n ->`; the fixed version compiles (tfsNext_currModeNet_eq_reach) but rests on currMode_ent_ex, reachable_net_ent, tfsNext_currMode and the currModeNet/reachableEnt stubs.

- **Status:** NEEDS-HYPOTHESIS (`reachableNet n`). Also BLOCKED-ON-STUB (`currModeNet`) as a secondary issue, but the visible Conjecture `currMode_ent_ex` already gets around that.
- **Intent:** if entity `i` is in the overlap state `tfsNext m2` (about to write the fail-safe successor of `m2` as its next mode), then its current mode is `m2`.
- **Failure:** `tfsNextStateNet m2 i n` constrains only the *software* component of entity `i` (via `liftEntNet`/`liftProcEnt`/`liftOverlap`). It says nothing about the mode state. The link between the two is an invariant of reachable states, captured at entity level by `EntAuxResults.tfsNext_currMode : reachableEnt e -> tfsNextStateEnt m e -> currModeEnt e = m`, which carries the reachability hypothesis. Without reachability the statement is false whenever `Mode` has two distinct elements. Counterexample: `n = [ [| tfsNext m2 $||$ tfsNext m2 $||$ tfsNext m2, mkPosition 0 0, h0, sing m1 |] ]` with `m1 <> m2` and any interface `h0`. Then `currModeNet m1 0 n` holds by `currMode_intro` and `tfsNextStateNet m2 0 n` holds by `bisim_refl`. This is verified in Rocq (--explore): `tfsNext_currModeNet_eq_collapses_Mode` proves `(statement) -> forall m1 m2 : Mode, m1 = m2`, so the statement (with the intended `currModeNet`) forces `Mode` to be a singleton. `Mode` is an abstract `Axiom`, so this is not a refutation inside the current axioms. It does contradict every intended model (e.g. one with a non-fail-safe mode).
- **Ripple-up:** not in the safety cone. `grep` finds no users in the frozen sources.
- **Suggested fix:**
  ```coq
  Lemma tfsNext_currModeNet_eq m1 m2 i n : reachableNet n -> currModeNet m1 i n ->
    tfsNextStateNet m2 i n -> m1 = m2.
  Proof.
    intros R C T. apply currMode_ent_ex in C. destruct C as [e [E CE]].
    destruct T as [e' T E']. lets EQ : entInNetUnique E E'. subst e'.
    lets RE : reachable_net_ent R E. lets Q : tfsNext_currMode RE T. congruence.
  Qed.
  ```
  This compiles at the target's position (helper `tfsNext_currModeNet_eq_reach` in NetAuxBasics.tfsNext_currModeNet_eq.v, --explore). It relies on `currMode_ent_ex` (blocked on the `currModeNet` stub), `reachable_net_ent` (Conjecture) and `tfsNext_currMode` (Admitted, D- reachableEnt). The in-file sketch ("induction on reachable…") also presupposes reachability.
- **Partial proof:** see HELPERS in NetAuxBasics.tfsNext_currModeNet_eq.v (demonstration only, not for splicing).

### `NetAuxBasics.tfsStart_prev_net`

- **Where:** `src/NetAuxBasics.v` line 1013 · **Lemma** · 2015 label: `#lift-track-net` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:missing-dormant-predecessor; missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add a `dormantStateNet i n` disjunct AND `reachableNet n ->` (only use, commented-out tfsStart_tfs_zero, has p). Argued, not proved.

- **Status:** FALSE (counterexample, machine-checked)
- **Intent:** Backtracking for the overlap state `tfsStart` at network level. If entity `i` is in `tfsStart` after a discrete network step, then before the step it was already in `tfsStart` or it was in `ovWait` (and received `bad`).
- **Failure:** The statement leaves out the `dormant` predecessor. In `SoftwareLanguage.v`, `dormant = chanMNext<vM'>? initN + chanAbort? dormantN + chanBad? tfsStartN`, so `dormant --bad?--> tfsStart`. Thesis §(overlap process), lines ~6517–6524 of `thesis.txt`, lists both `dormant --cBad?--> tfsStart` and `ovWait(m,t,t') --cBad?--> tfsStart`. The statement also has no `reachableNet n` hypothesis, so the overlap component may be an arbitrary process. For example, `chanBad! tfsStart` steps to `tfsStart` by itself, so adding the `dormant` disjunct alone would still not make it true.

  Counterexample, checked in Rocq (`NetAuxBasics.tfsStart_prev_net.cex.v`, lemma `tfsStart_prev_net_cex`; `Print Assumptions` shows only model axioms and stdlib axioms, no admitted lemmas):
  - `n  = [ [|sleeping || dormant || badOvlp, l, h, k|] ]`
  - `n' = [ [|sleeping || tfsStartN || listeningN, l, h, k|] ]`
  - `a  = anTau`. The step is `stepDnTauHead` / `stepDeProcTau` / `stepDpParR` / `stepDpSyncRL`: `dormant` inputs on `chanBad` and `badOvlp` outputs on it.
  - `tfsStartStateNet 0 n'` holds because `tfsStartN $([])$ ~p~ tfsStart` (helper `tfsStart_prev_net_cex_aux1`).
  - `~ tfsStartStateNet 0 n`: `dormant` can input on `abort` but `tfsStart` cannot.
  - `~ exists m t x y, ovWaitStateNet m t x y 0 n`: `dormant` can input `m` on `mNext` but `ovWait m t x y` cannot.
- **Ripple-up:** Only used, in commented-out code, by `NARMisc.tfsStart_tfs_zero` (line 90, label R, `cone=False`). That proof needs the predecessor to be either `tfsStart` (apply the IH) or some state contradicting `tfsStateNet` (use `state_pred_elim_net`). `dormant` contradicts `tfsStateNet` exactly as `ovWait` does, so the fix below does not break it. The lemma is not in the safety cone.
- **Suggested fix:**
  ```coq
  Lemma tfsStart_prev_net i n n' a : reachableNet n -> tfsStartStateNet i n' ->
    n -NA- a -NA> n' -> tfsStartStateNet i n \/ dormantStateNet i n \/
    exists m t x y, ovWaitStateNet m t x y i n.
  ```
  `tfsStart_tfs_zero` has `p : reachableNet n` in scope, so the extra hypothesis costs nothing there.

  Proof idea: use `link_net_ent_disc_bkwd` to get the predecessor entity. If it is unchanged, take the first disjunct. Otherwise get `link_net_prot_reach` and `reachableProt_triple`. With the current, incomplete `overlapState` (only `dormant`/`ovWait`), the conclusion follows directly. With a complete `overlapState`, backtrack the overlap component: only `dormant`, `ovWait` (`bad?`) and `tfsStart` itself (unchanged) reach `tfsStart`.

  Note: without `reachableNet n` (or an `overlapStateNet i n` hypothesis), even the `dormant`-extended statement is false.
- **Partial proof:** none for the original statement, since it is false.

### `NetAuxBasics.ovWait_del_pres_net`

- **Where:** `src/NetAuxBasics.v` line 1026 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:timer-params-not-delay-invariant; missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete, or replace by the parameter-shifting/existential form `ovWaitStateNet m t x y i n -> exists x' y', ovWaitStateNet m t x' y' i n'` (and use the fixed ovWait_del_pres_bkwd_net_strong for the backward direction).

- **Status:** FALSE (in any model where a network with an `ovWait` entity can delay, which is the protocol's normal
  waiting behaviour). The process-level core is Rocq-checked; the network witness is argued below but not mechanised.
- **Intent:** across a network delay, entity `i` stays in the overlap "wait" state.
- **Failure:** `ovWaitState m t x y p := p ~p~ ovWait m t x y`, where
  `ovWait m' t x y = chanAbort? .. $+$ chanBad? .. $+$ $<y>$chanPos<vL>? .. $+$ $<x>$chanPause!switchBcN(m')`.
  `x` and `y` are **countdown timeouts**: a delay `d <= x` turns `$<x>$P` into `$<x-d>$P` (`stepTpDelSub`).
  So a delay by `d` moves the overlap component from the `ovWait m t x y` class to the `ovWait m t (x-d) (y-d)` class.
  These classes are different: the timeout is observable. Rocq-checked (`--explore`; see helper
  `ovWait_del_pres_net_x_obs` in the `.v`):
  ```
  Lemma ovWait_del_pres_net_x_obs (m : Mode) (t x' y y' : Time) :
    x' <> zeroTime -> ~ ProcEquiv.bisimulation (ovWait m t zeroTime y) (ovWait m t x' y').
  ```
  (`ovWait m t 0 y` can do `chanPause *!` now; `ovWait m t x' y'` with `x' <> 0` cannot.)
  Concrete counterexample to (->): take any network `n` with entity `i` in `ovWait m t d y` (`d <= y`) that delays by
  `d` to `n'`. A single-entity network works: `[|nilProc $||$ ovWait m t d y $||$ nilProc, l, h, k|]`. `noSync` holds
  trivially because `ovWait` only uses `chanAbort/chanBad/chanPos/chanPause`, none of which the interface or mode state offers.
  In `n'`, the overlap component is `.. $+$ $<y-d>$.. $+$ $<d-d>$chanPause!..`, which can output on `chanPause`
  immediately. The lemma would also give `ovWaitStateNet m t d y i n'`, so by entity uniqueness and `bisim_trans` an
  `x = 0` instance would be bisimilar to an `x = d > 0` instance. That contradicts `..._x_obs` (with proof irrelevance for
  `d - d = 0`). The (<-) direction fails symmetrically: `ovWait_del_pres_bkwd_net_strong`, which is admitted but
  correct, says the predecessor is `ovWait m t (x+d) (y+d)`.
- **Ripple-up:** not in the safety cone. The only occurrence is inside the **commented-out** old proof of
  `NARMisc.ovWait_nextSince_time` (`Admitted (*R*)`, NARMisc.v:494). That lemma's own sketch says "for the timed
  inductive case, y decreases". So that proof should use `ovWait_del_pres_bkwd_net_strong` (NetAuxBasics.v:471), which
  gives `ovWaitStateNet m t (x +dt+ d) (y +dt+ d) i n`, instead of this lemma.
- **Suggested fix:** delete the lemma, or replace it with the parameter-shifting forms:
  ```
  Lemma ovWait_del_pres_net m t x y i n n' d : n -ND- d -ND> n' ->
    ovWaitStateNet m t x y i n -> exists x' y', ovWaitStateNet m t x' y' i n'.
  ```
  (state shape preserved), and/or the exact backward form that already exists (`ovWait_del_pres_bkwd_net_strong`).
  Both match the intended reading. The exists-form is provable from process-level delay tracking of `ovWait` (each summand idles
  or counts down) plus entity/network delay inversion (`net_del_ent_ex`-style lemmas, NetworkLanguage.v:517ff).
- **Partial proof:** `ovWait_del_pres_net_x_obs` (compiles).

### `NetAuxBasics.del_pres_bkwd_tfsStart`

- **Where:** `src/NetAuxBasics.v` line 1044 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability; incomplete-definition (overlapState)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (only use site tfsStart_tfs_zero has it); proof needs a complete overlapState invariant. Argued, not proved.

- **Status:** FALSE (counterexample, Rocq-verified: the statement implies `Mode -> False`). Also refutes the
  already-*accepted* sibling `NetAuxBasics.del_pres_bkwd_tfsNext`. **Lead: please read the warning below.**
- **Intent:** backward delay preservation. If entity `i` is in `tfsStart` after a network delay, it was already in
  `tfsStart` before (used to show `tfs` time is 0 in `tfsStart`, via urgency).
- **Failure:** there is no reachability hypothesis, and the process language has the timed prefix
  `$< e >$ P` (`stepTpDelSub`: `$<t>$P -d-> $<t-d>$P` for `d <= t`; `stepDpTimeOut`: a zero guard acts like `P`).
  Counterexample (any `m : Mode`, `d = 1`): one-entity network
  `n  = [ [| nilProc $||$ ($< 1 >$ tfsStart) $||$ nilProc, origin, emptyIface, sing m |] ]`
  delays by 1 to
  `n' = [ [| nilProc $||$ ($< 1-1 >$ tfsStart) $||$ nilProc, origin+origin, emptyIface, sing m |] ]`.
  `noSync` holds because during `[0,1)` the guarded term has no discrete action at all (guard nonzero). It
  would block a delay that *passed* the guard, since `sing m` offers `chanMCurr .! m`, which is why the
  guard must land exactly on 0. `$<0>$ tfsStart ~p~ tfsStart` (helper `..._bisimG`, valid for any `Q` that
  only delays to itself), so `tfsStartStateNet 0 n'`. But `$<1>$ tfsStart` cannot do tfsStart's
  `chanMCurr ;? [_]` input, so `~ tfsStartStateNet 0 n`.
  Verified (explore, all `Qed`, only model axioms + proof_irrelevance/funext/reals in `Print Assumptions`), in
  `NetAuxBasics.del_pres_bkwd_tfsStart.cex.v`:
  ```coq
  Lemma del_pres_bkwd_tfsStart_refuted (m : Mode) :
    ~ (forall i n n' d, n -ND- d -ND> n' -> tfsStartStateNet i n' -> tfsStartStateNet i n).
  Lemma del_pres_bkwd_tfsStart_tfsNext_refuted (m : Mode) :
    ~ (forall m0 i n n' d, n -ND- d -ND> n' -> tfsNextStateNet m0 i n' -> tfsNextStateNet m0 i n).
  ```
- **WARNING (consistency):**
  1. `NetAuxBasics.del_pres_bkwd_tfsNext` has an accepted `.ok` (NetAuxBasics-7), but its statement is refuted
     above. Its proof goes through `NetAuxBasics.tfsState_del_pres_net` (Conjecture l.197), which w1b-12 has also
     refuted in Rocq (`tfsState_del_pres_net_refuted (m : Mode)`, in `w1b-12/NetAuxBasics.tfsState_del_pres_net.v`,
     same `$<r>$ Q` trick). Its proof also uses `tfsNext_currModeNet_eq`, which is false in intended models.
     **`tfsState_del_pres_net` should join the known-inconsistent list**, and the `del_pres_bkwd_tfsNext` `.ok`
     should be rejected.
  2. This target and `del_pres_bkwd_tfsNext` are themselves inconsistent with any `m : Mode`. Proofs of later
     NetAuxBasics/NARMisc lemmas that bind a `Mode` and use them must be rejected too.
- **Ripple-up:** `grep`: the only use is NARMisc.v:106, inside the commented-out old proof of
  `NARMisc.tfsStart_tfs_zero` (Admitted `R`). `del_pres_bkwd_tfsNext` likewise (NARMisc.v:123, commented
  `tfsNext_tfs_zero`). `show`: `in_safety_cone=False`. No live dependency breaks.
- **Suggested fix:** add reachability (the only use site, `tfsStart_tfs_zero`, does induction on
  `p : reachableNet n` and has it):
  ```coq
  Lemma del_pres_bkwd_tfsStart i n n' d :
    reachableNet n -> n -ND- d -ND> n' -> tfsStartStateNet i n' -> tfsStartStateNet i n.
  (* and analogously del_pres_bkwd_tfsNext m i n n' d : reachableNet n -> ... *)
  ```
  Why provable: in reachable states the overlap component is (bisimilar to) one of the 13 overlap processes,
  and the only timed prefixes are the `$<x>$`/`$<y>$` guards inside `ovWait`, whose delay-derivatives are
  again `ovWait`. So no reachable overlap state other than `tfsStart` delays into `tfsStart`. The case split
  needs a *complete* overlap-state invariant; note that `ProtAuxDefs.overlapState` is marked
  "INCOMPLETE" (only dormant/ovWait), so `reachableProt_triple` cannot be used as-is. Alternatively, keep the
  statement and add a hypothesis that entity `i`'s overlap component is not a pending timed prefix, which is
  weaker than reachability but ad hoc.
  The same holds for `tfsState_del_pres_net`: it needs `reachableNet n` (and `reachableNet` gives it for `n'` too).
- **Partial proof:** none for the statement (it is false). See `.cex.v` for the refutations.

### `NetAuxBasics.ovReady_wait_track_net`

- **Where:** `src/NetAuxBasics.v` line 1056 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `bisim-state-param-tracking`
- **Fix (audit summary):** Weaken the conclusion to `m = m' /\ y = period m` (all that users need); needs an ovWait parameter-uniqueness lemma.

- **Status:** FALSE. The argument is rigorous but not machine-checked. A checked witness needs a value-congruence bisimulation lemma that the codebase lacks (see the end of this note).
- **Intent:** if entity `i` is `ovReady m t l` in `n` and `ovWait m' t' x y` in `n'` after one discrete step, then the step was the overlap component's `chanOutProc` output. The parameters then match the derivative `ovWaitN [m, t - period m, period m]`, which unfolds to `ovWait m (t-p) (t-p) p`, so `m = m'`, `t' = t - period m`, `x = t'` and `y = period m`.
- **Failure:** state predicates are defined **up to bisimulation**: `ovWaitState m t x y p := p ~p~ ovWait m t x y`. Two facts break the `t'`-conjuncts.
  1. `eSubtract` evaluates with *truncated* subtraction (`evalExpFun (eSubtract ..) = baseNonneg (r1 -nn- r2)`, where `subNonnegTot` returns 0 when `r1 < r2`). So `ovReady m t l` with `t < period m` still outputs and becomes `ovWaitN [m, t (-) period m, period m]`, whose pause timer evaluates to 0.
  2. In `ovWait M T X Y` the parameter `T` is **never observed directly**. It occurs only in the continuation `ovReadyN([M, T, vL])`. `ovReady` only uses it as `eSubtract T (ePeriod M)`, the next pause timer, and never outputs it. So `ovWait m t1 x y ~p~ ovWait m t2 x y` iff `t1 -nn- period m = t2 -nn- period m`, that is, iff `t1 = t2` or both are `<= period m`.

  The proof of 2 is a coinduction over the relation "same overlap-shape, equal `M`, value-equal (`evalExpFunTime`) timers `X`/`Y`, and value-equal `T` up to `-nn- period M`". It covers every transition:
  - The discrete transitions `chanAbort?`, `chanBad?`, `chanPos?` and `chanPause!` lead to identical terms or related shapes.
  - Under delay, `stepTpDelSub`, `stepTpDelAdd` and `stepTpDelIll` fire identically on value-equal timers and produce identical literal timers.

  This gives two counterexamples:
  - **(A) No reachability hypothesis.** Let entity `i` have overlap component exactly `ovReady m zeroTime l`, with `bisim_refl` giving `ovReadyStateNet m 0 l i n`. Its `chanOutProc` output synchronises with the interface (`stepDeIOProcInter` + `stepIntBuffOut`), giving an `anTau` step. The derivative `ovWaitN [m, 0 (-) p, p]` is bisimilar to `ovWait m 0 0 (period m)` by fact 2, so `ovWaitStateNet m 0 0 (period m) i n'` holds. The conclusion `exists pr : period m <= 0, ...` contradicts `period_positive`.
  - **(B) Fails even for reachable networks.** Take any reachable `ovReady m t l` with `period m <= t <= 2*period m`. One exists on every overlap cycle: `init` produces `ovWait m' (W + p) 0`, and successive outputs subtract `p`. The derivative is `ovWait m (t-p) (t-p) p` with `t - p <= p`. By fact 2 it is also `ovWaitState m t'' (t-p) p` for **every** `t'' <= period m`. Choosing `t'' <> t - p` falsifies both `t' = t - period m` and `x = t'`.

  The conjuncts `m = m'` and `y = period m` *are* true. Both parameters are observable: `M` is output on `chanOutProc`/`chanWake`, and `Y` is the `chanPos` timer, observable by delays.
- **Ripple-up:** not in the safety cone. Users:
  - `NARMisc.ovWait_nextSince_time` (lines 473 and 484, admitted `(*R*)`). It needs only `y = period m` to show `period m - y <= t1`.
  - `NARTop.ovWait_sent` (line 133). It needs `m = m'` and `y = period m`.

  No user genuinely needs the `t'` or `x` conjuncts. The same flaw affects the sibling `NetAuxBasics.ovWait_track_net` (line 1063: `t = t'` is false when `t <= period m` and the overlap component does not move, e.g. another entity steps). It probably also affects `NARTop.init_ovWait_track_net` if that one asserts the ovWait `t` parameter. The 2015 proofs used `unique_exps`, which suggests state predicates were then syntactic, not bisimulation-based.
- **Suggested fix:** keep only what is observable (and what the users need):
  ```coq
  Lemma ovReady_wait_track_net m t l i m' t' x y n n' a :
    ovReadyStateNet m t l i n -> ovWaitStateNet m' t' x y i n' ->
    n -NA- a -NA> n' -> m = m' /\ y = period m.
  ```
  If wanted, add `/\ time x = (time t -nn- time (period m))`; it is observable as the pause timer, but the coercions need checking. These conjuncts are true, but proving them still needs a protocol-level parameter-uniqueness lemma:
  ```coq
  Lemma ovWait_params_unique m t x y m' t' x' y' p :
    ovWaitState m t x y p -> ovWaitState m' t' x' y' p ->
    m = m' /\ x = x' /\ y = y'.
  ```
  Proving it means analysing timed transitions of `ovWait` (delay by `y` enables `chanPos?`). Together with the existing admitted `ovReady_ovWait_track_ent` (which gives `m = m'`) and `ovlp_outProc_out`, the corrected net-level lemma then follows by lifting.
  **Alternative (definitional):** make the overlap state predicates syntactic, i.e. equality up to `app`-unfolding and expression evaluation, instead of `~p~`. The original statement with `t'` then becomes provable for reachable networks once `period m <= t` is added as a hypothesis or derived from reachability.
- **Partial proof:** none. The net, entity and process lift is routine (`backtrack_net_pre`-style), but every route ends at the false `t'` conjunct.

### `NetAuxBasics.ovWait_track_net`

- **Where:** `src/NetAuxBasics.v` line 1063 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `bisim-state-param-tracking`
- **Fix (audit summary):** Replace `t = t'` by `(t -nn- period m) = (t' -nn- period m')` (or drop it; no users), or make overlap state predicates syntactic.

- **Status:** FALSE (counterexample by semantic analysis; not machine-checked, see below). The conjunct `t = t'` fails. The other three conjuncts (`m = m'`, `x = x'`, `y = y'`) are believed true but need a parameter-injectivity result for `ovWait` under `~p~` that the codebase lacks.
- **Intent:** if entity `i`'s overlap component is in `ovWait m t x y` before a discrete network step and in `ovWait m' t' x' y'` after it, the overlap component did not move, so all parameters agree.
- **Failure:** `ovWaitState m t x y p := p ~p~ ovWait m t x y` is defined up to strong timed bisimulation. The parameter `t` is never observed directly. In `ovWait`, `t` only flows into `ovReadyN [m', t, vL]`. `ovReady` then continues as `ovWaitN [m', t (-) period m', period m']`, so `t` affects behaviour only through `t -nn- period m`. `subNonnegTot` truncates to `zeroNonneg` when `t < period m`. Hence for `0 <= t, t' < period m`:
  `ovWait m t x y ~p~ ovWait m t' x y`.
  Both terms have the same discrete actions (abort?, bad?, after `y`: `pos<l>?`, after `x`: `pause!`) and the same delays. Every derivative is either syntactically equal on both sides, or differs only in closed expressions that evaluate to the same value: `eSubtract (eBase t) (ePeriod m)` vs `eSubtract (eBase t') (ePeriod m)`, both evaluating to `baseNonneg zeroNonneg`, and their iterates in later rounds. Delay guards are replaced by base values after any delay (`stepTpDelSub`) or fire identically (`stepTpDelAdd`/`stepDpTimeOut` look only at `evalExpFunTime`).
  Concrete counterexample: take `m` any mode, `t := 0`, `t' := period m / 2` (positive by `period_positive`), any `x y`, and the network `n := [ [| sleeping $||$ ovWait m t x y $||$ listening, l, h, k |] ]`. It has a self-loop `n -NA- a -NA> n` given by an out-of-range message (`stepDeIgnore` lifted to the network). Then `ovWaitStateNet m t x y 0 n` holds by `bisim_refl`, and `ovWaitStateNet m t' x y 0 n` holds by the bisimilarity above, but `t <> t'`. This is not an artefact of unreachable states. In the real protocol `init` starts the overlap at `t = waitTime + period` and every round subtracts `period`, so `ovWait` with `t < period m` is reachable.
  **Why not machine-checked:** the bisimilarity needs a coinductive "equal up to closed expressions with equal evaluation" relation. That in turn needs substitution lemmas (`subExp` on closed expressions, `subProcTerm` commuting with the relation) for every `ovWait`/`ovReady` derivative. This is a few hundred lines of metatheory, too much for an unused, non-cone, label-5 lemma.
- **Ripple-up:** `grep -n ovWait_track_net` finds no users. Not in the safety cone, so nothing breaks.
- **Suggested fix:** replace `t = t'` by what bisimilarity actually determines:
  ```coq
  Lemma ovWait_track_net m m' t t' x x' y y' i n n' a :
    ovWaitStateNet m t x y i n -> ovWaitStateNet m' t' x' y' i n' ->
    n -NA- a -NA> n' ->
    m = m' /\ (t -nn- period m) = (t' -nn- period m') /\ x = x' /\ y = y'.
  ```
  The alternative is to drop the `t` conjunct, since nothing uses the lemma. A cleaner long-term option is to make the overlap state predicates syntactic (or up to structural congruence) instead of up to `~p~`, which would also make the many "parameter-tracking" lemmas in this family provable by inversion, as the old `state_pred_elim`-style proofs assumed. The fixed version needs: (1) the overlap component cannot move under `a` while staying `~p~ ovWait` (every `ovWait` derivative, `ovAbort`/`tfsStart`/`ovReady`/`switchBc`, lacks `chanAbort *?`, which `ovWait` always enables; use `bisim_dae`); (2) a lemma `ovWait m t x y ~p~ ovWait m' t' x' y' -> m = m' /\ x = x' /\ y = y' /\ t -nn- period m = t' -nn- period m'`, proved by delaying to the guards and comparing enabled actions and output payloads.
- **Partial proof:** none.

### `NetAuxBasics.ovWait_prev_net`

- **Where:** `src/NetAuxBasics.v` line 1072 · **Lemma** · 2015 label: `#lift-track-net` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (argued via ProtAuxResults.ovWait_prev; caveat: its init branch is stated with initStateProt on the overlap component).

- **Status:** FALSE (counterexample, machine-checked); NEEDS-HYPOTHESIS `reachableNet n`. **The statement implies `Mode -> False`.**
- **Intent:** backward tracking for the overlap state `ovWait(m,t,x,y)` of entity `i` across a discrete network step. Before the step, entity `i` was already in `ovWait(m,t,x,y)`, or in `ovReady(m, t + period m, l)` (the broadcast that decrements `t` by `period m`), or in `init m`.
- **Failure:** this is the same defect w1b-08 found for `ovWait_prev_net_strong`: no reachability hypothesis, and `liftOverlap` does not constrain the other two slots of the software triple. So any process can sit in the overlap slot and step into `ovWait` through a sync with another slot.
  Counterexample (for any `m`, and `t = x = y = 0`): `n = [ [| (chanMCurr ? nilProc) $||$ (chanMCurr ! ovWait m t x y) $||$ nilProc, origin, emptyIface, sing m |] ]`. Slots 1 and 2 synchronise (`stepDpSyncRL`), giving `stepDeProcTau` and then `stepDnTauHead`. Afterwards the overlap slot is literally `ovWait m t x y`. Before, it only offers `chanMCurr ;! []`, and none of `ovWait`, `ovReady` (any parameters) or `init` can do that. So all three disjuncts fail.
  Checked in Rocq (`--explore`, HELPERS of `NetAuxBasics.ovWait_prev_net.v`, adapted from `work/w1b-08/NetAuxBasics.ovWait_prev_net_strong.cex.v`):
  - `ovWpn_cex m t x y : exists n n' a, ovWaitStateNet m t x y 0 n' /\ n -NA- a -NA> n' /\ ~(ovWait \/ (exists t0 l0, ovReady m t0 l0) \/ init)`
  - `ovWpn_refuted : (exact target statement) -> Mode -> False`
  `Print Assumptions ovWpn_refuted` shows only ComhBasics model axioms, proof irrelevance, functional extensionality and the stdlib classical-reals axioms. No admitted lemma is used.
- **Ripple-up:** not in the safety cone. The only textual user is `NARMisc.v:478`, inside a **commented-out** old proof (that lemma ends `Admitted (*R*)`). That proof is an induction on `nextSince`/reachability, so reachability is available at the call site. Nothing that currently compiles depends on it.
- **Suggested fix:** add reachability of the source network, as for its siblings (`ovWait_prev_net_strong`, `ovReady_prev_net_strong`, `ovReady_prev_net`; see w1b-08's note):
  ```coq
  Lemma ovWait_prev_net m t x y i n n' a : reachableNet n ->
    ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
    ovWaitStateNet m t x y i n \/
    (exists l, ovReadyStateNet m (t +t+ period m) l i n) \/
    initStateNet m i n.
  ```
  Proof plan. `link_net_ent_disc_bkwd` gives the entity at `i`. `reachable_net_prot`/`reachableProt_triple` give a `protocolState` triple with an `overlapState` middle slot. Then invert the entity step and the `parComp` step. If the overlap slot is unchanged, use disjunct 1. If it moved (alone or in a sync), the Qed process-level `ProtAuxResults.ovWait_prev` gives `ovReadyState m (t + period m) l` or its init branch.
  Caveats:
  1. As w1b-08 notes, `ovWait_prev`'s init branch is stated as `initStateProt m p` about the overlap *component*. It should probably be `initState m p`.
  2. `eSubtract` evaluates through the truncated `-nn-`. A literal `ovReady m t0 l` with `t0 < period m` steps to an `ovWait` with `t = 0`, and `t0 <> 0 + period m`. Whether the `t + period m` disjunct survives this depends on `ovReady m t0 l ~p~ ovReady m (period m) l` for all `t0 <= period m`, which is plausible since only the evaluated value `t0 -nn- period m = 0` is observable. `ovWait_prev` is Qed, so it presumably already handles this.
- **Partial proof:** none of the target (it is false as stated). See the counterexample in HELPERS.

## NARMisc

### `NARMisc.switchBc_nextMode_net`

- **Where:** `src/NARMisc.v` line 50 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n (every caller has it in scope); provable once nextModeEnt is defined, plus a net-level switchBc_prev lift.

- **Status:** NEEDS-HYPOTHESIS (`reachableNet n`). The statement as written is refutable from the admitted interface lemmas that agree with the intended definition of the stub; the refutation was checked in Rocq.
- **Intent:** In a reachable network, an entity whose overlap component is in `switchBc m` is mid-transition to `m`, so `nextModeNet m i n`.
- **Failure:** `switchBcStateNet m i n -> nextModeNet m i n` has no reachability premise. `switchBcStateNet` only constrains the software component, so take the unreachable one-entity network
  `n := [ [| nilProc $||$ switchBc m $||$ nilProc, mkPosition 0 0, h, sing m0 |] ]`.
  Here `switchBcStateNet m 0 n` holds (by `bisim_refl`). But `nextMode_ent_ex` and `nextMode_ent_mState` together force `nextModeMState (sing m0) = Some m`, and the left side computes to `None`. Both lemmas hold under the intended stub definition (`nextModeEnt m e` iff the mode state of `e` is `<|_, m, _|>`). Checked in Rocq (`--explore`). `Print Assumptions` lists only `nextMode_ent_ex`, `nextMode_ent_mState`, the stub parameters and model axioms:
  ```coq
  Lemma switchBc_nextMode_net_refute (m m0 : Mode) (h : Interface) :
    (forall m i n, switchBcStateNet m i n -> nextModeNet m i n) -> False.
  Proof.
    intro H.
    set (e := [| nilProc $||$ switchBc m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
    assert (switchBcStateNet m 0 [e]) as IS.
    { econstructor; [ | apply einConsLeft]. constructor. constructor.
      apply ComhCoq.ProcEquiv.bisim_refl. }
    apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
    inversion EIN; subst. unfold e in NM.
    apply nextMode_ent_mState in NM. simpl in NM. discriminate.
  Qed.
  ```
- **Ripple-up:** **In the safety cone.**
  - `NARMisc.nextSince_next` (line 185) uses it as `eapply switchBc_nextMode_net. replace m with x. eassumption. ...`. Here `p : reachableNet n` is in scope, so adding the hypothesis costs one extra subgoal: `eapply switchBc_nextMode_net; [exact p | ]`.
  - My accepted `NARMisc.nextSince_ovWait_modeEq`, in its helper `nextSince_ovWait_modeEq_next`, calls it as `eapply switchBc_nextMode_net; eassumption`. A `reachableNet n0'` hypothesis is in context at that point, so the call keeps working after the fix unchanged.
  - Any proof of `nextSince_switchBc_modeEq` (owned by steal-6) probably calls it too. `p : reachableNet n` is available there.

  Nothing above the cone breaks if the hypothesis is added, because every caller has reachability in scope.
- **Suggested fix:**
  ```coq
  Lemma switchBc_nextMode_net m i n :
    reachableNet n -> switchBcStateNet m i n -> nextModeNet m i n.
  ```
  Proof plan once `nextModeEnt` is defined: induction on `reachableNet`.
  - Base case: contradiction via `initNet_contra`.
  - Discrete step: backtracking shows the previous state was `switchBc m` (IH) or `ovWait m t 0 y` (`ProtAuxResults.switchBc_prev`, lifted to the network). In the second case `ovWaitState_nextMode_net` gives `nextModeNet m i n`, and `nextMode_pres_fwd_net` carries it forward (neither `ovWait` nor `switchBc` is in its excluded set).
  - Delay step: `switchBc` is urgent (`switchBc_urgent`), or use backward delay preservation together with `nextModeNet_del_pres`.

  A net-level `switchBc_prev_net` lift does not exist yet and would be needed.
- **Related finding (admitted interface is inconsistent):** In `EntAuxResults.nextModeEnt_not_stable m1 m2 p l h : nextModeEnt m1 ([|p, l, h, m2|]) -> False`, Rocq infers `m2 : ModeState` (confirmed with `About`), not `m2 : Mode`. So the lemma says `nextModeEnt` never holds for any entity. It contradicts `EntAuxResults.tfsCurr_failSafe`, which has no reachability premise: in a `--explore` check, `tfsCurr_failSafe` and `nextModeEnt_not_stable` together prove `Mode -> Interface -> False`, using the witness entity `[| nilProc $||$ tfsCurr $||$ nilProc, mkPosition 0 0, h, sing m |]`. Fix: annotate `(m2 : Mode)` so the mode state is the stable `sing m2`. `tfsCurr_failSafe` is also false on unreachable entities and needs `reachableEnt e`. My proofs do not use either lemma.

### `NARMisc.switchCurr_nextSince_nextMode_net`

- **Where:** `src/NARMisc.v` line 53 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define nextModeEnt/nextModeNet (lift of nextModeMState) and prove nextMode_pres_fwd_nextSince_net (reachable, nextSince on both sides).

- **Status:** BLOCKED-ON-STUB (`nextModeNet` / `nextModeEnt`). Reduced, and checked in `--explore`, to exactly one missing preservation lemma, which is true under the intended stub definition.
- **Intent:** if entity `i` is `nextSince m` and its overlap component is in `switchCurr` (about to output on `mCurr`), then its mode state still has next mode `m`, i.e. it is `<|m0, m, d|>`.
- **Failure:** The natural proof is induction on `nextSince`. It proves the stronger `nextSince m t i n p -> nextModeNet m i n`, and the `switchCurr` hypothesis is never used.
  - Base: `ovWaitStateNet m t' x y i n'`, so `ovWaitState_nextMode_net` (with reachability `reachNetDisc n n' a p w`) closes it.
  - Delay: `nextModeNet_del_pres` and the IH close it.
  - Discrete step `n -NA- a -NA> n'`, with the IH `nextModeNet m i n` and `nextSinceStateNet i n'`: we must carry `nextModeNet` across the step. The only forward-preservation lemma is `nextMode_pres_fwd_net`, and it requires `~(switchCurrStateNet i n \/ ovAbortStateNet i n \/ tfsCurrStateNet i n)`. In the case `switchCurrStateNet i n` (overlap stays `switchCurr`, since `switchCurr := chanMCurr!switchListen` and `switchListen` is not a `nextSinceState`), the broadcast or listener component, the interface, or another entity can still move. No visible lemma then relates `nextModeNet m i n` to `nextModeNet m i n'`. With `nextModeEnt` opaque, even `nextMode_ent_ex` cannot move from `[|p,l,h,k|]` to `[|p',l',h',k|]`.
  - Going backwards does not help either: every visible lemma that concludes `nextModeNet` is either state-specific (init/ovWait/ovReady/switchBc) or a preservation lemma that excludes `switchCurr`.
- **Caveat (not used):** the visible context is actually inconsistent. `NARMisc.init_nextMode_net` (no `reachableNet` hypothesis) is refuted from `nextMode_ent_ex` + `nextMode_ent_mState`; see `work/NARMisc-1/NARMisc.init_nextMode_net.v`. A vacuous ex-falso proof would therefore type-check. I deliberately did not submit one.
- **Ripple-up:** in the safety cone. Its only user is `NARMisc.nextSince_next` (case 4). That in turn feeds `currSince_curr` (NARMisc:260), `NARIncomp` line 276, and `NARInsuff` lines 342 and 467.
- **Suggested fix:** add to `NetAuxBasics.v`, next to `nextMode_pres_fwd_net`:
  ```coq
  Lemma nextMode_pres_fwd_nextSince_net m i n n' a :
    reachableNet n -> nextModeNet m i n -> nextSinceStateNet i n ->
    nextSinceStateNet i n' -> n -NA- a -NA> n' -> nextModeNet m i n'.
  ```
  (A narrower version that adds the hypothesis `switchCurrStateNet i n` is enough if one also proves that `nextSinceStateNet` is disjoint from `ovAbort` and `tfsCurr`. Those cases then go through `nextMode_pres_fwd_net`.)
  - Why it is true under the intended definition `nextModeNet m i n := exists e, e @ i .: n /\ nextModeEnt m e`, with `nextModeEnt m [|p,l,h,k|] := nextModeMState k = Some m`: in a `nextSinceState` the mode state is a `transState`. It changes only by
    - `stepMsSwitch` (`mCurr @?`, partner is the overlap output `switchCurr -> switchListen`, which leaves `nextSinceState`),
    - `stepMsAbort` (`mStable @?`, partner `ovAbort` or `tfsNext`, which are not `nextSinceState`s),
    - `stepMsInit`, which only applies to a stable mode state.
    The output rules and delay keep `nextModeMState` unchanged.
  - Better still, define the stub as above and prove `nextModeNet` preservation in general for steps whose mode-state action is not `mCurr @?` or `mStable @?`.
- **Partial proof (compiles in --explore, only the missing lemma admitted):** `work/steal-5/NARMisc.switchCurr_nextSince_nextMode_net.v`
  ```coq
  Proof.
    intros NS _. induction NS.
    - eapply ovWaitState_nextMode_net; [exact (reachNetDisc n n' a p w) | eassumption].
    - eapply switchCurr_nextSince_nextMode_net_pres; [exact p | exact IHNS | | exact H | exact w].
      eapply switchCurr_nextSince_nextMode_net_rel_state; eassumption.
    - eapply nextModeNet_del_pres; eassumption.
  Qed.
  ```
  Here `..._rel_state` is a local copy of `nextSince_rel_state`, which is later in the file. `..._pres` is the missing lemma above. With both in place the same script also proves `nextSince_next` outright. Then `switchCurr_nextSince_nextMode_net` could be reordered or derived from it.

### `NARMisc.outgoing_timeout_disc`

- **Where:** `src/NARMisc.v` line 389 · **Theorem** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:message-position-universally-quantified` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Move l into the existential (exists r l, delivered ...); fully proved with model axioms only (outgoing_timeout_disc_fixed); sent_out_del needs a one-line change.

- **Status:** FALSE (counterexample, machine-checked; no admitted lemmas used)
- **Intent:** if entity `i` has payload `v` timed out (stamp 0) in its output queue and the network makes a discrete step, then either `v` is still outgoing with stamp 0, or this step was `i` broadcasting `v`. In the second case `v` was delivered 0 time units ago, from `i`'s own position, to some radius `r`.

- **Failure:** the message position `l : Position` is a **universally quantified parameter** of the theorem. The conclusion asks for `delivered ([-v, l, r-]) …` for *every* `l`. A broadcast always carries the sender's position (`stepDeOut`: `[|p,l,i,k|] -EA- [-v, l, r-]#! ->> …`), and positions do not change on discrete steps. So for any `l` other than entity `i`'s position, the right disjunct can hold only by a stamp-0 delivery of `[-v,l,r-]`, which is impossible.
  Concrete counterexample (for any `m0 : Mode`):
  - Let `e0 := [|procProtocol, (0,0), {li=[]; lo=[<([],0)>]; ln=[]}, sing (failSafeSucc m0)|]`. Then `n := [e0]` is initial (`initialEnt` leaves the interface unconstrained) and so reachable via `p := reachNetInit`.
  - Let `w : [e0] -NA- anOut [-[], (0,0), r-] 0 -NA> [e1]`, where `e1` has an empty output list (`stepDnOutHead`/`stepDeOut`/`stepIntFwdOut`/`stepTlFwdHd`/`stepNlBuff`).
  - Take `v = []`, `i = 0`, `l = (1,0)`. The hypothesis `outgoing [] 0 0 [e0]` holds. The left disjunct fails because `e1`'s output list is empty. The right disjunct fails too: inverting `delivered` on `reachNetDisc … p w` forces either `anOut [-[],(0,0),r-] 0 = anOut [-[],(1,0),r'-] 0`, so `0 = 1`, or a delivery on `reachNetInit`, which has no constructor.

  Verified as `outgoing_timeout_disc_cex : forall m0 : Mode, ~ (<statement universally closed>)` in `NARMisc.outgoing_timeout_disc.v` (HELPERS section, explore check passes). `Print Assumptions` shows only model axioms (`Mode`, `failSafeSucc`, `failSafeSuccFS`, …) and stdlib reals/classical axioms. **No admitted lemma is used.**
- **Ripple-up:** in the safety cone. The only user is `NARMsgPosition.sent_out_del` (line 128, discrete case), which is used by `sent_delivered`, which is used by `NARMsgPosition` line 287 and `NARTop` line 558. `sent_out_del`'s statement is already `exists r l, delivered …`. Its proof gets `l` from inverting `outgoing` and lets `lets` unify the free `l`, so it only *needs* the corrected form below. Nothing up the chain breaks once the statement is fixed.
- **Suggested fix (A, minimal; recommended):** move `l` into the existential, matching `sent_out_del`'s shape:
  ```coq
  Theorem outgoing_timeout_disc (n n' : Network) (a : ActDiscNet) (i : nat)
    (p : reachableNet n) (w : n -NA- a -NA> n') (v : list BaseType) :
    outgoing v zeroTime i n ->
    outgoing v zeroTime i n' \/
    exists r l, delivered ([-v, l, r-]) zeroTime i n' (reachNetDisc n n' a p w).
  ```
  **Fully proved** as `outgoing_timeout_disc_fixed`, with `Print Assumptions` showing only model and stdlib axioms. No admitted lemma is used: the proof doesn't even need `link_net_ent_disc_fwd`, because I prove a small forward-existence lemma instead. In `sent_out_del`, replace `ex_flat. right. exists x. exists l. eassumption.` with `ex_flat. right. do 2 eexists. eassumption.` or similar. The discrete step it needs is checked as `outgoing_timeout_disc_user_step`.
  **Alternative (B, stronger):** keep `(l : Position)` but add the hypothesis `inPosNet l i n ->` before `outgoing …`. Also fully proved, as `outgoing_timeout_disc_fixedB`.
- **Partial proof:** the complete development is in `NARMisc.outgoing_timeout_disc.v`, about 150 lines of HELPERS, all `outgoing_timeout_disc_`-prefixed:
  - `_tl_out`: a timed-list output removes only `<(u,0)>`.
  - `_ent_out` and `_ent_nonout`: entity-level output-list preservation.
  - `_mk`: rebuilds `outgoing`.
  - `_fwd`: forward existence of entity `i` across a discrete network step.
  - `_core`: the step is either preserving or `a = anOut [-v, posEnt e, r-] i`.
  - `_fixed`, `_fixedB`, `_user_step`.

  To splice fix A after approval: paste the helpers before the theorem, change the statement as above, and use the body of `outgoing_timeout_disc_fixed` as the proof.

### `NARMisc.notifBadPathNet_urgent`

- **Where:** `src/NARMisc.v` line 412 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n; caller insuff_react has p in scope (fixed proof compiles relative to reachable_net_ent, reachableEnt stub, del_listening).

- **Status:** FALSE (counterexample) — needs `reachableNet n`
- **Intent:** a network in which entity `i` is on the "notify bad" path (listener in `rangeBad` with the current mode, or in `badOvlp`) cannot delay: those states are urgent.
- **Failure:** the statement has no reachability hypothesis (its sibling `notifAbortPathNet_urgent`, directly above it, does have `reachableNet n`). The `rangeBad` case is urgent without reachability (the mode state can always serve `mCurr`). The `badOvlp` case is not: the `bad!` output only blocks delay when something in the entity can synchronise with it. That holds for the real protocol's sender and switch handler in reachable states, but not for arbitrary process terms.
  Counterexample, verified in Rocq via `--explore` and closed under the model axioms only (no admitted lemmas). For any `m : Mode` and any `d`, take the one-entity network `[ [| nilProc $||$ nilProc $||$ badOvlp, origin, mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ]`. Then `notifBadPathNet 0` holds (by `nbpBad` and `bisim_refl`). It also delays by `d` to itself: `badOvlp`'s `bad!` has no partner, so `noSyncNow` holds trivially, and the empty interface and `sing m` delay. Hence `notifBadPathNet_urgent_refuted : forall (m:Mode) (d:Delay), ~ (forall i n n' d, notifBadPathNet i n -> n -ND- d -ND> n' -> False)`. The statement is therefore false whenever `Mode` is inhabited.
- **Ripple-up:** in the safety cone. The only user is `NARInsuff.insuff_react` (NARInsuff.v:634, `contradiction (notifBadPathNet_urgent i n n' d H7 w)`). That proof has `p : reachableNet n` in scope, so the fix costs one extra argument there: `notifBadPathNet_urgent i n n' d p H7 w`.
- **Suggested fix:**
  ```coq
  Lemma notifBadPathNet_urgent i n n' d :
    reachableNet n -> notifBadPathNet i n -> n -ND- d -ND> n' -> False.
  ```
  This is proved in my file as `notifBadPathNet_urgent_fixed`. It compiles, and its assumptions are the model axioms plus `reachable_net_ent`, the `reachableEnt` stub and the admitted `EntAuxResults.del_listening`. It is not in the blacklist. The proof goes through `del_net_ent` to get an entity-level delay, then splits on the two `notifBadPathEnt` cases. In the `rangeBad` case, `chanMCurr ;? [baseMode (currModeMState k)]` is enabled in both the listener and the mode state, which contradicts `noSyncNow`. In the `badOvlp` case, `del_listening` gives `listeningStateEnt e`, and `bisim_dae` on `bad!` (enabled in `badOvlp`) against `listening` yields a `listening` transition on `bad!`, which inversion refutes.
- **Partial proof:** `(prover work area; evidence for audited targets is in `2026-10-14-proof-completion-pass-1-evidence/audit/`) NARMisc.notifBadPathNet_urgent.v` holds the counterexample (`notifBadPathNet_urgent_cex`, `notifBadPathNet_urgent_refuted`) and the fixed proof (`notifBadPathNet_urgent_fixed`). The counterexample is due to an earlier attempt by NARMisc-2. I re-verified it here and made the fixed proof self-contained.

### `NARMisc.bcWait_bktrk_net`

- **Where:** `src/NARMisc.v` line 507 · **Lemma** · 2015 label: `4` · **in safety cone:** yes
- **Audit:** FALSE-ARGUED · root cause: `other:sent-on-wrong-network + missing chanWake predecessor case`
- **Fix (audit summary):** Name the step w, put sent on n' with reachNetDisc n n' a p w, and weaken the wake-up disjunct to x = zeroTime; NARTop.bcWait_sent adapts with a simpler script.

- **Status:** FALSE (counterexample, on paper; two independent defects). Not refutable inside Rocq as-is only because `Mode` is an abstract axiom type with no inhabitant/inequality axiom and building a reachable trace needs the whole semantics.
- **Intent:** back-tracking for the broadcast component. If entity `i` is in `bcWait m x` after a discrete step `n -a-> n'`, then before the step it was already `bcWait m x`, or it just woke up (`x = 0`), or it was `bcReady m l` and the step was the broadcast of `[m, l]` (so `x = period m` and the message has just been *sent*).

- **Failure 1 (wrong network in `sent`).** The third disjunct asks for
  `sent [baseMode m, basePosition l] zeroTime i n p`, i.e. sent *in the source network `n`* with history `p`.
  But the `bcReady m l -> bcWait m (period m)` step is itself the output on `chanOutProc` (software `!` synchronised with the interface `?`, an `anTau` network step). `sentBase` therefore yields
  `sent [..] zeroTime i n' (reachNetDisc n n' anTau p w)`: the message is sent in `n'`, not in `n`.
  `sent .. i n p` would need an *earlier* send of exactly `[m,l]` at the same instant, which in general does not exist.
  Counterexample: any reachable trace in which entity `i` enters `bcReady m l` and fires it while no earlier zero-time-ago send of `[m,l]` is recorded in `p`. For example, take the first broadcast after the `switchBc m` wake-up, with the overlap component's last `ovReady` output not at the same instant. Before the step, `bcWait m (period m)` and `sleeping` both fail at `n`, because the component is `bcReady m l`, which is not bisimilar to either: `bcReady` can only output on `chanOutProc`.
  
- **Failure 2 (missing predecessor case).** `bcWait m' x' := chanTrans? sleepingN + <x'>chanPos<vL>? bcReadyN(..) + chanWake<vM>? bcWaitN([vM, 0])`. So `bcWait m' x'` steps on `chanWake ? [m]` (synchronising with the overlap's `switchBc m = chanWake<m>!`) to `bcWait m 0`. This is the normal mode switch while broadcasting in the old mode `m'`: the overlap goes `dormant -> init m -> ovWait m .. -> switchBc m`, while the broadcast component sits in `bcWait m' x'`.
  Then `bcWaitStateNet m 0 i n'` holds, but at `n`:
  - `bcWaitStateNet m 0 i n` is false when `m' <> m` (the mode is observable through the later `chanOutProc [m,_]` output) or when `x' > 0` (`chanPos` is not yet enabled);
  - it is not `sleeping`;
  - it is not `bcReady`.
  
  None of the three disjuncts holds.

- **Ripple-up:** used only in `NARTop.bcWait_sent` (NARTop.v:314), which is in the safety cone (`currSince_periodic_sent` -> ... -> `safety`). There it is used in the discrete case of an induction on `p`. W2 (`x = 0`) is discharged by `0 < x`, and W3 is turned into `sent .. i n' (reachNetDisc ..)` with `constructor` (= `sentDisc`) applied to the bogus `sent .. i n p`. With the fix below, `bcWait_sent` goes through with a *simpler* script, because the base `sent` is delivered directly.

- **Suggested fix:** name the step `w`, put `sent` on `n'`, and weaken the wake-up disjunct to `x = zeroTime`. `x = zeroTime` covers wake-up from both `sleeping` and `bcWait m' x'`, and it is all `bcWait_sent` needs.
  ```coq
  Lemma bcWait_bktrk_net (n n' : Network) (m : Mode) (x : Time)
    (i : nat) (a : ActDiscNet) (p : reachableNet n) (w : n -NA- a -NA> n') :
    bcWaitStateNet m x i n' ->
    bcWaitStateNet m x i n \/ x = zeroTime \/
    (exists l, bcReadyStateNet m l i n /\ x = period m /\
    sent [baseMode m, basePosition l] zeroTime i n' (reachNetDisc n n' a p w)).
  ```
  If the sleeping/bcWait information is wanted, the second disjunct can instead be
  `((sleepingStateNet i n \/ exists m' x', bcWaitStateNet m' x' i n) /\ x = zeroTime)`.
  Corresponding change in `NARTop.bcWait_sent` (discrete case):
  ```coq
  lets BB : bcWait_bktrk_net p s H. decompOr3 BB W1 W2 W3.
  apply IHp in W1. decompEx2 W1 l q V. exists l q. constructor. assumption.
  contradiction (Q W2). invertClearAs2 W3 l L.
  andflat Y. rewrite <- Y1. exists l (Rle_refl x). my_applys_eq Y2. timering.
  ```
  Why the fixed version should be provable: lift a protocol-level back-tracking lemma for the broadcast component, which is missing today; it should be provable with `backtrack_weed`, like `ovWait_prev`:
  ```coq
  p -PA- a -PA> p' -> broadcastState p -> bcWaitState m x p' ->
    bcWaitState m x p \/ x = zeroTime \/
    exists l, bcReadyState m l p /\ x = period m /\ a = chanOutProc ;! [baseMode m, basePosition l].
  ```
  The lemma is: the component either did not move, or it moved by `chanWake?` (from `sleeping` or `bcWait`, giving `x = 0`), or by the `bcReady` output. In the output case, `link_ent_soft_disc`/`procNeq_tau_net` give `a = anTau` plus the interface input on `chanOutProc`, which are exactly the premises of `sentBase`.

- **Partial proof:** none. The statement is false, so no script was attempted.

### `NARMisc.rangeBad_notifBad_net`

- **Where:** `src/NARMisc.v` line 541 · **Lemma** · 2015 label: `#notifBadNetLift #complexNetLift` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `other:missing-currModeNet-hypothesis`
- **Fix (audit summary):** Add currModeNet m i n (proved relative to Conjecture currMode_ent_ex); the single caller notifBad_pres_tfs already has it, same tactic closes it.

- **Status:** NEEDS-HYPOTHESIS (`currModeNet m i n`). The statement is false in every model where `Mode` has two distinct elements. It is not refutable in Rocq without such an assumption, because `Mode` is an abstract axiom type.
- **Intent:** an entity whose listener component is in `rangeBad m` is on the notification-bad path.

- **Failure:** `notifBadPathEnt` has two constructors:
  - `nbpRng p l h k m : rangeBadStateProt m p -> currModeMState k = m -> notifBadPathEnt [|p,l,h,k|]`
  - `nbpBad .. : badOvlpStateProt p -> ..`

  `rangeBad m''` is the listener state that has just received a *foreign* mode `m''` with insufficient range, and is about to read its *own* current mode on `chanMCurr`. It then goes to `badOvlp` only if the two modes are equal (`currEq`). The bad path (`nbpRng`) therefore additionally requires that our current mode is `m`.
  The hypothesis `rangeBadStateNet m i n` says nothing about the mode state `k`. After unfolding (`destruct R as [e E1 E2]; inversion E1; subst; econstructor; [|apply E2]; eapply nbpRng; exact P`), the residual goal is exactly
  ```
  P : rangeBadStateProt m p
  E2 : [|p, l, h, k|] @ i .: n
  ============================
  currModeMState k = m
  ```
  This was verified with `--explore`. Nothing relates `k` to `m`, not even under reachability: the received foreign mode `m''` is arbitrary.
  Counterexample (paper): `n = [ [| q1 $||$ q2 $||$ rangeBad m1, l, h, sing m2 |] ]` with `m1 <> m2`.
  - `rangeBadStateNet m1 0 n` holds via `bisim_refl`.
  - `nbpRng` would need `rangeBad m1 ~p~ rangeBad m2`. That bisimilarity fails: after the input `chanMCurr?[m2]`, the right side reaches `currEq m2 m2`, which can do `chanBad!`; the left side reaches `currEq m2 m1`, which cannot.
  - `nbpBad` would need `rangeBad m1 ~p~ badOvlp`, which fails on `chanBad!`.
  
  Even in reachable networks the situation arises: another entity's message in mode `m1 ≠` our mode, with insufficient range.

- **Ripple-up:** single user `NARInsuff.notifBad_pres_tfs` (NARInsuff.v:407), in the safety cone. The call site is
  `lets RNN : rangeBad_next_net w OR CMN. left. or_flat. eapply rangeBad_notifBad_net; eassumption.`
  The goal is `notifBadPathNet i n'`, with `rangeBadStateNet m i n'` (from `RNN`) and `U0 : currModeNet m i n'` in context. So the strengthened lemma below is a drop-in replacement: the *same* tactic `eapply rangeBad_notifBad_net; eassumption` closes it.
- **Suggested fix:**
  ```coq
  Lemma rangeBad_notifBad_net m i n :
    rangeBadStateNet m i n -> currModeNet m i n -> notifBadPathNet i n.
  Proof.
    intros R C. destruct R as [e E1 E2]. apply currMode_ent_ex in C.
    destruct C as [e' [E2' CM]].
    assert (e' = e) by (eapply entInNetUnique; eassumption). subst e'.
    inversion E1 as [p l h k P]; subst.
    econstructor; [ | apply E2]. eapply nbpRng. exact P. reflexivity.
  Qed.
  ```
  This exact proof compiles in place, checked as a helper `rangeBad_notifBad_net_fixed` via `check --explore`. It uses only the existing conjecture `currMode_ent_ex` about the `currModeNet` stub. It is the mirror image of the already-proved `notifBadPathNet_cases`.
- **Partial proof:** see `NARMisc.rangeBad_notifBad_net.v` (helper `rangeBad_notifBad_net_fixed` = proof of the fixed statement).

### `NARMisc.init_nextMode_net`

- **Where:** `src/NARMisc.v` line 41 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete (duplicate of NetAuxBasics.init_nextMode_net, no users) or add reachableNet n.

- **Status:** NEEDS-HYPOTHESIS (`reachableNet n`). The statement as written is refutable from the admitted interface lemmas that agree with the intended definition of the stub; the refutation was checked in Rocq.
- **Intent:** In a reachable network, an entity whose overlap component is in `init m` already has `m` as the next mode in its mode state, so `nextModeNet m i n`.
- **Failure:** The statement `initStateNet m i n -> nextModeNet m i n` does not assume `reachableNet n`. `initStateNet` only constrains the software component, so take an unreachable one-entity network whose mode state is stable:
  `n := [ [| nilProc $||$ init m $||$ nilProc, mkPosition 0 0, h, sing m0 |] ]`.
  Then `initStateNet m 0 n` holds (by `bisim_refl`). However:
  - `nextMode_ent_ex` turns `nextModeNet m 0 n` into `nextModeEnt m e` for that entity.
  - `nextMode_ent_mState` turns that into `nextModeMState (sing m0) = Some m`.
  - `nextModeMState (sing m0)` computes to `None`, so `None = Some m` is a contradiction.

  Both interface lemmas hold under the intended stub definition (`nextModeEnt m e` iff the mode state of `e` is `<|_, m, _|>`), so the statement is false under that definition. Checked in Rocq (`--explore`). `Print Assumptions` lists only `nextMode_ent_ex`, `nextMode_ent_mState`, the `nextModeNet`/`nextModeEnt` parameters and model axioms:
  ```coq
  Lemma init_nextMode_net_refute (m m0 : Mode) (h : Interface) :
    (forall m i n, initStateNet m i n -> nextModeNet m i n) -> False.
  Proof.
    intro H.
    set (e := [| nilProc $||$ init m $||$ nilProc, mkPosition 0 0, h, sing m0 |]).
    assert (initStateNet m 0 [e]) as IS.
    { econstructor; [ | apply einConsLeft]. constructor. constructor.
      apply ComhCoq.ProcEquiv.bisim_refl. }
    apply H in IS. apply nextMode_ent_ex in IS. destruct IS as [e' [EIN NM]].
    inversion EIN; subst. unfold e in NM.
    apply nextMode_ent_mState in NM. simpl in NM. discriminate.
  Qed.
  ```
- **Ripple-up:** None. `grep` shows no user of `NARMisc.init_nextMode_net`. The only `init_nextMode_net` that is used is `NetAuxBasics.init_nextMode_net`, inside the commented-out proof of `NetAuxBasics.ovWait_ovReady_nextMode_net`, and that one already has `reachableNet n`. Not in the safety cone.
- **Suggested fix:** This lemma duplicates `NetAuxBasics.init_nextMode_net` without its hypothesis. Either delete it, or restate it as
  ```coq
  Lemma init_nextMode_net m i n :
    reachableNet n -> initStateNet m i n -> nextModeNet m i n.
  ```
  which is then proved by `exact (ComhCoq.NetAuxBasics.init_nextMode_net m i n)`. That version is itself admitted (label 7). It becomes provable once `nextModeEnt` is defined: the previous step is a `dormant -(mNext? m)-> init m` transition, which synchronises with the mode state outputting its next mode `m`.

### `NARMisc.msgBadPathNet_urgent`

- **Where:** `src/NARMisc.v` line 418 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableNet n (proved relative to reachable_net_ent, reachableEnt stub and admitted EntAuxResults.del_listening; write-up warns del_listening may be false in the gotMsg case because position reads are not urgent).

- **Status:** FALSE (counterexample). It needs `reachableNet n`, and it is false whenever `Mode` is inhabited.
- **Intent:** if entity `i` of a network is on the "message bad" path (listener in `gotMsg`/`gotRange` with a possibly-incompatible received mode, or in `badOvlp`), the network cannot delay: those states are urgent.
- **Failure:** the statement has no reachability hypothesis. Its siblings `msgAbortPathNet_urgent` and `notifAbortPathNet_urgent` both carry `reachableNet n`. In the `badOvlp` case the `bad!` output only blocks delay if some component of the same entity can take it, and an arbitrary process term need not have one.
  Counterexample, verified in Rocq (`--explore`; it uses only the model axioms and stdlib, no admitted lemmas). For any `m : Mode` and `d : Delay`, take
  `[ [| nilProc $||$ nilProc $||$ badOvlp, origin, mkInterface (mkInputList []) (mkOutputList []) (mkNotifList []), sing m |] ]`.
  Then `msgBadPathNet 0` holds via `mbpBad` and `bisim_refl`. The network also delays by `d`: the only enabled action is `chanBad *!`, whose complement neither the interface nor the mode state can do, so `noSync` holds; the process delays to itself, the empty interface lists delay, and `sing m` delays. The file proves
  `msgBadPathNet_urgent_refute : (forall n n' d i, msgBadPathNet i n -> n -ND- d -ND> n' -> False) -> Mode -> False`.
  This is the same flaw that w1b-01 found in `notifBadPathNet_urgent` (same `badOvlp` witness).
- **Ripple-up:** the only use is `NARIncomp.incomp_tfs` (NARIncomp.v:553), inside a commented-out old proof (`*) Admitted.`). That context has `p : reachableNet n`, so the fixed statement would serve it with one extra argument. Not in the safety cone.
- **Suggested fix:**
  ```coq
  Lemma msgBadPathNet_urgent (n n' : Network) (d : Delay) (i : nat) :
    reachableNet n -> msgBadPathNet i n -> n -ND- d -ND> n' -> False.
  ```
  This is proved in my file as `msgBadPathNet_urgent_fixed`. It compiles, and its assumptions are the model axioms, `reachable_net_ent`, the `reachableEnt` stub and the admitted `EntAuxResults.del_listening` (not blacklisted). The proof takes the entity delay from `del_net_ent`, gets `listeningStateEnt e` from `del_listening`, and refutes each `msgBadPathEnt` case: `gotMsg` enables `chanPos;?[l]`, `gotRange` enables `chanMCurr;?[m]` and `badOvlp` enables `chanBad *!`. `bisim_dae` moves the enabled action to `listening`, which cannot do it (inversion).
- **Caveat for the owner (semantic issue, analysis only):** in the `mbpMsg` (`gotMsg`) case the fixed proof leans on `del_listening`, and I believe `del_listening` (and `gotMsgStateEnt_urgent`) are false in the current entity semantics. `gotMsg` waits on `chanPos<vL>?`, and the position read is the entity rule `stepDePosRead`, which involves neither interface nor mode state. `noSync`/`noSyncNow` (EntityLanguage.v:196-209) only forbid delay when the *interface or mode state* can do the complement. No software component ever outputs on `chanPos`, so `stepTpPar` does not block either. So an entity whose listener sits in `gotMsg` can delay, for example with the broadcaster `sleeping` and the overlap `dormant`, which looks reachable. Fixing this needs a semantic change rather than a new hypothesis: for example, add `forall l', ~discActEnabled p (chanPos ;? [basePosition l'])` (and the same for the delay derivatives `p'`) as a premise of `stepTeDel`, or make position reads urgent in `noSyncNow`. With that change, `del_listening` and `msgBadPathNet_urgent_fixed` become plausible. The `gotRange` and `badOvlp` cases don't depend on this. `gotRange` is urgent even without reachability, because the mode state always offers `chanMCurr .! m`.
- **Partial proof:** `(prover work area; evidence for audited targets is in `2026-10-14-proof-completion-pass-1-evidence/audit/`) NARMisc.msgBadPathNet_urgent.v` contains the counterexample (`msgBadPathNet_urgent_cex`, `msgBadPathNet_urgent_refute`) and the fixed proof (`msgBadPathNet_urgent_fixed`), both compiled.

### `NARMisc.tfsState_not_currSince`

- **Where:** `src/NARMisc.v` line 437 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:failSafeSucc-may-be-identity`
- **Fix (audit summary):** Add ~ failSafe m (incomp_tfs gets it from Main H4); alternatively a model axiom failSafeSucc m <> m.

- **Status:** NEEDS-HYPOTHESIS (`~ failSafe m`). The statement is not derivable from the model axioms: it fails in admissible models where `failSafeSucc m = m` for a fail-safe `m`.
- **Intent:** thesis Listing 7.35: "when a transition to a fail-safe mode is completed, the currSince relation ceases to hold". The overlap component's only way out of the tfs states is `tfsListen --chanUnpause!--> dormant`. Before that, `tfsCurr --chanMCurr!--> tfsBc` installed `failSafeSucc m'` as the current mode, where `m'` is the mode read at `tfsStart`.
- **Failure:** the intuition needs the fail-safe write to actually *change* the current mode away from `m`. The axioms don't guarantee that.
  - Nothing in `ComhBasics.v` forbids `failSafeSucc m = m` or `m -mtr-> m`. The only constraints are `failSafeSuccFS` and `failSafeSucc_successor : m -mtr-> failSafeSucc m`. Take a model in which `m` is fail-safe and `failSafeSucc m = m`.
  - `currSince m` for such an `m` is reachable: `stepDeTest` lets the environment initiate a transition to `m`, and the normal path `dormant -> init m -> ovWait/ovReady (nextSince m) -> switchBc -> switchCurr -> switchListen` (`currSinceBase`) completes it.
  - The listener then goes `badOvlp --chanBad!-->` and the overlap goes `dormant --chanBad?--> tfsStart`. From there: `tfsStart` reads `m`; `tfsNext m` writes next mode `failSafeSucc m = m` (`stepMsInit`); `tfsCurr` waits for the timeout and does `chanMCurr!` (`stepMsSwitch`), so the current mode is still `m`.
  - `currModeNet m` holds at every step, so `currSinceDisc` keeps `currSince m t` alive through `tfsBc` and `tfsListen`. At the `tfsListen -> dormant` step we have `tfsStateNet i n`, `~tfsStateNet i n'` and `currSince m t i n p`, which contradicts the lemma.
  - This can't be exhibited inside Rocq because `Mode`/`failSafeSucc` are abstract axioms, but it shows the goal is independent of them.
  - Within Rocq, the proof goes through except for the `failSafe m` branch. The remaining goal is `TS : tfsStateNet i n, NTS : ~tfsStateNet i n', CS : currSince m t i n p, FS : failSafe m |- False`. No lemma in scope (only `currSince_curr` talks about `currSince`) refutes it.
- **Ripple-up:** `in_safety_cone=False`.
  - Used in the commented-out proof of `NARIncomp.incomp_tfs` (currently `Admitted`). `incomp_tfs` is applied in `Main.safety_aux`, where `H4 : ~ failSafe m2` is available, so the fix can be threaded through.
  - The admitted `NARInsuff.tfs_pres_not_currSince` (second disjunct `forall m' t' p', ~currSince m' t' i n p'`) has the same flaw and needs the same restriction. Its user in `NARInsuff` works under `~ sufficient`/`currSince m` hypotheses; check there whether `~failSafe m` is at hand.
- **Suggested fix (preferred):**
  ```coq
  Lemma tfsState_not_currSince (m : Mode) (t : Time) (i : nat) (n n' : Network)
    (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
    ~ failSafe m -> tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
  ```
  `incomp_tfs` then gets `~ failSafe m` too (Main passes `H4`).
  I proved this fixed version in Rocq (`--explore`, helper `tfsState_not_currSince_fixed`, ends in `Qed`). The proof is `currSince_curr` plus the existing proved `NetAuxBasics.tfs_currMode_disc_pres`, which in turn uses the admitted `tfsListen_failSafe_net` and the fwd-tracking lemmas.
  An alternative is a model axiom `failSafeSucc m <> m`. It is weaker than it looks: you would also need a new invariant that the next mode in `tfsCurr` is exactly `failSafeSucc` of the current mode, and `tfsCurr_failSafe` only says it is fail-safe. So the hypothesis route is preferable.
- **Partial proof:** `NARMisc.tfsState_not_currSince.v` in this directory:
  ```coq
  Lemma tfsState_not_currSince_fixed (m : Mode) (t : Time) (i : nat) (n n' : Network)
    (p : reachableNet n) (a : ActDiscNet) (w : n -NA- a -NA> n') :
    ~ failSafe m ->
    tfsStateNet i n -> ~tfsStateNet i n' -> ~currSince m t i n p.
  Proof.
    intros NFS TS NTS CS. apply NTS.
    eapply tfs_currMode_disc_pres; [exact w | | exact NFS | exact TS].
    eapply currSince_curr. exact CS.
  Qed.
  (* original statement: *)
  Proof.
    intros TS NTS CS.
    destruct (fsDecMode m) as [FS | NFS].
    2: { eapply tfsState_not_currSince_fixed; eassumption. }
    (* stuck: failSafe m branch *)
  Admitted.
  ```

### `NARMisc.msgBad_disc_net`

- **Where:** `src/NARMisc.v` line 445 · **Lemma** · 2015 label: `3` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `other:msgBadPathEnt-does-not-exclude-tfs-overlap`
- **Fix (audit summary):** Add ~ tfsStateNet i n (or ~tfsStateProt in msgBadPathEnt), or weaken the conclusion with \/ tfsStateNet i n'.

- **Status:** FALSE (counterexample). The key step is verified in Rocq; the path part is argued precisely below. The fix is NEEDS-HYPOTHESIS: add `~ tfsStateNet i n`, or weaken the conclusion.
- **Statement (frozen, `src/NARMisc.v:445`):**
  ```coq
  Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
    (p : reachableNet n) (w : n -NA- a -NA> n') :
    msgBadPathNet i n -> currModeNet m i n ->
    msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w).
  ```
- **Intent:** while the listener handles a possibly incompatible message (`gotMsg` → `gotRange` → `currPincCheck`≈`badOvlp`), any discrete step either keeps it on that path, or is the `chanBad` handshake that starts tfs right now (`tfsBase`, time 0).

## Failure

The proof sketch under the lemma says: *"We can eliminate tfsListen and tfsCurr because ... the definition of msgBadPath dictates that an entity is not tfs."* The current definition does not say that. `msgBadPathEnt` (`EntAuxDefs.v:98`) only constrains the listener component: `gotMsg`/`gotRange` with `possiblyIncompatible`, or `badOvlp`. Nothing excludes the overlap being in `tfsCurr` or `tfsListen`, and both of those accept `chanBad?` and stay where they are:

```
tfsCurr   := chanAbort? tfsCurrN   $+$ chanBad? tfsCurrN   $+$ chanMCurr!tfsBcN
tfsListen := chanAbort? tfsListenN $+$ chanBad? tfsListenN $+$ chanUnpause!dormantN
```

So the `badOvlp` case has a step `w` (the internal τ from `chanBad!`/`chanBad?`) after which:
- the listener is `listening`, so `msgBadPathNet i n'` is false;
- the overlap is still `tfsCurr`/`tfsListen` and was *not* just started. `tfs m zeroTime i n' (reachNetDisc n n' a p w)` can only come from `tfsDisc` back along `p` to the last `tfsStart`. That needs both zero elapsed delay since then **and** `currModeNet m` at that `tfsStart`. `reachableNet` is a `Type`, so `tfs` really is indexed by the concrete path, and proof irrelevance doesn't help.

### Verified in Rocq (`NARMisc.msgBad_disc_net.v`, `--explore`, rc=0)

`msgBad_disc_net_onestep` proves this for any `P1 l h k`, with `e := [| P1 $||$ tfsListen $||$ badOvlp, l, h, k |]` and `e' := [| P1 $||$ subProcTerm (listsToSub [] []) (liftNameProc tfsListenN) $||$ liftNameProc listeningN, l, h, k |]`:
- `msgBadPathNet 0 [e]`
- `tfsListenStateNet 0 [e]`
- `[e] -NA- anTau -NA> [e']`
- `~ msgBadPathNet 0 [e']`
- `tfsListenStateNet 0 [e']`

The mode state `k` is unchanged. Helpers:
- `msgBad_disc_net_tgt_not`: an entity whose listener is `listening` is never `msgBadPathEnt`. It uses `bisim_dae`. `listening` cannot do `chanPos?`, `chanMCurr?` or `chanBad!`.
- `msgBad_disc_net_tfsListen_unfold`: the derivative is bisimilar to `tfsListen`.

### Full reachable counterexamples (the path part, argued by hand)

**(A) No delays.** This works in any model with a fail-safe `F` and a proof `p0 : F -mtr-> failSafeSucc F`, where `FS := failSafeSucc F <> F` and `modeTransTime F FS p0 = zeroTime`. Single-entity network, starting at `[[| procProtocol, l, h0, F |]]`, which is initial. All steps are discrete:
1. The environment sends `anIn [-[baseMode M; basePosition l], l, r-]`. Then `chanInProc` takes the listener to `gotMsg M l`.
2. `chanPos` takes it to `gotRange M r0` with `r0 <= 0`.
3. `chanMCurr` reads `F`, giving `currPincCheck F M r0` ≈ `badOvlp`, because `possIncDist F M > 0 >= r0`. This state is `msgBadPath`.
4. `chanBad` syncs with `dormant`. The overlap moves to `tfsStart` and the listener to `listening`.
5. `tfsStart` reads `F` and moves to `tfsNext F`. That writes `FS` (`stepMsInit p0`, timer `0`) and moves to `tfsCurr`. `chanMCurr!` (`stepMsSwitch`) moves to `tfsBc`, and the mode is now `FS`. `chanTrans!` syncs with `sleeping`'s `chanTrans?` and moves to `tfsListen`.
6. Repeat steps 1–3. The listener is now `currPincCheck FS M r0` ≈ `badOvlp`. Call this state `n`. It satisfies `msgBadPathNet 0 n` and `currModeNet FS 0 n` (`currMode_intro`).
7. `w` is the `chanBad` sync with `tfsListen`, as in the verified step. Call the result `n'`.

In `n'`, `~msgBadPathNet 0 n'` (verified). For `tfs FS zeroTime 0 n' (reachNetDisc n n' _ p w)`, invert along `p`. Every state from the end back to the `tfsStart` of step 4 is not `tfsStart`, so `tfsBase` fails and only `tfsDisc` applies. At the `tfsStart` state, `tfsBase` needs `currModeNet FS` while the mode is `F <> FS` (`currMode_ent_ex` and uniqueness). `tfsDisc` needs `tfs` at the previous state, where the overlap is `dormant`. That fails because `tfsDisc` needs `tfsStateNet` there and `tfsBase` needs `tfsStart`. So `tfs` is false, and so is the conclusion.

**(B) With a delay.** This needs only `modeTransTime F FS p0 > 0`. Same start. Reach `tfsCurr` with mode state `<|F, FS, T|>`, `T > 0`. Delay by `d < T`. This is legal: `chanMCurr!` is not enabled before the timeout, and there are no complementary actions among `sleeping`, `tfsCurr` and `listening`, so `noSync` and `stepTpPar` hold. Then repeat steps 1–3 to reach listener ≈ `badOvlp` (state `n`, mode `F`). Then `w` is the `chanBad` sync with `tfsCurr` (`n'`). `~msgBadPathNet 0 n'` holds as before. `tfs F zeroTime 0 n'` would have to pass back through the `reachNetDel` step. There `tfsBase` fails, because the overlap is in `tfsCurr`. `tfsDel` gives time `t +dt+ d > 0 <> zeroTime`. So the conclusion is false again.

The other cases are a second, independent route. In the `gotMsg`/`gotRange` cases, `w` can be the overlap's `tfsCurr → tfsBc` mode switch. That changes `currModeMState` from `m` to `failSafeSucc m`. `possiblyIncompatible` can then fail (`minDistComp fs _ = 0`), and the RHS fails whenever a delay elapsed since `tfsStart`. It does whenever `modeTransTime > 0`.

## Ripple-up

- Not in the safety cone (per `show`).
- The only user is `NARIncomp.instant_incomp_tfs` (`NARIncomp.v:411`, closed with `Qed` relative to this lemma). There, `currSince m t i n p` does **not** exclude the overlap being in `tfsCurr`. `currSince` survives until the `tfsCurr` mode switch, so scenario (B) also looks like a counterexample to `instant_incomp_tfs`: message received at time 0, `0 < t`, the entity already tfs from an earlier event. Through that lemma the issue reaches the (commented-out) proof of `incomp_bad` in `NARIncomp.v`.

## Suggested fix

Either option needs approval, since each changes a statement.

**Option 1: restore the sketch's assumption as a hypothesis.**
```coq
Lemma msgBad_disc_net (n n' : Network) (a : ActDiscNet) (i : nat) (m : Mode)
  (p : reachableNet n) (w : n -NA- a -NA> n') :
  msgBadPathNet i n -> currModeNet m i n -> ~ tfsStateNet i n ->
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w).
```
(Equivalently, add `~ tfsStateProt p` to each `msgBadPathEnt` constructor.) The sketch then goes through:
- `chanBad!` can only meet `dormant`/`ovWait`, both going to `tfsStart`. This gives `tfsBase`, and the internal τ leaves the mode state alone.
- The only mode changer is `chanMCurr!`, from `switchCurr` or `tfsCurr`. `switchCurr` forces the listener `paused` (`paused_switch_net`), which is disjoint from `msgBadPath`. `tfsCurr` is excluded by the new hypothesis.

`instant_incomp_tfs` would then need to case-split on `tfsStateNet i n`.

**Option 2: weaken the conclusion.** This keeps the callers' hypotheses.
```coq
  msgBadPathNet i n' \/ tfs m zeroTime i n' (reachNetDisc n n' a p w) \/ tfsStateNet i n'.
```
This is provable: if the overlap is already tfs while the listener is on `msgBadPath`, then it stays tfs. The only exit is `tfsListen --chanUnpause!--> dormant`, which needs the listener in `listening`/`paused`. `instant_incomp_tfs` and `incomp_bad` would need the same extra disjunct ("already transitioning to fail-safe"), which is arguably the right reading of the thesis.

## Partial proof

None of the target itself. The Rocq file holds the verified counterexample step and the disjointness helpers.

### `NARMisc.tfs_zero_disc_pres`

- **Where:** `src/NARMisc.v` line 453 · **Lemma** · 2015 label: `4` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:modeTransTime-may-be-zero`
- **Fix (audit summary):** Either add model axiom 0 < modeTransTime m m' p (owner approval) or add hypothesis currSince m' t i n p (only caller has it).

- **Status:** NEEDS-HYPOTHESIS (missing model axiom: mode transition times are positive). False in
  models of the current axioms where `modeTransTime m (failSafeSucc m) _ = 0`.
- **Intent:** while an entity is `tfs m` with elapsed time 0, any discrete step keeps it `tfs m 0`, i.e. a
  fail-safe transition cannot *complete* within the instant it starts.
- **Failure:** `tfs m 0 i n p` is built only by `tfsBase` (`tfsStart`) and `tfsDisc` steps (`tfsDel` adds a
  positive delay, so cannot give time 0). The in-file sketch says a `tfs m 0` entity is in `tfsStart`,
  `tfsNext` or a *delay-guarded* `tfsCurr`. The guard is the mode state: `tfsNext m` does
  `chanMNext<failSafeSucc m>!`, which synchronises with `stepMsInit`, giving mode state
  `<| m, fSucc m, modeTransTime m (fSucc m) pf |>`; `tfsCurr` leaves only by `chanMCurr!`, which synchronises
  with `stepMsSwitch`, enabled only on `<| _, _, zeroTime |>`. Nothing in `ComhBasics.v` says
  `0 < modeTransTime m m' pf` (only `modeTransTime_bound : modeTransTime m m' p <= trans m`; the thesis
  Def. 5.1 doesn't require positivity either). With `modeTransTime m (fSucc m) _ = 0` (consistent with
  all model axioms), the following all-discrete, zero-delay run exists (the thesis's own Examples 5.12/5.13,
  thesis.txt ~l.7015-7050, minus the delay in tfsCurr):
  `ovWait|badOvlp --τ(bad)--> tfsStart` (tfsBase: tfs m 0) `--mCurr<m>?--> tfsNext m --mNext<fSucc m>!-->
  tfsCurr` (mode state `<|m,fSucc m,0|>`) `--mCurr!--> tfsBc --τ(trans)--> tfsListen` (still tfs m 0 by
  tfsDisc) `--τ(unpause, listener in listening)--> dormant`. In the last step `n'` has the overlap in
  `dormant`, so neither `tfsBase` (needs tfsStart) nor `tfsDisc` (needs `tfsStateNet i n'`) can derive
  `tfs m 0 i n' (reachNetDisc ...)` (`tfsDel` has the wrong reachability index). So the conclusion fails.
  Not Rocq-checkable as a concrete counterexample: `Mode` is an abstract axiom type and `currModeNet` (in
  `tfsBase`) an opaque `Parameter`, so no concrete reachable network can be built; the argument is on
  paper against the intended semantics.
- **Ripple-up:** only user: `NARIncomp.instant_incomp_tfs` (NARIncomp.v:414). `show` says
  `in_safety_cone=False`. Related: `NARMisc.tfs_transGuard` relies on `tfsNext_tfs_zero` and
  `modeTransTime_bound` only, so it isn't affected.
- **Suggested fix:** either
  1. *(model axiom, owner approval)* add to `ComhBasics.v`
     `Axiom modeTransTime_pos : forall m m' (p : m -mtr-> m'), 0 < modeTransTime m m' p.`
     Then the lemma should be provable by the in-file sketch, via the strengthened invariant
     `tfs m zeroTime i n p -> tfsStartStateNet i n \/ (exists m', tfsNextStateNet m' i n) \/
      (tfsCurrStateNet i n /\ exists t', transGuard t' i n /\ 0 < t')`,
     proved by induction on `tfs` with net-level fwd-tracking (`tfsStart_next_net`, `tfsNext_next_net`,
     `mState_disc_pres`, `mState_switch_states`). That's sizeable inter-component work (label 4 was optimistic).
  2. *(statement change, cheaper; recommended)* add the hypothesis the only caller already has
     (`H : currSince m t i n p` in `instant_incomp_tfs` at the `apply tfs_zero_disc_pres` line):
     ```
     Lemma tfs_zero_disc_pres (n n' : Network) (a : ActDiscNet) (i : nat) (m m' : Mode)
       (t : Time) (p : reachableNet n) (w : n -NA- a -NA> n') :
       currSince m' t i n p -> tfs m zeroTime i n p ->
       tfs m zeroTime i n' (reachNetDisc n n' a p w).
     ```
     **Rocq-checked** (explore mode, `NARMisc.tfs_zero_disc_pres.fix.v`) relative to admitted
     `tfs_rel_state`, `tfsState_not_currSince` and conjecture `tfsStateNet_dec`:
     ```
     intros CS T. destruct (tfsStateNet_dec i n') as [D|D].
     - apply tfsDisc; assumption.
     - exfalso. eapply (tfsState_not_currSince m' t i n n' p a w);
       [eapply tfs_rel_state; eassumption | exact D | exact CS].
     ```
     Caller change: `eapply tfs_zero_disc_pres; eassumption`.
     Caveat for the owner: `tfsState_not_currSince` can itself fail if `failSafeSucc m = m` is allowed
     (the mode doesn't change at `tfsCurr -> tfsBc`, so `currSince m` survives through the tfs run). It
     needs `failSafeSucc m <> m`, or "m not fail-safe", as a hypothesis. In `instant_incomp_tfs`, m is
     the current mode of an entity that just got an incompatible message, so non-fail-safe is natural there.
- **Partial proof:** none for the statement as given (no positivity axiom to use).

## EntAuxResults

### `EntAuxResults.tfsBc_failSafe`

- **Where:** `src/EntAuxResults.v` line 69 · **Lemma** · 2015 label: `C` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Add hypothesis reachableEnt e (available at NARNonFS_currSince.v:176 via reachable_net_ent); define reachableEnt; and also forbid internal sync on mode-state channels, else the reachable version still fails (see notes).

- **Status:** NEEDS-HYPOTHESIS (unprovable as stated; with the missing hypothesis it becomes BLOCKED-ON-STUB `reachableEnt`)
- **Intent:** in a *reachable* entity whose overlap component is in the `tfsBc` state
  (`chanTrans!tfsListenN`), the mode state's current mode is fail-safe: the preceding
  `tfsCurr` state wrote the fail-safe successor out on `chanMCurr`.
- **Failure:** the statement has no reachability hypothesis, so `e` may be any entity whose
  process is `nilProc $||$ tfsBc $||$ nilProc`, with an arbitrary mode state `sing m`. So the
  lemma implies that *every* mode is fail-safe (given any `Position` and `Interface`).
  Verified in Rocq (compiles in `--explore`; see `EntAuxResults.tfsBc_failSafe.v` HELPERS):
  ```
  Lemma tfsBc_failSafe_cex :
    (forall e, tfsBcStateEnt e -> failSafe (currModeEnt e)) ->
    Position -> Interface -> forall m : Mode, failSafe m.
  Proof.
    intros H l h m.
    apply (H ([| nilProc $||$ tfsBc $||$ nilProc, l, h, sing m |])).
    unfold tfsBcStateEnt, tfsBcStateProt. constructor. constructor.
    unfold tfsBcState. apply ProcEquiv.bisim_refl.
  Qed.
  ```
  The model axioms in `ComhBasics.v` don't force all modes to be fail-safe. For example, `Mode := bool`,
  `failSafe := (fun b => b = true)`, `failSafeSucc := fun _ => true` and `modeTransRel := fun _ _ => True`
  satisfy `fsDecMode`, `failSafeSucc*` and `minDistCompFS`. So the statement is not provable, and in any intended
  model (one with a non-fail-safe mode) it is false. If it were made true, every mode would be fail-safe, `minDistComp`
  would be identically 0, and `safety` would become vacuous.
- **Ripple-up:** in the safety cone. One user: `NARNonFS_currSince.v:176` (`nonFS_currSince`), which
  applies it to `[|p', l', h', k'|]`, the entity `i` in the reachable network `n'` after a step.
  The `(*CHANGE: ... Add reachability of entity as a hypothesis*)` comment above the lemma already
  records this. At the use site, `reachableEnt [|p',l',h',k'|]` is available via
  `reachable_net_ent` (NetAuxBasics.v:745) from `reachableNetDisc ... n'` and `e' @ i .: n'` (H4).
- **Suggested fix:**
  ```
  Lemma tfsBc_failSafe (e : Entity) :
    reachableEnt e -> tfsBcStateEnt e -> failSafe (currModeEnt e).
  ```
  At the use site, insert `eapply reachable_net_ent; [econstructor; eassumption | eassumption]`
  (or equivalent) before `apply TF`.
  The fixed statement is still BLOCKED-ON-STUB while `reachableEnt` is an opaque `Parameter`.
  It becomes provable with `reachableEnt e := exists n i, reachableNet n /\ e @ i .: n`
  (equivalently, an inductive closure of initial entities under `-EA->`/delays). Proof: induct on reachability with the
  invariant "tfsCurr ⇒ nextModeEnt (failSafeSucc _) e" (cf. `tfsCurr_failSafe`) together with
  "tfsBc ⇒ failSafe (currModeEnt e)". The only entry into `tfsBc` is the `chanMCurr!` output from `tfsCurr`,
  which synchronises with the mode state's `stepDeCurrWrite` and sets the current mode to that fail-safe next mode.
  `tfsBc` itself only does `chanTrans!`, which leaves the current mode unchanged.
- **Partial proof:** none beyond the counterexample.

### `EntAuxResults.bcReady_pos`

- **Where:** `src/EntAuxResults.v` line 102 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define inPosEnt (e.g. inductive with witness [|p,l,h,k|], or posEnt e = l) and reachableEnt; prove posEnt e = l by reachability induction using a new process lemma bcReady_prev and bcReady urgency.

- **Status:** BLOCKED-ON-STUB (`inPosEnt`, EntAuxDefs.v:149; also `reachableEnt`, EntAuxDefs.v:143)
- **Intent:** if a reachable entity's broadcast component is ready to output `(m, l)` (state `bcReady m l`), then the entity is at position `l`. The value `l` was read from `chanPos`, and the state is urgent, so it cannot have moved since.
- **Failure:** the goal is `inPosEnt l e`, and `inPosEnt` is an opaque `Parameter`. No definition, axiom, lemma or conjecture visible at this point (or anywhere else in the project) has `inPosEnt` as a conclusion. It only appears as the conclusion of this lemma and `ovReady_pos`, and as a hypothesis of `NetAuxBasics.inPos_ent_net`. The hypothesis `reachableEnt e` is also an opaque `Parameter`, and nothing visible derives `False` from it or from `bcReadyStateEnt m l e`. Interpreting `inPosEnt := fun _ _ => False` and `reachableEnt := fun _ => True` is consistent with every visible assumption, and makes the statement false for any entity whose process is `bcReady m l` in parallel with anything. So no proof exists while the stubs are opaque.
- **Ripple-up:** in the safety cone. Its only user is `NARMsgPosition.v:244`, in the base case of the "sent message carries the sender's position" result. There it is combined with `inPos_ent_net` and `inPos_unique` to show that the broadcast position equals the sender's position. `ovReady_pos` (EntAuxResults.v:110) is the twin lemma for the overlap component and is blocked the same way.
- **Suggested fix (stub definitions; the statement stays as it is):**
  ```coq
  (* EntAuxDefs.v, replacing the Parameter; analogous to the nextModeEnt idea *)
  Inductive inPosEnt (l : Position) : Entity -> Prop :=
    | ipeWitness (p : ProcTerm) (h : Interface) (k : ModeState) :
      inPosEnt l ([|p, l, h, k|]).
  (* or: Definition inPosEnt l e := posEnt e = l. *)

  (* moved below initialEnt *)
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  These match the definitions proposed in `NetAuxBasics.inPos_ent_net.fail.md` and `NetAuxBasics.reachable_net_ent.fail.md`.
- **Proof plan under these definitions** (not mechanised; the stubs can't be replaced from a proof file):
  Prove `posEnt e = l` by induction on `reachableEnt e`.
  1. *Init:* `initialProc p` puts the broadcast component in `sleeping`, not `bcReady`. Use inversion and the bisimulation-contradiction tactics (`bisim_contra`).
  2. *Discrete step* `e -EA- a ->> e'`: discrete entity steps never change the position (every `stepDiscEnt` rule keeps `l`). If the broadcast component of `e` was already `bcReady m l`, apply the IH. Otherwise it moved into `bcReady m l`. Here a missing process-level backtracking lemma is needed, in the style of `ovReady_prev` (ProtAuxResults.v:433):
     `bcReady_prev : p -PA- a -PA> p' -> broadcastState p -> bcReadyState m l p' -> bcWaitState m zeroTime p /\ a = chanPos ;? [basePosition l]`
     (`bcWait` = `... + $<x>$chanPos<vL>? bcReady(m, vL) + ...`, SoftwareLanguage.v:133). Lifted through the parallel triple, an input on `chanPos` can only be matched by `stepDePosRead`, because no component outputs on `chanPos`. That rule forces the value read to be the entity's position, so `l = posEnt e = posEnt e'`.
  3. *Delay step* `e -ED- d ->> e'` (with `d > 0`, since `Delay` is a `posreal`): a delay of the broadcast component cannot enter `bcReady` from another state (an output prefix only idles in itself), so `e` was already in `bcReady m l`. Then `bcReady_urgent` (EntAuxResults.v:273, which needs `reachableEnt e` and is proved via `reachable_ent_prot`) gives `False`. The urgency lemma sits *below* this one in the file, so either move `bcReady_pos` below the urgency section or inline the `noSyncNow_tac` / `bcReady_outProc_out` argument.
  Finally, `posEnt e = l` gives `inPosEnt l e` by `destruct e; simpl in *; subst; constructor`.
- **Partial proof:** none. The goal `inPosEnt l e` has no introduction rule while it is a `Parameter`.

### `EntAuxResults.ovReady_pos`

- **Where:** `src/EntAuxResults.v` line 110 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Same as bcReady_pos: define inPosEnt and reachableEnt; also add an ovReady_urgent / ovReady_outProc_out lemma (missing today) and an ovReady backtracking helper.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`, EntAuxDefs.v:143; `inPosEnt`, EntAuxDefs.v:149)
- **Intent:** if a reachable entity's overlap component is in `ovReady m t l` (about to output `chanOutProc![m, l]`), then the entity is currently at position `l`.
- **Failure:** the conclusion `inPosEnt l e` is an opaque `Parameter`. The only visible statements that conclude `inPosEnt` are `bcReady_pos` (just above, also admitted) and this target. `bcReady_pos` needs `bcReadyStateEnt m l e`, which cannot be derived from `ovReadyStateEnt m t l e`: the broadcast and overlap components are independent parts of the `parTriple`. Interpreting `inPosEnt := fun _ _ => False` and `reachableEnt := fun _ => True` is consistent with every visible assumption, and it makes the statement false for any entity whose overlap component is in `ovReady`. So it can't be proved while the stubs are opaque.
- **Ripple-up:** in the safety cone. It is used at NARMsgPosition.v:254 (`lets OP : ovReady_pos H4 H9. eapply inPos_ent_net in OP.`) to show that the position in an overlap-component broadcast equals the sender's position. It has the same role as `bcReady_pos` at NARMsgPosition.v:246.
- **Suggested fix (stub definitions; statement unchanged):**
  ```coq
  Inductive inPosEnt (l : Position) : Entity -> Prop :=
    | ipeWitness p h k : inPosEnt l ([|p, l, h, k|]).
  (* reachableEnt: reflexive-transitive closure of initialEnt under -EA- / -ED-,
     declared after initialEnt; see NetAuxBasics.reachable_net_ent.fail.md *)
  ```
- **Proof plan under those definitions:** induct on `reachableEnt` with the invariant `forall m t l, ovReadyStateEnt m t l e -> posEnt e = l`.
  - *Init:* `initialProc p` puts the overlap component in `dormant`, so `ovReady` is impossible (state disjointness).
  - *Discrete step `e -EA- a ->> e'`:* the entity position is unchanged by every discrete rule. If `e'` is in `ovReady m t l`, then either the overlap component did not move, so `e` was already in `ovReady m t l` and the IH applies, or it moved. If it moved, `ovReady_prev` (ProtAuxResults.v:433, admitted) gives that `e` was in `ovWait m t x 0`, and the only `ovWait -> ovReady` action is `chanPos ;? [basePosition l']`. At the entity level that can only be synchronised by `stepDePosRead`, which forces `l' = posEnt e = posEnt e'`. A lifted helper is needed for this, analogous to `ovReady_ovWait_track_ent`.
  - *Delay step `e -ED- d ->> e'`:* this needs an urgency lemma `ovReady_urgent : reachableEnt e -> ovReadyStateEnt m t l e -> e -ED- d ->> e' -> False`, proved like `bcReady_urgent` (EntAuxResults.v:272): `ovReady` enables `chanOutProc ;! [m, l]` and the interface always accepts it. It also needs time-backtracking of `ovReady` (`ovReady` is a pure output prefix, so the predecessor under delay is also `ovReady m t l`). No `ovReady_urgent` exists in the frozen sources yet, and there is no `ovReady_outProc_out` lemma either; it would have to be added next to `bcReady_outProc_out`.
  - The comment's "disc_pre_pos [salvaged]" refers to this position-preservation fact for discrete steps. It is not present in the frozen sources.
- **Partial proof:** none. Nothing can be stated about `inPosEnt` until the stub is filled.

### `EntAuxResults.link_ent_outList`

- **Where:** `src/EntAuxResults.v` line 573 · **Lemma** · 2015 label: `5` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:wrong-step-relation (input disjunct uses -tl- ?? which has no rules; buffering is -ol- ??)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Change the input disjunct to lo -ol- v ?? -ol> lo' and InterfaceLanguage.outList_in_input_pres's premise accordingly; both fixed statements are proved with model+stdlib axioms only (link_ent_outList_fixed, link_ent_outList_input_pres_fixed).

- **Status:** FALSE (counterexample, verified in Rocq)
- **Intent:** a discrete entity step either leaves the output list `lo` unchanged, or the output list changes by buffering one message (input) or by forwarding one message (output).
- **Failure:** the input disjunct is stated at the *timed-list* level, `outList lo -tl- v ?? -tl> outList lo'`. But `stepTimedList` has no input rule at all: its rules are `stepTlFwdHd`/`stepTlFwd` (outputs `v !!`) and `stepTlDelEmp`/`stepTlDel` (delays). Buffering happens only at the output-list level (`stepOlBuff : mkOutputList l -ol- v?? -ol> mkOutputList (<(v, msgLatency)> :: l)`). So the `??` disjunct can never hold. The entity rule `stepDeIOProcInter` (the software outputs on `chanOutProc` and the interface buffers through `stepIntBuffOut`/`stepOlBuff`) makes `lo' = <(v,msgLatency)> :: lo`. Then `lo <> lo'`, there is no `??` timed-list step, and a `!!` step can't lengthen a list.
  Concrete instance (no reachability hypothesis is needed, since the lemma has none): `p = chanOutProc $<[]>$! nilProc`, `p' = nilProc`, `lo = mkOutputList []`, `lo' = mkOutputList [<([], msgLatency)>]`, `b = aeTau`, with `l, k, li, ln` arbitrary and kept. Lemmas `link_ent_outList_cex` and `link_ent_outList_false` below compile (checked with `--explore`, rc=0).
- **Ripple-up:** it's used only in `NetAuxBasics.outgoing_disc_pres` (line 632), which is in the safety cone and is used by `NARMsgPosition` line 56. That proof then calls `InterfaceLanguage.outList_in_input_pres` (Admitted, label 6) on the `??` disjunct. `outList_in_input_pres` has the same flawed `-tl- u ??` premise, so it is vacuously true and can't serve a corrected statement unchanged. `outgoing_disc_pres` itself is true: buffering only prepends, so membership is preserved. Only its support lemmas are mis-stated.
- **Suggested fix (option A, recommended: two statement changes and no proof-script change in `outgoing_disc_pres`):**
  ```coq
  Lemma link_ent_outList p p' l l' k k' li li' lo lo' ln ln' b :
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, lo -ol- v ?? -ol> lo'
    \/ outList lo -tl- v !! -tl> outList lo'.

  (* InterfaceLanguage.v *)
  Lemma outList_in_input_pres v u t lo lo' :
    <( v, t )> _: outList lo -> lo -ol- u ?? -ol> lo' ->
    <( v, t )> _: outList lo'.
  ```
  Both are proved below (`link_ent_outList_fixed`, `link_ent_outList_input_pres_fixed`; they compile). The script of `outgoing_disc_pres` (`lets LEO : link_ent_outList LE1. ... eapply outList_in_input_pres; eassumption.`) should type-check unchanged with them (checked by reading the script, not compiled), because the `??` hypothesis now has exactly the type the new `outList_in_input_pres` expects.
  *Option B:* keep `outList_in_input_pres` and phrase the input disjunct as `outList lo' = <(v, msgLatency)> :: outList lo`. The `??` branch of `outgoing_disc_pres` then becomes `rewrite ...; right; assumption` instead of the `outList_in_input_pres` call.
- **Partial proof / evidence:**
  ```coq
  Lemma link_ent_outList_cex (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
    [|chanOutProc $<[]>$! nilProc, l, {| li := li; lo := mkOutputList []; ln := ln |}, k|]
      -EA- aeTau ->>
    [|nilProc, l, {| li := li; lo := mkOutputList [<([], msgLatency)>]; ln := ln |}, k|] /\
    ~ (mkOutputList [] = mkOutputList [<([], msgLatency)>] \/ exists v,
       outList (mkOutputList []) -tl- v ?? -tl> outList (mkOutputList [<([], msgLatency)>])
    \/ outList (mkOutputList []) -tl- v !! -tl> outList (mkOutputList [<([], msgLatency)>])).
  Proof.
    split.
    - eapply stepDeIOProcInter with (v := []).
      + constructor. constructor.
      + constructor. constructor.
    - intros [E | [v [T | T]]].
      + inversion E.
      + inversion T.
      + inversion T.
  Qed.

  Lemma link_ent_outList_false (l : Position) (k : ModeState) (li : InputList) (ln : NotifList) :
    ~ (forall p p' l l' k k' li li' lo lo' ln ln' b,
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, outList lo -tl- v ?? -tl> outList lo'
    \/ outList lo -tl- v !! -tl> outList lo').
  Proof.
    intros H. destruct (link_ent_outList_cex l k li ln) as [S N].
    apply N. eapply H. exact S.
  Qed.

  Lemma link_ent_outList_fixed p p' l l' k k' li li' lo lo' ln ln' b :
    [|p, l, {| li := li; lo := lo; ln := ln |}, k|] -EA- b ->>
    [|p', l', {| li := li'; lo := lo'; ln := ln' |}, k'|] ->
    lo = lo' \/ exists v, lo -ol- v ?? -ol> lo'
    \/ outList lo -tl- v !! -tl> outList lo'.
  Proof.
    intros S. inversion S; subst; try (left; reflexivity).
    - right. match goal with [V : _ -i- chanOutProc {? _ -i> _ |- _] =>
        inversion V; subst end. eexists. left. eassumption.
    - match goal with [V : _ -i- chanInProc {! _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - match goal with [V : _ -i- chanAN {! _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - match goal with [V : _ -i- chanIOEnv {? _ -i> _ |- _] =>
        inversion V; subst end. left; reflexivity.
    - right. match goal with [V : _ -i- chanIOEnv _! _ !_ _ -i> _ |- _] =>
        inversion V; subst end.
      match goal with [V : _ -ol- _ !! -ol> _ |- _] => inversion V; subst end.
      eexists. right. eassumption.
  Qed.

  Lemma link_ent_outList_input_pres_fixed v u t lo lo' :
    <( v, t )> _: outList lo -> lo -ol- u ?? -ol> lo' ->
    <( v, t )> _: outList lo'.
  Proof.
    intros I S. inversion S; subst.
    - simpl. right. exact I.
    - match goal with [V : _ -tl- _ ?? -tl> _ |- _] => inversion V end.
  Qed.
  ```
  Once the statement is corrected, the body of `link_ent_outList_fixed` is the proof. It uses only model and stdlib axioms.

### `EntAuxResults.reachable_ent_prot`

- **Where:** `src/EntAuxResults.v` line 25 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt (EntAuxDefs.v:143) as the inductive closure of initialEnt under -EA-/-ED- (declared after initialEnt); then the proof is a 3-case induction (compiled against a local copy).

- **Status:** BLOCKED-ON-STUB (reachableEnt)
- **Intent:** The process component of a reachable entity is a reachable protocol term.
- **Failure:** `reachableEnt : Entity -> Prop` is an opaque `Parameter` (EntAuxDefs.v:143). No lemma in scope eliminates `reachableEnt`; it only ever appears as a hypothesis. The explore check confirms the goal is `H : reachableEnt ([|p, l, h, k|]) |- reachableProt p` with nothing usable. The source comment at EntAuxResults.v:24 already says "Requires reachableEnt to be defined before it is proved."
- **Ripple-up:** Not in the safety cone. Its only user is `Ltac urgency_pre_tac` (EntAuxResults.v:141), which every `urgency_pre_tac2*` call builds on, i.e. the entity-level urgency lemmas (`*_ent_del` / `..._ED_...` family at EntAuxResults.v:200-410). It is true under the intended definition.
- **Suggested fix (stub definition):** use the reflexive-transitive closure of `initialEnt` under entity transitions, as the "Idea" comment at EntAuxDefs.v:144 says. This is the same definition proposed in `NetAuxBasics.reachable_net_ent.fail.md`:
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' d : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  `initialEnt` is defined after the stub (EntAuxDefs.v:154), so the stub must move below it.
- **Proof under that definition** (compiled against the frozen build with a local, prefixed copy of the inductive; see `EntAuxResults.reachable_ent_prot.v` HELPERS, explore rc=0). Induct over the generalised entity:
  ```coq
  Lemma reachable_ent_prot_aux e : reachableEnt e -> reachableProt (procEnt e).
  Proof.
    induction 1 as [e I | e e' a R IH S | e e' d R IH S].
    - inversion I as [p l h k IP FS]; subst. inversion IP; subst. simpl. constructor.
    - inversion S; subst; simpl in *; try assumption; eapply reachprDisc; eassumption.
    - inversion S; subst; simpl in *. eapply reachprDel; eassumption.
  Qed.
  (* target *)
  Proof. intro R. apply (reachable_ent_prot_aux _ R). Qed.
  ```
  The case split is this: an initial entity's process is `procProtocol` (`reachprBase`); entity discrete steps either leave the process unchanged or take a process step `p -PA- a -PA> p'` (`reachprDisc`); entity delays take a process delay (`reachprDel`).

### `EntAuxResults.nextModeEnt_not_stable`

- **Where:** `src/EntAuxResults.v` line 28 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `typo` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Annotate (m2 : Mode) so the 4th field is sing m2, and define the nextModeEnt stub (inductive on <|m,m2,t|>); the fixed lemma is then `intro H; inversion H` (compiled as nextModeEnt_not_stable_fixed on a local copy).

- **Status:** FALSE (for the intended definition of the stub) and BLOCKED-ON-STUB (`nextModeEnt`, EntAuxDefs.v:146). It is on the harness's known-inconsistent list.
- **Intent:** an entity whose mode state is a *stable* mode `sing m2` has no next mode. The comment says "immediate once nextModeEnt is defined".
- **Failure:** `m2` has no type annotation. It sits in the 4th field of `mkEntity`, so Rocq infers `m2 : ModeState`, not `Mode`; `--explore` confirms this (`m2 : ModeState` in the context). Every entity has the form `[|p, l, h, k|]`, so the statement as written is equivalent to `forall m e, ~ nextModeEnt m e`, which says the relation is empty. The helper `nextModeEnt_not_stable_equiv` proves this equivalence in the explore file.
  - While the stub is an opaque `Parameter`, the statement can't be proved: `nextModeEnt := fun _ _ => True` is a model of the context that refutes it.
  - For the intended definition (EntAuxDefs.v:147: "one constructor, in which the entity has mode state <m, m', d>"), it is **false**. Instantiate `m2 := <| m, m, zeroTime |>` with any `m : Mode`. `nextModeEnt_not_stable_cex` checks this in Rocq against a local copy of the intended definition.
  - It is also inconsistent with the admitted `tfsCurr_failSafe` (EntAuxResults.v:58, `tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m`), and with `nextEq_mode` whenever a `nextEqStateEnt` entity exists.
- **Ripple-up:** not in the safety cone. `grep -n nextModeEnt_not_stable frozen/*.v` finds no users, only its own definition. Fixing it or deleting it breaks nothing.
- **Suggested fix:** annotate `m2` as a stable mode (one character of intent, `(m2 : Mode)`):
  ```coq
  Lemma nextModeEnt_not_stable m1 (m2 : Mode) p l h :
    nextModeEnt m1 ([|p, l, h, m2|]) -> False.
  ```
  (The coercion `sing` then makes the 4th field `sing m2`.) Together with the stub completion
  ```coq
  Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
    | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
  ```
  the fixed statement is proved by `intro H; inversion H.` (checked as `nextModeEnt_not_stable_fixed`). Without completing the stub, the fixed statement also follows from the admitted `nextMode_ent_mState` (EntAuxResults.v:487): `nextModeMState (sing m2) = None <> Some m1`. That only works if the lemma is moved after `nextMode_ent_mState`, or `nextMode_ent_mState` is moved before it.
  - Note for the lead: `NetAuxBasics-6/NetAuxBasics.nextMode_ent_ex.fail.md` claims `nextModeEnt_not_stable` becomes a one-line inversion once the stub is defined. That holds only for the `(m2 : Mode)` version, not for the statement as written.
- **Partial proof:** see `EntAuxResults.nextModeEnt_not_stable.v` (HELPERS are demonstrations only, not for splicing).

### `EntAuxResults.tfsNext_prev_ent`

- **Where:** `src/EntAuxResults.v` line 42 · **Lemma** · 2015 label: `#back-track-lift-ent` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis reachableEnt e (and reachableNet n in NetAuxBasics.tfsNext_prev_net); prove by reachability once reachableEnt is defined.

- **Status:** FALSE (counterexample). Also NEEDS-HYPOTHESIS `reachableEnt e`.
- **Intent:** this lifts `ProtAuxResults.tfsNext_prev` to entities. If an entity's overlap component is in `tfsNext m` after a discrete step, then before the step it was either already in `tfsNext m`, or in `tfsStart`. Thesis: tfsStart --chanCurr?m--> tfsNext(m), with self-loops on tfsNext(m).
- **Failure:** the statement has no reachability or shape hypothesis on the pre-state `e`, so `e`'s process can be any `ProcTerm`. The process-level original `tfsNext_prev` assumes `overlapState p`, and the entity lift dropped that hypothesis. Counterexample, checked in Rocq (`--explore`, helper `tfsNext_prev_ent_cex` ends in `Qed`, uses only constructors and `ProcEquiv.bisim_refl`):
  - `q := nilProc $||$ tfsNext m $||$ nilProc`
  - `e  := [| outPrefix chanMCurr [] q, l, h, <|m, m, zeroTime|> |]`
  - `e' := [| q, l, h, sing m |]`
  - `e -EA- aeTau ->> e'` by `stepDeCurrWrite`, a mode-state current write.
  - `tfsNextStateEnt m e'` holds because the middle component is literally `tfsNext m`.
  - `e`'s process is an `outPrefix`, not a `_ $||$ _ $||$ _`, so `liftOverlap` fails on it and neither disjunct holds.
  So the lemma implies `forall (m : Mode) (l : Position) (h : Interface), False`.
- **Ripple-up:** `in_safety_cone=False`. The only user is `NetAuxBasics.tfsNext_prev_net` (proved from this lemma, no reachability hypothesis), which is false by the same counterexample lifted to a one-entity network. That in turn is used only in the commented-out `(*R*)` proof of `NARMisc.tfsNext_tfs_zero`. That proof inducts on `p : reachableNet n`, so a reachability hypothesis is available where it is needed. Nothing in the `safety` cone breaks.
- **Suggested fix:**
  ```coq
  Lemma tfsNext_prev_ent m e e' a : reachableEnt e -> tfsNextStateEnt m e' ->
    e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
  ```
  The same fix applies upstream: `tfsNext_prev_net m i n n' a : reachableNet n -> tfsNextStateNet m i n' -> n -NA- a -NA> n' -> ...`. Its proof gets `reachableEnt` from `reachable_net_ent`.
  I proved the fixed statement in Rocq relative to the existing admitted lemmas (helper `tfsNext_prev_ent_fixed`, compiles with `Qed`). It uses `reachable_ent_prot` (admitted, stub `reachableEnt`), `reachableProt_triple` (admitted), `link_ent_soft_disc` (admitted), `link_par_triple_discW_2` (admitted) and `tfsNext_prev` (proved). It does not use any known-inconsistent lemma.
- **Partial proof:** see `EntAuxResults.tfsNext_prev_ent.v` in this directory (HELPERS: counterexample + fixed version):
  ```coq
  Lemma tfsNext_prev_ent_fixed m e e' a : reachableEnt e -> tfsNextStateEnt m e' ->
    e -EA- a ->> e' -> tfsNextStateEnt m e \/ tfsStartStateEnt e.
  Proof.
    intros RE TN S.
    inversion TN as [p' l' h' k' TP]; subst.
    inversion TP as [q1 q2 q3 TQ]; subst.
    destruct e as [p l h k].
    lets RP : reachable_ent_prot RE.
    lets PS : reachableProt_triple RP.
    inversion PS as [p1 p2 p3 B O L]; subst.
    lets LE : link_ent_soft_disc S.
    destruct LE as [EQ | [b ST]].
    - left. rewrite EQ. constructor. exact TP.
    - lets W : link_par_triple_discW_2 ST.
      destruct W as [EQ2 | [b' ST2]].
      + subst. left. constructor. constructor. assumption.
      + right. constructor. constructor.
        eapply tfsNext_prev; eassumption.
  Qed.
  ```

### `EntAuxResults.currEq_mode`

- **Where:** `src/EntAuxResults.v` line 50 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `missing-reachability`
- **Fix (audit summary):** Replace by a transition-local lemma (rangeBad m'' --chanMCurr<m>?--> step synchronises with stepMsOutCurr*, so m = currModeMState k); adding reachableEnt alone is not enough (see notes).

- **Status:** NEEDS-HYPOTHESIS (`reachableEnt e`), and then BLOCKED-ON-STUB (`reachableEnt`). Not refutable from the model axioms, but unprovable: it implies that `Mode` is a subsingleton.
- **Intent:** if the listener of an entity is in the `currEq m m''` state (it has just read the current mode `m` from the mode state on `chanMCurr` in `rangeBad m''`), then `m` is the entity's current mode.
- **Failure:** `currEqStateEnt m m'' e` constrains only the process term of `e` (`liftProcEnt (liftListen (fun p => p ~p~ currEq m m''))`). It says nothing about the mode state `k`, and `currModeEnt e = currModeMState k`. So for any `m1 m2 : Mode`, the entity
  `[| nilProc $||$ nilProc $||$ currEq m1 m1, mkPosition 0 0, mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil), sing m2 |]`
  satisfies `currEqStateEnt m1 m1 e` and has `currModeEnt e = m2`. Verified in Rocq (`--explore`, see `EntAuxResults.currEq_mode.v`):
  ```
  Lemma currEq_mode_cex :
    (forall m m'' e, currEqStateEnt m m'' e -> m = currModeEnt e) ->
    forall m1 m2 : Mode, m1 = m2.
  Proof.
    intros H m1 m2.
    apply (H m1 m1 ([| nilProc $||$ nilProc $||$ currEq m1 m1,
                       mkPosition 0%R 0%R, mkInterface (mkInputList nil) (mkOutputList nil) (mkNotifList nil), sing m2 |])).
    unfold currEqStateEnt, currEqStateProt. constructor. constructor.
    unfold currEqState. apply ProcEquiv.bisim_refl.
  Qed.
  ```
  `Mode` is an abstract `Axiom`, and the axioms don't force two distinct modes, so the statement is not refutable. But it is unprovable: a model with `Mode := bool` refutes it.
- **Ripple-up:** `grep -n currEq_mode` finds only `NARInsuff.v:220`, inside the commented-out old proof of `notifAbort_not_nextSince` (labelled `R`, currently `Admitted`). In that proof the entity comes from a reachable network (`rn : reachableNet n`). Not in the safety cone, so nothing live breaks.
- **Suggested fix:**
  ```
  Lemma currEq_mode m m'' e : reachableEnt e ->
    currEqStateEnt m m'' e -> m = currModeEnt e.
  ```
  This is still blocked while `reachableEnt` (EntAuxDefs.v:143) is an opaque `Parameter`. With `reachableEnt e` defined inductively as "reachable from an initial entity `[| initial protocol term, l, h, sing m0 |]` by entity discrete/delay steps (`-EA-`, delays)", the proof is an induction on reachability with an invariant of the form "listener in `currEq m m''` ⇒ `currModeMState k = m`". Base case: the initial listener is not in `currEq`. Step: the listener enters `currEq m m''` only via `rangeBad m''` reading `chanMCurr<vM>?`, which synchronises with `stepMsOutCurrSing`/`stepMsOutCurrTrans` and so reads exactly `currModeMState k`. **Caveat for the owner:** the invariant must also survive interleaved steps of the other two components while the listener sits in `currEq`. The only actions that change `currModeMState` are `chanMCurr @?` (`stepMsSwitch`, from `switchCurr`/`tfsCurr` outputs) and `chanMStable @?` (abort, which keeps the current mode). So the invariant must be strengthened to rule out the overlap/broadcast components emitting `chanMCurr!` while the listener is in `currEq`. On the `switchBc` path this holds because the listener is paused first (`chanPause!`). The `tfsCurr` path needs a separate argument. This strengthening is the real content of the proof once the stub is filled.
- **Partial proof:** none for the target itself. The counterexample helper above compiles.

### `EntAuxResults.ovAbort_unstable`

- **Where:** `src/EntAuxResults.v` line 53 · **Lemma** · 2015 label: `#inter-component` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt (inductive closure of initialEnt); prove by reachability induction with the strengthened overlap-band invariant from the write-up. Separately consider adding the missing WRITE-STBL entity rule (definition change).

- **Status:** BLOCKED-ON-STUB (`reachableEnt`, EntAuxDefs.v:143)
- **Intent:** if the overlap component of a reachable entity is in `ovAbort` (= `chanMStable!dormant`, about to abort the pending mode switch), then the entity's mode state is a transition state `<| m, m', t |>`. In other words, there is always a pending transition for `ovAbort` to abort (thesis §"overlap component": "Aborting a transition is achieved by the process ovAbort via an output on chanStable").
- **Failure:** the only hypothesis that could constrain `mstEnt e` is `reachableEnt e`, and that is an opaque `Parameter`. Nothing visible before the target concludes anything about the mode state from `reachableEnt`. The visible facts are `reachable_ent_prot` (admitted, which only gives `reachableProt p`) and `currEq_mode`, which is about the listener. `ovAbortStateEnt e` only constrains the process component (`liftProcEnt (liftOverlap ovAbortState)`).
  Reading `reachableEnt := fun _ => True` is consistent with every visible assumption, and under it the statement is false. **Verified in Rocq (explore check, compiled at the target's position):**
  ```coq
  Lemma ovAbort_unstable_cm (m : Mode) (p1 p3 : ProcTerm) (l : Position) (h : Interface) :
    ovAbortStateEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |]) /\
    ~ unstable (mstEnt ([| p1 $||$ ovAbort $||$ p3, l, h, sing m |])).
  Proof.
    split.
    - unfold ovAbortStateEnt, ovAbortStateProt. constructor. constructor.
      unfold ovAbortState. apply ComhCoq.ProcEquiv.bisim_refl.
    - simpl. intro U. inversion U.
  Qed.
  ```
  So the target cannot be proved while `reachableEnt` stays opaque.
- **Ripple-up:** **not** in the safety cone. Its only user is `ovAbort_urgent` (EntAuxResults.v:287-290, `lets OUS : ovAbort_unstable U U0`), and `grep -n ovAbort_urgent` finds no users of that lemma. Nothing above it breaks.
- **Suggested fix (stub definition; statement unchanged):** the reflexive-transitive closure of `initialEnt`, as in `NetAuxBasics.reachable_net_ent.fail.md`. Move the stub below `initialEnt` (EntAuxDefs.v:156):
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' d : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
- **Proof plan under that definition:** induct on `reachableEnt` with the strengthened invariant
  `Inv e := (exists m', initStateEnt m' e) \/ (exists m t x y, ovWaitStateEnt m t x y e) \/ (exists m t l, ovReadyStateEnt m t l e) \/ ovAbortStateEnt e \/ (exists m, switchBcStateEnt m e) \/ switchCurrStateEnt e  ->  unstable (mstEnt e)`.
  The overlap component must sit in one of these states throughout a pending switch.
  - *Init:* `initialProc` puts the overlap component in `dormant`, which is disjoint from all six states.
  - *Entering the band:* the only way in is `dormant --chanMNext<m'>?--> init m'`. At entity level that synchronises via `stepDeNextRead` with `k -ms- chanMNext .! m'`, and only `stepMsOutNext` provides that, so `k` is `<|m,m',t|>`. All other in-band moves (`init→ovWait→ovReady→ovWait`, `ovWait --chanAbort?--> ovAbort`, `ovWait --chanPause!--> switchBc`, `switchBc→switchCurr`) are process-internal taus, so they leave `k` unchanged. The backtracking lemmas needed are `ovlp_abort_in` (ProtAuxResults.v:905, admitted) for `ovAbort`, plus analogous `*_prev` facts for the other states.
  - *Mode state changes while in the band:* (i) delays keep a transition state a transition state (`stepMsDelTout`/`DelGuard`/`Timeout`); (ii) `stepDeTest`/`stepMsInit` only fire from a stable `k`; (iii) `stepMsSwitch` needs a process output `chanMCurr *!` (`stepDeCurrWrite`). Only `switchCurr` and `tfsCurr` emit that, and both are overlap states, so it can only happen as the exit `switchCurr → switchListen`, which leaves the band. (iv) `stepMsAbort` (`chanMStable @?`): see the finding below. It is currently unreachable, so it cannot break the invariant. Under a corrected semantics only `ovAbort → dormant` emits it, which also leaves the band. `bc_mStable_out_not` and `ovlp_mStable_out_not` (ProtAuxResults.v:914-918) cover the other components. The listener (`currOK`/`currComp`) only *inputs* `chanMStable`, via `stepDeRdStbl`, which needs a stable `k`, so it never fires in the band.
  - The target then follows from `Inv` applied to its `ovAbort` disjunct.
- **Side finding (definition discrepancy, worth a separate report):** `stepDiscEnt` (EntityLanguage.v:127-185) has **no WRITE-STBL rule**. The thesis (§4 entity semantics, around thesis.txt:5477) has `P --chanStable!--> P'`, `K --chanStable?--> K'` ⟹ `⟨P,l,I,K⟩ --τ--> ⟨P',l,I,K'⟩`. The Rocq code only has `stepDeRdStbl` (process *input*, mode-state *output*). As a result, the `ovAbort` output `chanMStable *!` and the `tfsNext` self-loop `chanMStable!` can never synchronise with the mode state's `stepMsAbort` (`<|m,m',t|> -ms- chanMStable @? -ms> m`), so an entity in `ovAbort` can never take its discrete step. `ovAbort_urgent` then forbids it from delaying. Proposed addition (needs owner approval: it is a definition change):
  ```coq
  | stepDeWrStbl : forall (p p' : ProcTerm) (l : Position)
    (i : Interface) (k k' : ModeState),
    p -PA- chanMStable *! -PA> p' -> k -ms- chanMStable @? -ms> k' ->
    [| p , l , i , k |] -EA- aeTau ->> [| p' , l , i , k' |]
  ```
  The proof plan above holds with or without this rule.
- **Partial proof:** none for the target itself (`introz U.` leaves `U : reachableEnt e`, `U0 : ovAbortStateEnt e` ⊢ `unstable (mstEnt e)`, with no usable facts about `U`). The counter-model helper above compiles.

### `EntAuxResults.tfsCurr_failSafe`

- **Where:** `src/EntAuxResults.v` line 58 · **Lemma** · 2015 label: `#inter-component` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add reachableEnt e, drop the unused (m : Mode) parameter, define nextModeEnt; additionally forbid process-internal synchronisation on chanMNext/chanMCurr/chanMStable, otherwise even the reachable version is false.

- **Status:** BLOCKED-ON-STUB (`nextModeEnt`), plus NEEDS-HYPOTHESIS (`reachableEnt e`, itself a stub). There is also a modelling issue: the statement is still false for reachable entities under the intended definition, because overlap and listener can synchronise internally on `chanMNext`.
- **Statement (frozen, `src/EntAuxResults.v:58`):**
  ```coq
  Lemma tfsCurr_failSafe (e : Entity) (m : Mode) :
    tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m.
  ```
  (The parameter `m` is unused. The existential shadows it.)
- **Intent:** when the overlap component is in `tfsCurr`, it has just written `failSafeSucc m` to the mode state on `chanMNext`. So the mode state is `<| m, failSafeSucc m, t |>`, and its next mode is fail-safe.

## Failure

1. **Opaque stub.** `nextModeEnt : Mode -> Entity -> Prop` is a `Parameter` (`EntAuxDefs.v:146`). Before the target, only one lemma in scope mentions it: `nextModeEnt_not_stable`, which is an elimination lemma and is on the harness's forbidden (inconsistent) list. `NetAuxBasics.v:906` is not imported here. Nothing in scope can introduce `nextModeEnt`. Instantiating it as `fun _ _ => False` refutes the statement, because `tfsCurrStateEnt` is inhabited. So it can't be proved while the stub is opaque.

2. **False under the intended definition when there is no reachability hypothesis** (verified in Rocq). Take the definition from the stub's comment:
   ```coq
   Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
     | nme p l h m t : nextModeEnt m' ([| p, l, h, <| m, m', t |> |]).
   ```
   The entity `[| nilProc $||$ tfsCurr $||$ nilProc, l, h, sing m |]` is in `tfsCurrStateEnt` and has a stable mode state, so it has no next mode. This is `tfsCurr_failSafe_cex` in `EntAuxResults.tfsCurr_failSafe.v`, which compiles.

3. **Still false for reachable entities: internal `chanMNext` synchronisation** (the step is verified in Rocq; the reachability path is argued informally because `reachableEnt` is a stub). `tfsNext m` offers `chanMNext<failSafeSucc m>!`. The listener states `currOK m''` and `currComp m'' r` offer `chanMNext<vM'>?`. The process-level `$||$` allows `stepDpSyncLR` between them, and `stepDeProcTau` lifts that to an entity τ-step that **does not touch the mode state**. The overlap then reaches `tfsCurr` with mode state `sing m`. Two lemmas in the `.v` file establish this:
   - `tfsCurr_failSafe_bypass` proves `[| nilProc $||$ tfsNext m $||$ currOK m'', l, h, sing m |] -EA- aeTau ->> [| nilProc $||$ liftNameProc tfsCurrN $||$ q3, l, h, sing m |]`, and that the target is in `tfsCurrStateEnt`.
   - `tfsCurr_failSafe_unfold` proves `liftNameProc tfsCurrN ~p~ tfsCurr`.

   A plausible trace from `initialEnt` reaches the source state, starting from `[| sleeping $||$ dormant $||$ listening, l, h, m0 |]`:
   1. The listener takes an `chanAN` notification with mode `m0` and an insufficient range, then reads `chanMCurr` and reaches `currEq m0 m0`, then `badOvlp`.
   2. `chanBad!` synchronises with `dormant`'s `chanBad?`. The overlap moves to `tfsStart` and the listener to `listening`.
   3. The overlap reads `chanMCurr`. It is now in `tfsNext m0`.
   4. The listener takes another notification with mode `m'' <> m0` and an insufficient range, and reaches `currOK m''`. The `gotMsg`→`currComp` path also works.
   5. The internal `chanMNext` sync moves the overlap to `tfsCurr` while the mode state is still `sing m0`.

   With any definition of `nextModeEnt` that reads the mode state, the conclusion fails at this point.

## Ripple-up

- Not in the safety cone (per `show`).
- The only consumer is the planned proof of `EntAuxResults.tfsBc_failSafe` (line 69, label `C`, currently `introz U. Admitted.`). The proof sketch comment says to backtrack to `tfsCurr` and then apply this lemma. `tfsBc_failSafe` is used in `NARNonFS_currSince.v:176`. The planned proof route of `tfsBc_failSafe` via this lemma breaks. `tfsBc_failSafe` itself may survive. In the bypassed state, `tfsCurr`'s `chanMCurr!` is an empty output that needs `stepMsSwitch` on a *transitional* mode state, so the overlap can't reach `tfsBc` from mode state `sing m0` (barring a similar internal capture).

## Suggested fix

1. Define the stub as its comment describes (inductive on `<| m, m', t |>`, as above). Define `reachableEnt` as the reflexive-transitive closure of `initialEnt` under the entity transitions.
2. Add reachability and drop the unused parameter. This requires approval, because it changes the statement:
   ```coq
   Lemma tfsCurr_failSafe (e : Entity) :
     reachableEnt e -> tfsCurrStateEnt e -> exists m, nextModeEnt m e /\ failSafe m.
   ```
3. **And** stop processes from capturing mode-state channels internally. Either:
   - restrict `stepDpSync*` (or `stepDeProcTau`) so the channels `chanMNext`, `chanMCurr`, `chanMStable` never synchronise between process components; or
   - give the listener separate read channels from the overlap's write channels.

   Without (3), the statement in (2) is still false, by the trace above.

With (1)–(3), the proof is a reachability induction with this invariant: overlap in `tfsCurr` → mode state is `<| m, failSafeSucc m, t |>`. Entry happens only via `stepDeNextWrite` from `tfsNext` (`stepMsInit` with `failSafeSucc_successor`). While in `tfsCurr`, only the overlap could abort or switch the mode state (`chanMStable!`/`chanMCurr!`), the listener only reads it, and delays keep the transitional shape. `failSafeSuccFS` then gives `failSafe`.

## Partial proof

See `EntAuxResults.tfsCurr_failSafe.v` in this directory, copied from `EntAuxResults-1` and re-verified with `--explore` (rc=0). Its HELPERS hold the compiled demonstrations `tfsCurr_failSafe_nextModeEnt`, `tfsCurr_failSafe_cex`, `tfsCurr_failSafe_unfold` and `tfsCurr_failSafe_bypass`. The PROOF section is `Admitted`.

### `EntAuxResults.tfsNext_currMode`

- **Where:** `src/EntAuxResults.v` line 78 · **Lemma** · 2015 label: `Proof: Induction on reachableEnt.` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `bisim-state-param-tracking`
- **Fix (audit summary):** Restate as failSafeSucc (currModeEnt e) = failSafeSucc m (all tfsNext_urgent needs: k0 -mtr-> failSafeSucc m), with reachableEnt defined; or track the literal overlap derivative instead of a bisimulation class.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`)
- **Intent:** in a reachable entity whose overlap component is in `tfsNext m`, the mode state's current mode is `m`. The overlap entered `tfsNext m` by reading `m` on `chanMCurr` from `tfsStart`, and nothing can change the current mode while it stays there.
- **Failure:** `reachableEnt` is an opaque `Parameter` (EntAuxDefs.v:143). The only fact about it visible before the target is the admitted `reachable_ent_prot : reachableEnt [|p,l,h,k|] -> reachableProt p`, which says nothing about the mode state `k`. `tfsNextStateEnt m e` (`liftProcEnt (liftOverlap (tfsNextState m))`) constrains only the process. So the statement is independent of the current context. Take the interpretation `reachableEnt [|p,l,h,k|] := reachableProt p`, which satisfies `reachable_ent_prot`, and the entity `[| p, l, h, sing m1 |]` where `p` is a reachable protocol term with its overlap in `tfsNext m2` and `m1 <> m2`. That entity satisfies both hypotheses and refutes the conclusion. No proof can exist until the stub is defined.
- **Ripple-up:** not in the safety cone. Its only user is `EntAuxResults.tfsNext_urgent` (EntAuxResults.v:251), which is used by `NARMisc.v:363`. `NetAuxBasics.tfsNext_currModeNet_eq`'s suggested fix (see NetAuxBasics-6's fail note) also relies on it. The statement is true under the intended definition, so nothing breaks up the chain once `reachableEnt` is defined.
- **Suggested fix (definition of the stub, as its comment says: reflexive-transitive closure of `initialEnt`):**
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  (`initialEnt` must be moved above it, or the definition placed after `initialEnt`.)
  **Proof plan under this definition** (no strengthened invariant needed). Induct on `reachableEnt e`.
  1. *Init:* `initialProc p` forces `p = procProtocol`, whose overlap is `dormant`, not `tfsNext`. Contradiction.
  2. *Discrete step `e -EA- a ->> e'`:* `tfsNext_prev_ent` gives `tfsNextStateEnt m e \/ tfsStartStateEnt e`.
     - Previous state `tfsStart`: only `tfsStart`'s `chanMCurr<vM>?` input leads to `tfsNext`, so the entity step is `stepDeCurrRead` with `k -ms- chanMCurr .! m' -ms> k'`. Both `stepMsOutCurrSing` and `stepMsOutCurrTrans` force `m' = currModeMState k = currModeMState k'`, and the new overlap state is `tfsNext m'`, so `m = m'`.
     - Previous state `tfsNext m`: by IH `currModeEnt e = m`. By `curr_switch_mState`, the current mode can change only through `chanMCurr @?`, that is, entity rule `stepDeCurrWrite`. That rule needs the process to output `chanMCurr *!`, which only `switchCurr`/`tfsCurr` (overlap) can do, and the overlap is in `tfsNext`. Every other entity rule leaves `k` unchanged or moves it by an MState step that keeps the first component (`stepMsAbort`, `stepMsInit` via `stepDeTest`/`stepDeNextWrite`, the outputs). So `currModeEnt e' = m`.
  3. *Delay step:* every `stepMsDel*`/`stepMsTimeout` rule keeps the first component of the mode state. The process is still `tfsNext m`, by delay preservation of the overlap state or by urgency.
  A process-level lemma "`tfsNextStateProt m p -> ~ p -PA- chanMCurr *! -PA> p'`" is the only new ingredient beyond existing tracking lemmas.
- **Partial proof:** none. The target is not provable while `reachableEnt` is opaque.

### `EntAuxResults.switchCurr_mState`

- **Where:** `src/EntAuxResults.v` line 92 · **Theorem** · 2015 label: `D- reachableEnt` · **in safety cone:** no
- **Audit:** BLOCKED-ON-STUB · root cause: `stub`
- **Fix (audit summary):** Define reachableEnt; prove with the strengthened init/ovWait/ovReady/switchBc invariant (d <= x etc.) from the write-up.

- **Status:** BLOCKED-ON-STUB (`reachableEnt`)
- **Intent:** in a reachable entity whose overlap component is in `switchCurr`, the mode state is mid-transition and its timer has run out: `mstEnt e = <| m, m', zeroTime |>`. Thesis Listing 7.27 gives the same property as "next mode is m'". Its purpose is urgency: `<|m,m',0|>` is exactly the mode state that can input `chanMCurr @?` (`stepMsSwitch`, `mst_tout_mCurr_in`), which matches the `chanMCurr *!` output of `switchCurr`. That is how `swithcCurr_urgent` (EntAuxResults.v:342) uses it.
- **Failure:** `reachableEnt` is an opaque `Parameter` (EntAuxDefs.v:143). `Print reachableEnt` gives `*** [ reachableEnt : Entity -> Prop ]`. After `intros R S; inversion S`, the explore check shows this goal:
  ```
  R : reachableEnt ([|p, l, h, k|])   SP : switchCurrStateProt p
  ============================
  exists m m', mstEnt ([|p, l, h, k|]) = <| m, m', zeroTime |>
  ```
  The goal is about the mode-state component `k`. In scope, the facts that eliminate `reachableEnt` are all admitted:
  - `reachable_ent_prot` (process only, says nothing about `k`);
  - `ovAbort_unstable` and `tfsNext_currMode`, whose hypotheses need the overlap component in `ovAbort`/`tfsNext`, which is disjoint from `switchCurr`.

  So the statement is independent of the context. Consider the interpretation
  `reachableEnt [|p,l,h,k|] := reachableProt p /\ (ovAbortStateProt p -> unstable k) /\ (forall m, tfsNextStateProt m p -> currModeMState k = m)`.
  It satisfies all three admitted facts. It also admits `[| p, l, h, sing m |]` with `p` a reachable protocol term whose overlap is in `switchCurr`. Such a `p` exists: `reachableProt` lets the process take `chanMNext?`/`chanMCurr?`/`chanPause!`/`chanWake!` steps alone, without a mode-state partner. That entity refutes the conclusion. No proof can exist until the stub is defined.
- **Ripple-up:** not in the safety cone (`show`: `in_safety_cone=False`). Its only user is `EntAuxResults.swithcCurr_urgent` (EntAuxResults.v:347, `lets SMS : switchCurr_mState U U0`), which has no further textual users in the frozen sources. The `NARNonFS_currSince.v:180` site builds a `switchCurrStateEnt` but doesn't call this lemma. The statement is true under the intended definition (below), so nothing breaks up the chain once the stub is filled.
- **Suggested fix:** define the stub as in the sibling notes (`w1b-11/EntAuxResults.reachable_ent_prot.fail.md`, `w1b-05/EntAuxResults.tfsNext_currMode.fail.md`), i.e. the reflexive-transitive closure of `initialEnt`. The stub must move below `initialEnt`:
  ```coq
  Inductive reachableEnt : Entity -> Prop :=
    | reachEntInit e : initialEnt e -> reachableEnt e
    | reachEntDisc e e' a : reachableEnt e -> e -EA- a ->> e' -> reachableEnt e'
    | reachEntDel e e' (d : Delay) : reachableEnt e -> e -ED- d ->> e' -> reachableEnt e'.
  ```
  The statement itself needs no change.

  **Proof plan under that definition.** Unlike `tfsNext_currMode`, direct induction is too weak. The 2015 comment says this needs a strengthened invariant covering the whole overlap "transition" path, proved by one induction on `reachableEnt`. Writing `k = mstEnt e`, `p = procEnt e`:
  ```
  Inv(e) :=
     (initStateProt m' p             -> exists m d, k = <|m, m', d|> /\ d <= modeTransTime m m' _)
  /\ (ovWaitStateProt m' t x y p     -> exists m d, k = <|m, m', d|> /\ d <= x /\ d <= t - period m' + y)
  /\ (ovReadyStateProt m' t l p      -> exists m d, k = <|m, m', d|> /\ d <= t - period m')
  /\ (switchBcStateProt m' p         -> exists m, k = <|m, m', zeroTime|>)
  /\ (switchCurrStateProt p          -> exists m m', k = <|m, m', zeroTime|>)
  ```
  The target is the last conjunct. Cases:
  1. *Init:* `procProtocol`'s overlap is `dormant`, so every conjunct is vacuous.
  2. *Entering `init m'`:* only via `dormant`'s `chanMNext<vM'>?`. This syncs with the mode state's `stepMsOutNext`, which needs `k = <|m, m', d|>`. That `d` came from `stepMsInit` (`= modeTransTime m m' p`) and has only decreased since (`stepMsDel*`/`stepMsTimeout`). Carrying `d <= modeTransTime` in the `dormant` case needs one more conjunct: dormant with a transitional `k` has `d <= modeTransTime`. The same invariant holds for every transitional `k`, and can be kept as a separate global conjunct.
  3. *`init` → `ovWait(m', T, T, 0)`* with `T = waitTime m m' _ + period m'` and `m` read from `chanMCurr` (`stepMsOutCurrTrans`, so `m = currModeMState k`). Then `d <= modeTransTime <= waitTime = T - period m'` by `timeMax` in `waitTime`. Matching the two `m -mtr-> m'` proofs needs the existing `proof_irrelevance`-based fact (ComhBasics.v:673) or equivalent.
  4. *`ovWait` delays by δ:* `d`, `x`, `y` all drop by δ (saturating at 0) and `t` is fixed, so both inequalities are preserved.
  5. *`ovWait` → `ovReady(m', t, l)`* when `y = 0`: `d <= t - period m'`.
  6. *`ovReady` → `ovWait(m', t - p, t - p, p)`* with `p = period m'`: `d <= t - p` gives both conjuncts.
  7. *`ovWait` → `switchBc m'`* via `$<x>$chanPause!`, enabled only when `x = 0`, so `d = 0`.
  8. *`switchBc` → `switchCurr`* via `chanWake!`: `k` is unchanged. Delays keep `<|m,m',0|>` (`delMStateTout`).
  9. *Frame:* while the overlap is in any of these states, `k` can lose its transitional form only by `chanMStable @?` (needs `ovAbort`/`tfsNext` outputting `chanMStable *!`) or `chanMCurr @?` (needs `switchCurr`/`tfsCurr` outputting `chanMCurr *!`). `stepMsInit` needs a stable `k`. Only the overlap component emits these outputs, and in cases 2–8 it isn't in such a state, except `switchCurr` itself, which leaves the invariant's scope on that step.

  The only new process-level ingredients are "which overlap states can output `chanMStable`/`chanMCurr`" and "the `$<x>$` guard is enabled only at `x = 0`". The existing backtracking (`*_prev_ent`) and urgency tactics should cover the rest.
- **Partial proof:** none possible while the stub is opaque. The explore script that confirms the goal shape is in `EntAuxResults.switchCurr_mState.v`.

### `EntAuxResults.tfsListen_paused`

- **Where:** `src/EntAuxResults.v` line 114 · **Lemma** · 2015 label: `C` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:false-invariant (listener is not paused on the fail-safe path)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete it (needs owner approval) and re-prove tfsListen_urgent from del_listening_pre plus the tfsListen_abort_in/bad_in/unpause_out activation lemmas.

- **Status:** FALSE (counterexample; and still false with a reachability hypothesis added)
- **Intent:** a helper for `tfsListen_urgent`: "when the overlap component is in `tfsListen`, the listener
  component is `paused`", so the overlap's `chanUnpause!` can synchronise with the listener's
  `chanUnpause?`, which by maximal progress rules out delay.
- **Failure:**
  1. *As stated (no hypothesis on p1, p3):* trivially false. `nilProc $||$ tfsListen $||$ nilProc` satisfies
     `tfsListenStateProt`, but `nilProc` is not bisimilar to `paused` (`paused` enables `chanUnpause *?`,
     `nilProc` enables nothing). Rocq-verified: `tfsListen_paused_cex` in
     `EntAuxResults.tfsListen_paused.cex.v` (Qed in explore mode; adapted from EntAuxResults-2's attempt).
  2. *Adding `reachableProt (p1 $||$ p2 $||$ p3)` does not rescue it.* The listener is only ever paused by
     `ovWait`'s `chanPause!`, i.e. during a *mode switch* (`switchBc/switchCurr/switchListen`). The
     fail-safe path `dormant/ovWait --bad?--> tfsStart -> tfsNext -> tfsCurr -> tfsBc --trans!--> tfsListen`
     never pauses the listener. The thesis says so itself: Example 5.13 (thesis.txt ~l.7041-7050) gives the
     reachable configuration `sleeping | tfsListen | listening` and explains that `listening`'s self-loop
     `cUnpause? qlistening` exists precisely to absorb `tfsListen`'s `cUnpause!`.
     In Rocq I proved (relative to the admitted thesis lemma `ProtAuxResults.paused_switch`, the only
     non-model admitted assumption):
     ```
     Lemma tfsListen_paused_reach_contra p :
       reachableProt p -> tfsListenStateProt p -> pausedStateProt p -> False.
     ```
     (proof in the `.cex.v`: `paused_switch` turns `paused` into `switchState`; `tfsListen` enables
     `chanAbort *?`, none of `switchBc m`/`switchCurr`/`switchListen` does). So the reachable version of the
     lemma would be equivalent to "`tfsListen` is unreachable", contradicting Example 5.13.
- **Ripple-up:** `grep`: only user is `EntAuxResults.tfsListen_urgent` (l.242), which is itself used by
  `NARMisc.v:371`. `show` reports `in_safety_cone=False`. `tfsListen_urgent` is (as far as the thesis goes)
  *true*, but its current proof route through this lemma is unsound.
- **Suggested fix:** delete `tfsListen_paused` (statement change needs owner approval) and re-prove
  `tfsListen_urgent` along the thesis's own sketch (Listing 7.28 and the `del_ovlp` comment): use
  `del_listening_pre` (EntAuxResults l.405, currently *after* `tfsListen_urgent`, so one of the two must be
  moved). It gives listener ∈ {abortOvlp, badOvlp, listening, paused}; in each case a synchronisation with
  `tfsListen` exists: `abortOvlp` outputs `chanAbort *!` vs `tfsListen_abort_in`; `badOvlp` outputs
  `chanBad *!` vs `tfsListen_bad_in`; `listening` and `paused` input `chanUnpause *?` vs
  `tfsListen_unpause_out`. If a protocol-level replacement helper is wanted, a true one is:
  ```
  Lemma tfsListen_listener_sync p3 :
    abortOvlpState p3 \/ badOvlpState p3 \/ listeningState p3 \/ pausedState p3 ->
    discActEnabled p3 (chanAbort *!) \/ discActEnabled p3 (chanBad *!) \/
    discActEnabled p3 (chanUnpause *?).
  ```
  (each disjunct by `activation_tac`, cf. `paused_unpause_in`), which together with `del_listening_pre`
  and the existing `tfsListen_*_in/out` lemmas suffices for `tfsListen_urgent`.
- **Partial proof:** none possible; see `EntAuxResults.tfsListen_paused.cex.v` for both Rocq-checked refutations.

### `EntAuxResults.gotMsgStateEnt_urgent`

- **Where:** `src/EntAuxResults.v` line 201 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Restore the thesis noComm clause forall l, a <> chanPos;?[basePosition l] inside EntityLanguage.noSyncNow (definition change, needs approval); the target is then provable without reachableEnt (validated on a local copy: gotMsgStateEnt_urgent_fixedA).

- **Status:** FALSE (counterexample) for every faithful definition of the `reachableEnt` stub. The root cause is BLOCKED-ON-DEFINITION: `EntityLanguage.noSyncNow` leaves out the `chanPos` clause of the thesis's `noComm` (Def. 4.22). As stated, the lemma also depends on the opaque stub `reachableEnt`. The only route to a proof inside the frozen development goes through `reachable_ent_prot` and `reachableProt_triple`. That route is vacuous, because `reachableProt_triple` is refutable (see `w1b-14/ProtAuxResults.reachableProt_triple.fail.md`). The prior attempt `EntAuxResults-2/EntAuxResults.gotMsgStateEnt_urgent.vacuous.v` uses exactly that route: it gets `listenerState` for a gotMsg process, which is impossible. Don't accept it.

- **Intent:** an entity whose listener is in `gotMsg m l` (it has just taken a message off `chanInProc` and now has to read its own position on `chanPos`) is urgent, meaning it cannot delay. In the thesis this holds because position reads are always available (rule POS-READ), and `noSyncEnt`/`noComm` forbid delay whenever `P` can input on `chanPos`.

- **Failure:** the Rocq delay rule `stepTeDel` requires only `noSync p i k d`. Its `noSyncNow a p i k` checks only whether `p` can synchronise with the interface `i` or the mode state `k`. A `chanPos` read is a tau via `stepDePosRead`, which involves neither `i` nor `k`, so it never blocks a delay. At process level, `inPrefix` delays freely (`stepTpIn`). Hence a gotMsg entity can delay whenever its other components can.
  Mechanised in `EntAuxResults.gotMsgStateEnt_urgent.cex.v` (HELPERS; compiles under `--explore`). `Print Assumptions` lists only model axioms (`Mode`, `failSafeSucc`, `failSafeSuccFS`, `speedMax`, …) plus stdlib classical reals, FE and PI. No admitted lemma is used.
  ```coq
  Lemma gotMsgStateEnt_urgent_false (R : Entity -> Prop) (m0 : Mode) :
    (forall e, initialEnt e -> R e) ->
    (forall e e' a, R e -> e -EA- a ->> e' -> R e') ->
    ~ (forall (e e' : Entity) (d : Delay) m l,
         R e -> gotMsgStateEnt m l e -> e -ED- d ->> e' -> False).
  ```
  So the target fails for **any** `R` that contains the initial entities and is closed under discrete entity steps. That includes the stub's documented intent ("reflexive transitive closure of initialEnt under entity transition relations"). Witness:
  1. Start from `e0 = [| procProtocol, origin, I1, failSafeSucc m0 |]`, where `I1` has one incoming message `[m0, origin]` stamped `0`. This is `initialEnt`, since `initialEnt` allows any interface.
  2. One `aeTau` step (`stepDeIOInterProc`): `listening` inputs on `chanInProc` and the interface forwards, giving `e1 = [| sleeping || dormant || X, origin, I∅, failSafeSucc m0 |]`. Here `X` is the substituted `gotMsgN([m0, origin])` and `I∅` is the empty interface.
  3. `X ~p~ gotMsg m0 origin` (`gotMsgStateEnt_urgent_X_bisim`), so `gotMsgStateEnt m0 origin e1`.
  4. `e1 -ED- 1 ->> [| sleeping || dormant || gotMsg m0 origin, origin, I∅, failSafeSucc m0 |]` with `delta = origin`. Every discrete action of `sleeping || dormant || X` is an input on `chanWake`, `chanTrans`, `chanMNext`, `chanAbort`, `chanBad` or `chanPos`. The interface outputs only on `chanInProc`/`chanAN`, and a stable mode state outputs only on `chanMCurr`/`chanMStable`, so `noSync` holds. The `stepTpPar` sort side conditions hold because all three components are inputs only.

- **Ripple-up:** used only by `EntAuxResults.msgAbortPathEnt_urgent` (gotMsg case) → `NARMisc.msgAbortPathNet_urgent` → `NARIncomp.v:351`. **Not in the safety cone.** The same root cause very likely also falsifies `msgAbortPathEnt_urgent`. In its gotMsg case the mode state is unstable, but with the overlap in `ovWait` behind a running `$<y>$` guard nothing synchronises. I didn't mechanise this, because building concrete `possiblyIncompatible` modes needs more than the abstract axioms give. More broadly, the missing clause lets *any* entity whose only enabled software action is a `chanPos` read idle: `gotMsg`, and `bcWait`/`ovWait` once their `$<x>$`/`$<y>$` guards have expired. Timeliness arguments that rely on position reads being immediate (broadcast within `period`, `ovReady` timing) are therefore unsupported by the current semantics too.

- **Suggested fix (definition change; needs owner approval):** restore the thesis's `noComm` clause `∀l, ¬ P --chanPos⟨l⟩?-->`.
  - **A (faithful to the thesis, preferred):** in `EntityLanguage.v`,
    ```coq
    Definition noSyncNow (a : DiscAct) (p : ProcTerm)
      (i : Interface) (k : ModeState) : Prop :=
      discActEnabled p a ->
      (~discActEnabledInter (a^) i /\ ~discActEnabledMState (a^) k) /\
      (forall l : Position, a <> chanPos ;? [basePosition l]).
    ```
    `noSync` and `stepTeDel` stay unchanged. Because the clause sits inside `noSyncNow`, it is also enforced at every intermediate point of a delay, which is needed for timed guards that expire mid-delay. With this change the target is provable **without** using `reachableEnt` at all. This is validated in the `.cex.v` on a local copy of the fixed rule (`gotMsgStateEnt_urgent_noSyncNowA` / `_noSyncA` / `_delA`):
    ```coq
    Lemma gotMsgStateEnt_urgent_fixedA (e e' : Entity) (d : Delay) m l :
      gotMsgStateEnt m l e -> gotMsgStateEnt_urgent_delA e d e' -> False.
    ```
    The proof is 5 lines: invert the delay, instantiate `noSync` at `chanPos ;? [basePosition l]`, and use `activation_tac` to show that gotMsg enables that read. Only model axioms are used. The cost: the 6 or so sites that destructure `noSyncNow` (`EntAuxResults.v` 226/257/280/297/355, the tactics in `EntityLanguage.v` 370–394, and `NetAuxBasics.v` 664–710) need `[[NI NM] _]` instead of `[NI NM]`.
  - **B (less invasive):** leave `noSyncNow` alone and add a premise `noPosRead p d` to `stepTeDel`, where
    ```coq
    Definition noPosRead (p : ProcTerm) (d : Delay) : Prop :=
      forall l : Position, ~ discActEnabled p (chanPos ;? [basePosition l]) /\
      (forall p' (d' : Delay), d' < d -> p -PD- d' -PD> p' ->
         ~ discActEnabled p' (chanPos ;? [basePosition l])).
    ```
    The target's proof is the same. Proofs that only invert delays are unaffected apart from auto-generated hypothesis names. Proofs that construct entity delays must discharge `noPosRead`.
  - Either way the target can keep its statement, and the `reachableEnt e` hypothesis becomes unused.

- **Partial proof:** none for the statement as given, since it is refuted. The counterexample, the fix validation and the reusable helpers are all in `EntAuxResults.gotMsgStateEnt_urgent.cex.v`. Reusable pieces:
  - the `gotMsgStateEnt_urgent_vareq` tactic, which evaluates the opaque `varEqDec` tests left by `subProcTerm`/`listsToSub`, making `gotMsgN $(args)$` unfoldings literal;
  - the "non-variable-only" inversion loop `gotMsgStateEnt_urgent_inv`;
  - `gotMsgStateEnt_urgent_X_bisim`, an `app`-unfolding bisimulation pattern.

### `EntAuxResults.nextEq_mode`

- **Where:** `src/EntAuxResults.v` line 483 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `bisim-state-param-tracking` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Delete the state-invariant form and use a transition-local lemma (w1b-03's nextEq_mode_step: currOK -> step -> nextEq m' m'' -> nextModeMState k' = Some m'), plus define nextModeEnt.

- **Status:** BLOCKED-ON-STUB (`nextModeEnt`), and FALSE as stated under the stub's intended definition.
- **Intent:** if the listener of an entity is in the `nextEq m' m''` state (it has just read `m'` from the mode state on `chanMNext`), then the entity's mode state is in transition with next mode `m'`.
- **Failure:**
  1. `nextModeEnt` is an opaque `Parameter` (EntAuxDefs.v:146). Nothing usable constrains it. The only admitted fact that produces `nextModeEnt` for a specific mode is the blacklisted `nextModeEnt_not_stable`, and `tfsCurr_failSafe` only gives an existential. So the lemma can't be proved while the stub is opaque.
  2. Under the intended definition in the stub's comment ("mode state `<m, m', d>`, with `m'` the parameter"), the statement is false. `nextEqStateEnt m' m'' e` constrains only the software component and says nothing about the mode state. Counterexample: `e = [| nilProc $||$ nilProc $||$ nextEq m1 m2, l, h, sing m0 |]` satisfies `nextEqStateEnt m1 m2 e` because `bisim_refl` holds, but its mode state is stable. Verified in Rocq with `--explore`: `nextEq_mode_cex_intended` in `w1b-03/EntAuxResults.nextEq_mode.v` compiles with `Qed`. It uses a prefixed inductive `nextEq_mode_nextModeEntI m'` with the single constructor `[|p,l,h,<|m,m',d|>|]`. The earlier prover (`EntAuxResults-2/...cex.v`) showed the same with the opaque stub plus `nextModeEnt_not_stable`.
  3. Adding `reachableEnt e` probably doesn't fix it either. After the listener's `chanMNext` read (`currOK` → `nextEq`), `nextEq` is urgent but only blocks *time*. Another component can still act discretely before the listener's `nextEq` tau. For example, the overlap component can abort (`chanMStable @?` gives `stepMsAbort`, a stable mode state) or switch (`chanMCurr @?` on `<|m,m',0|>`). So as a state invariant, even of reachable entities, it is doubtful.
- **Ripple-up:** used only once, at NARInsuff.v:236. That line is inside the comment opened at NARInsuff.v:218 and closed at :314, part of the commented-out proof of `notifAbort_not_nextSince`. So no live proof depends on this lemma. Not in the safety cone. It is used with `nextMode_ent_mState` (also blocked on the stub) to turn `nextEqStateEnt x1 m' e'` into `nextModeMState k0 = Some x1`.
- **Suggested fix:** delete the state-invariant lemma and replace its single use with a *transition-local* fact. In NARInsuff, the listener step `currOK m'' → nextEq x1 m''` is a synchronisation on `chanMNext` with the mode state (`stepMsOutNext`, which leaves the mode state unchanged). So the needed fact is:
  ```coq
  Lemma nextEq_mode_step p l h k p' l' h' k' a m' m'' :
    currOKStateEnt m'' ([|p, l, h, k|]) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    nextEqStateEnt m' m'' ([|p', l', h', k'|]) ->
    nextModeMState k' = Some m'.
  ```
  It should be provable with `link_ent_proc_neq_disc` (case `p -PA- chanMNext ;? [baseMode m'] -PA> p'` paired with `k -ms- chanMNext .! m' -ms> k'`, where inversion gives `k = k' = <|_, m', _|>`) and the existing `currOK`/listener tracking lemmas. Separately, define `nextModeEnt m e := nextModeMState (mstEnt e) = Some m`, which makes `nextMode_ent_mState` trivial.
- **Partial proof:** none. The counterexample file is `w1b-03/EntAuxResults.nextEq_mode.v` (helpers section).

### `EntAuxResults.nextMode_ent_mState`

- **Where:** `src/EntAuxResults.v` line 487 · **Lemma** · 2015 label: `D` · **in safety cone:** no
- **Audit:** CONTRADICTS-ADMITTED · root cause: `stub` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Define the nextModeEnt stub (inductive on <|m,m',t|> or via EntityLanguage.nextModeEnt e = Some m), after which the proof is inversion or exact; and fix the partner lemmas tfsCurr_failSafe and nextEq_mode.

- **Status:** BLOCKED-ON-STUB (nextModeEnt)
- **Intent:** If an entity has next mode `m` (relation `nextModeEnt`), then its mode-state component is a transition state whose target is `m`, i.e. `nextModeMState k = Some m`. This is the elimination rule for the stub.
- **Failure:** `nextModeEnt : Mode -> Entity -> Prop` is an opaque `Parameter` (EntAuxDefs.v:146). Before the target, the only lemma with `nextModeEnt` in a hypothesis is `nextModeEnt_not_stable` (EntAuxResults.v:28), which is on the banned known-inconsistent list. Every other lemma (`tfsCurr_failSafe`, `nextEq_mode`) concludes `nextModeEnt`, so none of them eliminates it. Under the opaque stub, `nextModeEnt := fun _ _ => True` is a model of the context that refutes the target (take `k := sing m0`). The explore check shows the bare goal `H : nextModeEnt m ([|p,l,h,k|]) |- nextModeMState k = Some m`.
- **Ripple-up:** Not in the safety cone. Used once, at NARInsuff.v:237, to turn `nextEq_mode` into `nextModeMState k0 = Some x1` and derive a contradiction in a forward-tracking case. It is true under either definition below.
- **Suggested fix (stub definition):** one of the following. Both were checked in Rocq (explore, rc=0) against local prefixed copies in `EntAuxResults.nextMode_ent_mState.v`, where they are also proved equivalent (`nextMode_ent_mState_demo_equiv`).
  1. Per the "Idea" comment at EntAuxDefs.v:147. This matches `NetAuxBasics.nextMode_ent_ex.fail.md`:
     ```coq
     Inductive nextModeEnt (m' : Mode) : Entity -> Prop :=
       | nmeWitness p l h m t : nextModeEnt m' ([|p, l, h, <| m, m', t |>|]).
     ```
     Target proof: `intro U. inversion U; subst. reflexivity.`
  2. Reuse the existing, now-shadowed function `EntityLanguage.nextModeEnt : Entity -> option Mode` (EntityLanguage.v:92):
     ```coq
     Definition nextModeEnt (m : Mode) (e : Entity) : Prop :=
       EntityLanguage.nextModeEnt e = Some m.
     ```
     Target proof: `intro U. exact U.` (it is definitional). Renaming one of the two homonymous `nextModeEnt`s would avoid the shadowing altogether.
- **Related note:** both definitions refute `nextModeEnt_not_stable` *as written* (where `m2` is inferred as `ModeState`). They prove the `(m2 : Mode)`-annotated version by `inversion`/`discriminate` (`nextMode_ent_mState_demo_not_stable`, `..._demo2_not_stable`). See `EntAuxResults.nextModeEnt_not_stable.fail.md` for that lemma's write-up.

### `EntAuxResults.gotMsg_gotRange_track_ent`

- **Where:** `src/EntAuxResults.v` line 500 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `eSubtract-vs-bPossInc-typing`
- **Fix (audit summary):** Fix the range typing first (make (|vL,l'|) (-) speedMax (.) msgLatency evaluate to a baseDistance, or let bPossInc accept baseNonneg), then restate as w1b-06 suggests: reachable pre-state, conclusion l = l' /\ gotRangeStateEnt m (canonical range) e' instead of parameter equalities.

- **Status:** FALSE. Two independent reasons: (a) the state predicates are bisimulation classes, so `m'` and `r` are
  determined only up to bisimilarity; (b) there is no reachability hypothesis, so a foreign component can feed
  `chanPos`. The Rocq-checked part is the key indistinguishability fact (`gotMsg_gotRange_track_ent_indist` in
  the `.v`). The full counterexample needs a positive bisimilarity proof (sketched below), which I did not mechanise.
- **Intent:** when an entity steps from a listener in `gotMsg m l1` to a listener in `gotRange m' r`, the listener
  read the entity's own position `l` on `chanPos`. So `l = l'`, `m = m'` and `r = dist2d l l1 -nn- speedMax*msgLatency`.
- **Failure:**
  `gotRangeStateProt m' r p'` only says `p3' ~p~ gotRange m' r`, and `gotRange m'' r` uses `r` and `m''`
  **only** through `possIncBool x m'' r`, for an input mode `x`. That happens in `currPincCheck` (`bPossInc vM m'' r`) and in
  `nextPincCheck` (`bPossInc vM' m'' r`). Every other continuation (`listeningN`, `badOvlpN`, `abortOvlpN`) forgets them.
  Hence `gotRange m1 r1 ~p~ gotRange m2 r2` whenever `forall x, possIncBool x m1 r1 = possIncBool x m2 r2`.
  For non-mode inputs both guards fail to evaluate, so `evalBoolExpFunTot` gives `false` for both `b` and `!~b` on both sides.
  1. *`r` counterexample (honest step, no intruder):* take `l1 := l` (message from the receiver's own position), the
     listener `p3 := gotMsg m l` and the entity step `stepDePosRead` (reads `basePosition l`). The derivative is
     `gotRangeN [m, (|l, l| (-) speedMax (.) msgLatency)]`, whose distance argument evaluates to `0`.
     Let `eps := speedMax*adaptNotif > 0`. Then `possIncBool x m eps = possIncBool x m 0 = true` for **every** `x`, because
     `possIncDist x m >= 2*speedMax*adaptNotif`; this is Rocq-checked as `gotMsg_gotRange_track_ent_indist`.
     So `p3' ~p~ gotRange m eps`, and the hypotheses hold with `r := eps`. The conclusion would force `eps = 0`.
  2. *`m` counterexample:* in any model with two modes `m1 <> m2` such that `minDistComp x m1 = minDistComp x m2`,
     `period m1 = period m2` and `trans m1 = trans m2` for all `x`, `possIncBool x m1 r = possIncBool x m2 r` for all `x, r`.
     So `gotRange m1 r ~p~ gotRange m2 r`, and `m = m'` is unprovable. It is consistent with the axioms in
     `ComhBasics.v`, which never separate modes.
  3. *Intruder on `chanPos`:* without `reachableEnt`, `p1` may be `chanPos $<[eBase (basePosition l2)]>$! nilProc`.
     The `stepDpSyncLR` tau then feeds `l2 <> l` to the listener, so the true range is `dist2d l2 l1 - ...`, not `dist2d l l1 - ...`.
  Mechanising (1) needs one positive bisimilarity: `gotRangeN [em, e] ~p~ gotRange m' r'` for any closed `em, e`
  with `forall b, evalBoolExpFun (bPossInc b em e) = evalBoolExpFun (bPossInc b m' r')`. The proof is a cofix over
  the finite derivative set `gotRange -> currPincCheck -> {currComp -> nextPincCheck, badOvlp}`, including the
  timed residuals of the `ifThen` branches. It needs the substitution clean-up tactics (`clean_proc_hyp`,
  `remove_resets_hyp`), because `varEq` is opaque. I estimated 2-4 hours and stopped, since the target is outside the safety cone.
- **Side finding:** the admitted protocol-level lemma used at the call site, `ProtAuxResults.gotMessage_next`,
  is also false as stated. After `chanPos ;? [v]` with `v` **not** a position (e.g. `baseMode _`), the distance
  expression fails to evaluate. Then `currPincCheckN [..]` has both guards `false` and is stuck. Any `gotRange m'' r` with a real `r`
  can always take a branch after a mode input, so no `r` exists. `goMsg_gotRange_track` (`r = mkDistance ...` exactly) is
  false for reason (1).
- **Ripple-up:** not in the safety cone. Its only user is `NARIncomp.v:138` (`msgAbort_not_nextSince`), which uses
  `GGE` to rewrite `x1` (from `gotMessage_next`) into `dist2d l l' -nn- ...`, transferring the `possiblyIncompatible`
  facts of `mapMsg` to `mapGrng`.
- **Suggested fix:** state the conclusion with the canonical range instead of equating parameters. Add
  reachability to exclude foreign `chanPos` writers:
  ```
  Lemma gotMsg_gotRange_track_ent (m : Mode) (l l' l1 : Position)
    (p p' : ProcTerm) h h' k k' a :
    reachableEnt ([|p, l, h, k|]) ->
    gotMsgStateEnt m l1 ([|p, l, h, k|]) ->
    (exists m' r, gotRangeStateEnt m' r ([|p', l', h', k'|])) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    l = l' /\
    gotRangeStateEnt m (mkDistance (dist2d l l1 -nn- speedMax *nn* msgLatency)) ([|p', l', h', k'|]).
  ```
  At `NARIncomp.v:138`, apply `mapGrng` with this canonical `r` (and `m''`) directly instead of `x1`. The
  `possiblyIncompatible` side-conditions then match `mapMsg`'s `r'` syntactically. Reachability is available there
  (`rn`, via `reachable_net_ent`). This is provable once (i) `reachableEnt` is concrete
  (BLOCKED-ON-STUB `reachableEnt`), so the other two components never output on `chanPos`, and (ii) the
  "expression-vs-value" bisimilarity lemma above exists. `gotMessage_next` should similarly be restricted to
  `a = chanPos ;? [basePosition l']` and conclude `gotRangeState m'' (mkDistance (dist2d l' l -nn- ...)) p'`.
- **Partial proof:** `gotMsg_gotRange_track_ent_indist` (in the `.v`, compiles).

### `EntAuxResults.gotRange_currPincCheck_track_ent`

- **Where:** `src/EntAuxResults.v` line 511 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `bisim-state-param-tracking` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Replace parameter equalities with a forward-tracking conclusion (gotRangeStateEnt m2 r e' \/ currPincCheckStateEnt (currModeMState k) m2 r e') under reachableProt p, as in the w1b-16 write-up.

- **Status:** FALSE (counterexample, checked in Rocq). It needs any `m : Mode` and nothing else.
- **Intent:** if an entity whose listener is in `gotRange m2 r` takes a step into a state whose listener is in `currPincCheck m1' m2' r'`, then the step was the read of the current mode from the mode state. So the parameters carry over (`m2 = m2'`, `r = r'`) and the mode read is the current one (`m1' = currModeMState k`).
- **Failure:** the state predicates are **bisimilarity classes** (`currPincCheckState m m'' d p := p ~p~ currPincCheck m m'' d`), and bisimilarity can't tell parameters apart once the guard decides the branch. `currPincCheck x y z = (!~bPossInc x y z $> currCompN[y,z]) $+$ (bPossInc x y z $> badOvlpN)`. When `bPossInc x y z` evaluates to true:
  - the left summand is a false-guarded conditional, which has no discrete steps and idles under delay (`stepTpIfFalse`);
  - the right summand behaves like its body.

  So `currPincCheck x y z ~p~ badOvlpN` for **every** triple with `possiblyIncompatible x y z`. Since `possIncDist m m' >= 2*speedMax*adaptNotif > 0`, every distance below that bound is possibly incompatible for every pair of modes.

  **Counterexample:**
  - `e = [| nilProc $||$ nilProc $||$ gotRange m r0, l, h, sing m |]` with `r0 = 0`, and `e'` the same with the listener replaced by its `chanMCurr ;? [baseMode m]` derivative `currPincCheckN $([m, m, r0])$`. The step is `stepDeCurrRead` with `stepMsOutCurrSing`.
  - `gotRangeStateEnt m r0 e` holds by reflexivity.
  - `currPincCheckStateEnt m m r1 e'` holds for `r1 = speedMax*adaptNotif` (`<> 0`), because both terms are bisimilar to `badOvlpN`.
  - The conclusion then forces `r0 = r1`, i.e. `0 = speedMax*adaptNotif`, which contradicts `speedMax_pos` and `adaptNotif_positive`.

  This is `gotRange_currPincCheck_track_ent_cex` in `EntAuxResults.gotRange_currPincCheck_track_ent.v`, which closes with `Qed` in --explore. `Print Assumptions` lists only model axioms (`speedMax_pos`, `adaptNotif_positive`, `period_positive`, …) plus the stdlib classical/funext/proof-irrelevance axioms. **No admitted lemma is used.** Adding reachability doesn't help: any reachable entity in `gotRange m'' r` with small `r` (`r` is a truncated `-nn-` subtraction, so `0` is typical) gives the same failure.
  - A second, independent failure appears once `p1`/`p2` are arbitrary. With no reachability hypothesis, `p1` may output `chanMCurr ;! [baseMode m']` and synchronise internally with the listener (`stepDeProcTau`), so even `m1' = currModeMState k` fails for parameter-sensitive cases.
- **Ripple-up:** not in the safety cone. Its only user is `NARIncomp.msgAbort_not_nextSince` (NARIncomp.v:162, case 2 "gotRange"), which needs only the fact `x1 = currModeMState k0`, and only to turn `~possiblyIncompatible (currModeMState k0) m'' r` into `currCompState m'' r p3'` via `currPincCheck_cond_false`.
- **Same defect in siblings (same argument, same helper lemma `..._guard_sum`):**
  - `gotMsg_gotRange_track_ent` (`m = m'`, and `r = …`): `gotRange m r ~p~ gotRange m' r'` whenever `r, r' < 2*speedMax*adaptNotif`.
  - `currComp_nextPincCheck_track_ent` (`m2 = m2' /\ r = r' /\ nextModeMState k = Some m1'`): `nextPincCheck` has the same `!~B $> _ $+$ B $> _` shape.

  Equalities of parameters can **never** be derived from bisimilarity-class state predicates. Only positive state facts can.
- **Suggested fix:** replace the parameter equalities with a forward-tracking conclusion that states the derivative's state with the expected parameters, and add protocol reachability to rule out internal synchronisation:
  ```coq
  Lemma gotRange_currPincCheck_track_ent (m2 : Mode) (r : Distance)
    (p p' : ProcTerm) (l l' : Position) h h' k k' a :
    reachableProt p ->
    gotRangeStateEnt m2 r ([|p, l, h, k|]) ->
    [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    gotRangeStateEnt m2 r ([|p', l', h', k'|]) \/
    currPincCheckStateEnt (currModeMState k) m2 r ([|p', l', h', k'|]).
  ```
  - **Why it should be provable.** By inversion on the entity step and the parallel triple, either `p3' = p3`, which gives the left disjunct, or `p3` steps. In that case `gotRange m2 r`'s only steps are `chanMCurr ;? [v]` to `currPincCheckN $([v, m2, r])$`. The input either comes from the mode state (`stepDeCurrRead`, where both `stepMsOutCurrSing` and `stepMsOutCurrTrans` output `currModeMState k`), giving the right disjunct via `..._app_bisim`, or from an internal sync with `p1`/`p2`. The internal sync is excluded by a reachability invariant: in a reachable protocol the broadcast and overlap components only output on `chanMCurr` with the empty tuple (`switchCurr`, `tfsCurr`), and an arity mismatch blocks `stepDpIn`. That invariant can be proved by induction on `reachableProt` directly; it doesn't need the admitted, and probably over-strong, `reachableProt_triple`.
  - **Why it suffices for the user.** `msgAbort_not_nextSince` has `rn : reachableNet n`, so `reachable_net_prot` supplies `reachableProt`. In case 2, the left disjunct gives `mapGrng` directly, and the right disjunct gives `currPincCheck_cond_false H8` and then `mapCuco`. The detour through `gotRange_next` and the equalities is no longer needed.
- **Partial proof:** none for the stated lemma (it is false). The counterexample and reusable bisimulation helpers are in the HELPERS of `EntAuxResults.gotRange_currPincCheck_track_ent.v`: `_ifFalse_sum` (cofix), `_ifTrue`, `_guard_sum`, `_app_bisim` and `_pid`. They are demonstrations, not for splicing.

### `EntAuxResults.currComp_listening_track_ent`

- **Where:** `src/EntAuxResults.v` line 519 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `mode-chan-internal-sync` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Either restate to list every way currComp reaches listening (mode-state chanMStable read, chanMNext read with ~possiblyIncompatible, or internal chanMStable sync with the overlap) as in the w1b-01 write-up, or forbid internal sync on mode-state channels (definition change).

- **Status:** FALSE (counterexample). Two independent counterexamples, both checked in Rocq (`--explore`, rc=0) and closed under the model axioms plus stdlib axioms only, with no admitted lemmas. The second one is ordinary protocol behaviour, so adding `reachableEnt` would not rescue the statement.
- **Intent:** if the listener goes from `currComp m'' r` to `listening` in one entity step, then the step was the listener reading `chanMStable` from the mode state (RD-STBL). So the mode state was stable (`k -ms- chanMStable @! -ms> k'`) and the interface is unchanged.
- **Failure:** a listener in `currComp` can reach a state bisimilar to `listening` in two other ways. Neither involves the mode state outputting on `chanMStable`.
  1. **Internal sync with the overlap component** (`currComp_listening_track_ent_cex1`). The protocol's overlap states `tfsNext m` and `ovAbort` *output* on `chanMStable`; they are meant for WRITE-STBL, which aborts the mode state. The listener's `currComp` *inputs* on `chanMStable`. Inside `p1 $||$ p2 $||$ p3` these two synchronise to a process `tau` (`stepDpSyncLR`), and the entity takes `stepDeProcTau` with `k' = k`. Witness: `[| nilProc $||$ (chanMStable ! nilProc) $||$ currComp m'' r, l, h, <|m,m,zeroTime|> |] -EA- aeTau ->> [| nilProc $||$ nilProc $||$ listeningN, l, h, <|m,m,zeroTime|> |]`. A transitional mode state has no `chanMStable @!` step.
     This state also looks reachable. The listener goes badOvlp → `bad!` (the overlap moves to tfsStart → tfsNext) → listening → receives a message → gotMsg → gotRange → currPincCheck → currComp, while the overlap is still in tfsNext and the mode state is still transitional.
  2. **Reading the next mode when it is not possibly incompatible** (`currComp_listening_track_ent_cex2`). Take `k = <|m, m', t|>` and `~ possiblyIncompatible m' m'' r`, for example `r := possIncDist m' m''`. Then `currComp -chanMNext<m'>?->` gives `nextPincCheckN(m', m'', r)` via `stepDeNextRead` with `stepMsOutNext`, so `k' = k`. Because `bPossInc` evaluates to false, `nextPincCheck = (!~bPossInc $> listeningN) $+$ (bPossInc $> abortOvlpN)` is bisimilar to `listening`. The proof uses `cond_bisim_true`, `cond_bisim_false`, `choice_bisim_context` and `choice_bism_unit_r`. This is exactly the "conditional branch that evaluates to listening" that the ProtAuxDefs comment warns about. Again `k` cannot output `chanMStable`.
  The lemma `currComp_listening_track_ent_refuted` (from cex1) and the lemma `currComp_listening_track_ent_refuted2` (from cex2 with `r := possIncDist m m`) each prove `~ (statement)` for any `m : Mode`.
  The `h = h'` half *is* true: every way of reaching listening leaves the interface alone. Any step that leaves `p3` fixed would need `currComp ~ listening`, which fails because `listening` can do `chanPause *?`.
- **Ripple-up:** not in the safety cone. The only user is `NARIncomp.msgAbort_not_nextSince`, which is marked proved (sub-case 2 of the currComp case, NARIncomp.v:200). That proof currently rests on this false lemma.
  - The user has `possiblyIncompatible m' m'' r` and `nextModeMState k0 = Some m'`, so counterexample 2 is excluded there.
  - Counterexample 1 is not excluded. In that sub-case the overlap may sync on `chanMStable` and the listener ends in `listening` with `k0` unchanged, so the user's `false.` step cannot succeed.
  - The user's *statement* is probably still true. The overlap moved from tfsNext to tfsNext, or from ovAbort to dormant, so `~nextSinceStateNet i n'` (the right disjunct) should hold given reachability. Its proof must take the right disjunct in that sub-case instead of deriving a contradiction.
- **Suggested fix:** either of the following.
  (a) Correct the statement so that it lists every way the step can happen:
  ```coq
  Lemma currComp_listening_track_ent m'' r l l' p1 p2 p3 p' h h' k k' a :
    currCompStateEnt m'' r ([|p1 $||$ p2 $||$ p3, l, h, k|]) ->
    listeningStateEnt ([|p', l', h', k'|]) ->
    [|p1 $||$ p2 $||$ p3, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
    h = h' /\
    ( k -ms- chanMStable @! -ms> k'
    \/ (exists m', k -ms- chanMNext .! m' -ms> k' /\ ~ possiblyIncompatible m' m'' r)
    \/ (k = k' /\ exists p1' p2' p3', p' = p1' $||$ p2' $||$ p3' /\
          p1 $||$ p2 -PA- chanMStable *! -PA> p1' $||$ p2') ).
  ```
  This should be provable without reachability by the case analysis above. The ingredients are `currComp ≁ listening`, `nextPincCheck` with possInc true `≁ listening` (it is `~ abortOvlp`, which only does `chanAbort!`), and bisimulation transfer of `p3`'s step to `currComp`.
  For the user: disjunct 1 contradicts `unstable k0`, as now. Disjunct 2 forces `m'` to be the next mode and contradicts `possiblyIncompatible m' m'' r`. Disjunct 3 needs a small reachable-overlap lemma: an overlap state that outputs on `chanMStable` is tfsNext or ovAbort, so its derivative is not `nextSinceState`. That proves the right disjunct of `msgAbort_not_nextSince`.
  (b) Alternatively, change the definition. Give WRITE-STBL its own channel (overlap `chanMAbort!` against a mode-state `chanMAbort?`, plus the missing entity rule; the Rocq `stepDiscEnt` currently has RD-STBL but no WRITE-STBL rule), so that the overlap and listener cannot synchronise. Then add `nextModeMState k = Some m' -> possiblyIncompatible m' m'' r` as a hypothesis, or the second disjunct above. This is a model change and needs owner approval. The same overlap/listener `chanStable` sync is present in the thesis (§4, tfsNext/ovAbort `chanStable!` against currOK/currComp `chanStable?`).
- **Partial proof:** `(prover work area; evidence for audited targets is in `2026-10-14-proof-completion-pass-1-evidence/audit/`) EntAuxResults.currComp_listening_track_ent.v` holds both counterexamples, the two refutations, and the helpers `..._app_bisim` and `..._listeningN : listeningState listeningN`. The helpers can be reused for other `#fwd-track` and listening lemmas.

### `EntAuxResults.currComp_nextPincCheck_track_ent`

- **Where:** `src/EntAuxResults.v` line 526 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `mode-chan-internal-sync` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Forbid process-internal synchronisation on chanMNext/chanMCurr/chanMStable (definition change) and restate as in the w1b-05 write-up (premise nextModeMState k = Some m1, conclusion currComp unchanged \/ (nextPincCheckStateEnt m1 m2 r e' /\ k' = k)).

- **Status:** FALSE (counterexample, machine-checked). **The statement implies `Mode -> False`**, so it belongs on the known-inconsistent list next to `nextModeEnt_not_stable` etc.
- **Intent:** if the listener goes from `currComp m2 r` to `nextPincCheck m1' m2' r'` in one entity step, then the step was the listener reading the next mode `m1'` from the mode state over `chanMNext`. So the parameters carry over (`m2 = m2'`, `r = r'`) and the mode state is unstable with next mode `m1'`.
- **Failure (main, verified):** the process semantics (`stepDpSyncLR/RL`, SoftwareLanguage.v) lets *any* two parallel components synchronise on *any* channel, mode-state channels included. The overlap state `tfsNext m` outputs `chanMNext<eFailSafeSucc m>!`, and `currComp`'s `chanMNext<vM'>?` input can synchronise with that output *inside the process*. The result is a process `tau`, lifted by `stepDeProcTau`, which never consults the mode state. The listener then holds `nextPincCheck m1' ..` while `k` can be anything, e.g. a stable `sing m0` with `nextModeMState k = None`.
  Concrete counterexample (any `m0 : Mode`, `r : Distance`, `l`, `h`):
  `p  = nilProc $||$ (outPrefix chanMNext [eBase m0] nilProc) $||$ currComp m0 r`,
  `p' = nilProc $||$ nilProc $||$ app nextPincCheckN [m0, m0, r]`, `k = k' = sing m0`, `a = aeTau`.
  `currCompStateEnt m0 r [|p,l,h,k|]` holds by `bisim_refl`. `nextPincCheckStateEnt m0 m0 r [|p',l,h,k|]` holds by unfolding the `app` (helper `ccnp_app_bisim`). The step is `stepDeProcTau` over `stepDpParR (stepDpSyncLR ...)`. The conclusion requires `None = Some m0`.
  In `EntAuxResults.currComp_nextPincCheck_track_ent.v` (HELPERS, compiles under `--explore` at the target's position, using no admitted lemmas):
  - `ccnp_counterexample : (statement) -> forall m0 r l h, False`
  - `ccnp_inconsistent : (statement) -> Mode -> False`
  This is not a quirk of a junk, unreachable state. In the real protocol the overlap's `tfsNext` (or `ovAbort`'s `chanMStable!`) can coexist with the listener's `currComp`/`currOK`, so the listener can "read" the overlap's *proposed* fail-safe mode instead of the mode state's. The thesis has the same unrestricted SYNC-LR/RL rules (thesis ~l.3659–3718).
- **Second, independent problem (argued, not machine-checked):** state predicates are bisimulation classes, and `nextPincCheck m1 m2 r` is a pair of guarded branches. Whenever `possIncBool m1 m2 r = false`, it is bisimilar to `listening`. Take `r'` with `r' >= possIncDist m1' m2'` (it is an arbitrary `Distance`). Then the *honest* step `currComp m2 r --chanMStable *?--> listening` via `stepDeRdStbl`, with a stable `k`, also satisfies both hypotheses. It refutes the conclusion (`nextModeMState k = None`) and `r = r'`. So even with the semantics repaired, the conclusion cannot recover the parameters of the target state from a bisimulation-class hypothesis. Only the parameters *produced by the step* can be concluded.
- **Ripple-up:** not in the safety cone. The only user is `NARIncomp.msgAbort_not_nextSince` (NARIncomp.v:188, case 3 "currComp"). That proof ends in `Qed`, so it currently rests on an inconsistent assumption. Its user is the `incomp_*` chain at NARIncomp.v:280 (also outside the cone). The sibling targets `currComp_listening_track_ent` (internal `chanMStable` sync with `tfsNext`/`ovAbort`, with `k` unstable, refutes its `k -ms- chanMStable @! -ms> k'`) and the `currOK`/`nextEq` analogues have the same internal-sync hole. `gotRange_currPincCheck_track_ent` does not, because `chanMCurr` outputs carry `[]` and `chanMCurr<vM>?` inputs carry 1 value, so `stepDpIn`'s length check blocks a sync.
- **Suggested fix:**
  1. *Definition change (needed for any version of the lemma):* forbid process-internal synchronisation on the mode-state channels, which the thesis's architecture clearly intends to be point-to-point with the mode state. E.g. in `SoftwareLanguage.v`:
     ```coq
     Definition modeStateChan (c : Channel) : Prop :=
       c = chanMStable \/ c = chanMCurr \/ c = chanMNext.
     (* add the premise ~ modeStateChan c to stepDpSyncLR and stepDpSyncRL *)
     ```
     (The `sort`/`noSync` machinery used for delays should get the same side condition.)
  2. *Restated lemma,* concluding only what the step determines, and in the form `msgAbort_not_nextSince` actually uses (it needs: listener moved out of `currComp`, `nextModeMState k0 = Some m'`, so the listener is now in `nextPincCheck m' m'' r`):
     ```coq
     Lemma currComp_nextPincCheck_track_ent (m2 m1 : Mode) (r : Distance)
       (l l' : Position) (p p' : ProcTerm) h h' k k' a :
       currCompStateEnt m2 r ([|p, l, h, k|]) -> nextModeMState k = Some m1 ->
       [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
       currCompStateEnt m2 r ([|p', l', h', k'|]) \/
       (nextPincCheckStateEnt m1 m2 r ([|p', l', h', k'|]) /\ k' = k).
     ```
     Proof idea once fix 1 is in place. If the listener component moves, then by bisimilarity with `currComp m2 r` its action is `chanMStable *?` or `chanMNext ;? [m]`, lifted unchanged to the top level, because syncs on these channels are now forbidden. The only entity rules with these process actions are `stepDeRdStbl`, impossible because `k` is unstable and `chanMStable @!` needs a stable state, and `stepDeNextRead`, where `stepMsOutNext` forces `k = <_, m, _> = k'`, so `m = m1`. The derivative is `app nextPincCheckN [m1, m2, r]`, which is bisimilar to `nextPincCheck m1 m2 r` (helper `ccnp_app_bisim` plus the substitution computation, both already checked in the helper file). In `msgAbort_not_nextSince` case 3 the `mapCuco` hypotheses give exactly `nextModeMState k0 = Some m'` and `possiblyIncompatible m' m'' r`. Then `nextPincCheck_cond_true` gives `abortOvlp`, so `mapAbort` applies, as the current script already intends.
- **Partial proof:** none of the target (it is false). See HELPERS of `EntAuxResults.currComp_nextPincCheck_track_ent.v` for the checked refutation and for `ccnp_app_bisim : def n = (l1, q) -> bisimulation (app n l) (subProcTerm (listsToSub l1 l) q)` (reusable) and `ccnp_varEq_tac` (computes `update`/`varEq` substitutions).

### `EntAuxResults.ovReady_ovWait_track_ent`

- **Where:** `src/EntAuxResults.v` line 534 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE (counterexample, Rocq-checked with no admitted dependencies). It also NEEDS-HYPOTHESIS: a reachability hypothesis.
- **Intent:** This is the entity-level tracking result for the overlap transition ovReady -> ovWait. If an entity whose overlap component is in `ovReady m t l0` takes a discrete step to an entity whose overlap component is in `ovWait m' ...`, then the step was the software outputting `[m, l0]` on `chanOutProc` to its own interface (`stepDeIOProcInter`), the mode state is untouched, `m = m'`, and the broadcast position `l0` is the entity's own position `l`.
- **Failure:** The statement has no reachability hypothesis. `ovReadyStateEnt`/`ovWaitStateEnt` are `liftProcEnt (liftOverlap ...)`, so they constrain only the middle parallel component of `p`. Both the entity position `l` and the other two components are arbitrary. Two independent counterexamples are checked in `--explore` (rc=0) in `EntAuxResults.ovReady_ovWait_track_ent.v`. `Print Assumptions` on each lists only the ComhBasics model parameters plus the stdlib's classical-reals, functional-extensionality and proof-irrelevance axioms. No admitted lemma is used.
  1. **`l = l0` fails** (`ovReady_ovWait_track_ent_false : forall m0 : Mode, ~ <statement>`). Fix any `m0 : Mode` and take
     - `p  := nilProc $||$ ovReady m0 (period m0) (mkPosition 0 0) $||$ nilProc`, at position `l := mkPosition 1 0`;
     - `p' := nilProc $||$ ovWaitN $([m0, period m0 (-) ePeriod m0, ePeriod m0])$ $||$ nilProc` (the literal ovReady continuation);
     - `h` with empty lists, `h'` with `<([m0, (0,0)], msgLatency)>` buffered in the output list, and `k = k' = sing m0`;
     - the step `stepDeIOProcInter` (ParR/ParL/`stepDpOut` + `stepIntBuffOut`/`stepOlBuff`).

     The ovWait premise holds with `t' = x' = mkTime (period m0 -nn- period m0)` and `y' = period m0`. The statement then yields `mkPosition 1 0 = mkPosition 0 0`, which `lra` refutes. Discrete entity steps never move the entity, and nothing ties `l0` to `l` except the history: `ovReady` is entered via `chanPos` (`stepDePosRead`) and left before any delay. That is an invariant of *reachable* entities only.
  2. **The process/interface conjuncts fail too, even with `l = l0`** (`ovReady_ovWait_track_ent_false2`, which refutes the weaker statement with only the first conjunct). Make the third component `inPrefix chanOutProc [vM'', vL'] nilProc`. The ovReady output then synchronises internally (`stepDpSyncLR`), the entity step is `stepDeProcTau` with `h' = h`, and `p` has no `chanOutProc ;! [m0, l0]` step to `p'`. Inversion refutes it.
  - The non-trivial ingredient in both is the premise `ovWaitState m0 t' t' (period m0) (ovWaitN $([m0, t (-) ePeriod m0, ePeriod m0])$)`. It is proved by a small "bisimulation up to evaluation of time expressions" (`..._R`, `..._R_disc`, `..._R_timed`, `..._R_sym`, `CoFixpoint ..._bisim`). It relates `app` terms to their unfoldings and ovWait/ovReady bodies whose time arguments evaluate (via `evalBaseNonnegFun ∘ evalExpFun`) to the same nonneg real.
- **Ripple-up:** Not in the safety cone. Its only users are inside **commented-out** proofs of two admitted `(*R*)` theorems: `NARMsgPosition.fst_sent` (NARMsgPosition.v:90) and `NARTop.ovWait_sent` (NARTop.v:140). Both live in a `reachableNet n` context. Both use only the process-step and interface-step conjuncts (to build `sentBase`), plus `k = k'`/`m = m'` through `subst`. The `exists l` in their conclusions does not need `l = l0`. Nothing compiled breaks if the statement is changed.
- **Suggested fix:** add a reachability hypothesis. Two variants:
  - (a) **Preferred, stub-free.** Drop `l = l0` and assume protocol reachability, which the callers get from `NetAuxBasics.reachable_net_prot`:
    ```coq
    Lemma ovReady_ovWait_track_ent m m' t t' x' y' l0 a p p' l l' h h' k k' :
      reachableProt p ->
      ovReadyStateEnt m t l0 ([|p, l, h, k|]) ->
      ovWaitStateEnt m' t' x' y' ([|p', l', h', k'|]) ->
      [|p, l, h, k|] -EA- a ->> [|p', l', h', k'|] ->
      p -PA- chanOutProc ;! [baseMode m, basePosition l0] -PA> p' /\
      h -i- chanOutProc {? [baseMode m, basePosition l0] -i> h' /\
      k = k' /\ m = m'.
    ```
    Proof plan (believed provable relative to the existing admitted ProtAuxResults lemmas):
    1. `reachableProt_triple` gives `p = p1 $||$ p2 $||$ p3` with broadcast/overlap/listener states, and `p2` is the ovReady component.
    2. Invert the entity step. The four steps that leave `p` unchanged make `p2` bisimilar to both ovReady and ovWait, which `state_pred_elim` / `bisim_contra` refute.
    3. Every other step is a process step. Decompose the parallel step. `p1`/`p3`-only steps leave `p2` unchanged (same contradiction).
    4. A `p2` step lands in ovWait. `ProtAuxResults.ovWait_prev` (Qed) gives the action `chanOutProc ;! [m', l']` with `ovReadyState m' _ l' p2`, and bisimilarity with `ovReady m t l0` forces `m' = m` and `l' = l0`.
    5. Synchronisation with `p1`/`p3` would need a broadcast or listener input on `chanOutProc`, which is impossible (cf. `prot_outProc_in_not`).
    6. So the top-level action is `chanOutProc ;! [m, l0]`. The only entity rule with that process action is `stepDeIOProcInter`, which gives the interface step and `k = k'`.
  - (b) **Keeping `l = l0`.** Add `reachableEnt ([|p, l, h, k|])` instead. `l = l0` then follows from `ovReady_pos` (admitted, D- reachableEnt) together with a completed `inPosEnt` stub (`inPosEnt l [|_, l', _, _|] <-> l = l'`). This variant is therefore BLOCKED-ON-STUB (`reachableEnt`, `inPosEnt`) until those are defined. The other conjuncts follow as in (a) via `reachable_ent_prot`.
- **Related observation:** the sibling `*_track_ent` lemmas just above (`gotMsg_gotRange_track_ent`, `gotRange_currPincCheck_track_ent`, `currComp_listening_track_ent`, `currComp_nextPincCheck_track_ent`) also lack reachability hypotheses. They are very likely refutable the same way, because an arbitrary sibling component can synchronise on `chanPos` / `chanMCurr` / `chanMStable` / `chanMNext` instead of the mode state or the position read. This was not checked here.
- **Partial proof:** none of the target. The `.v` file holds the two Rocq-checked refutations. Its bisimulation helpers (`..._R*`, `..._bisim`) also prove the ovWait half of the admitted `ProtAuxResults.ovlp_outProc_out` for the concrete ovReady continuation, and can be reused there.

## NARTop

### `NARTop.ovWait_sent`

- **Where:** `src/NARTop.v` line 116 · **Theorem** · 2015 label: `The base case fails because we know all entities are dormant to begin with.` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `incomplete-definition (overlapState/listenerState)`
- **Fix (audit summary):** Add reachableNet n to NetAuxBasics.ovWait_prev_net_strong and fix reachableProt_triple (compReach); then re-run the cloud proof.

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof depends on an admitted lemma that is inconsistent as stated)
- **Intent:** See the in-file comment and `(*Proof: …*)` sketch.
- **Failure:** A complete proof was written in the cloud session, and for `currSince_del_bcWait` it was re-checked here. It rests on admitted lemmas that are inconsistent as stated (`ovWait_prev_net_strong` and/or `reachableProt_triple`, transitively). So it can't be accepted until those statements or definitions are fixed. See CONDITIONAL_PROOFS.md.
- **Ripple-up:** In the safety cone: `ovWait_sent` feeds `nextSince_periodic_sent`, and `currSince_del_bcWait` feeds `currSince_periodic_sent`.
- **Suggested fix:**
  - Add `reachableNet n` to `ovWait_prev_net_strong`.
  - Make the protocol component state predicates reachability-based (`compReach`), so that `reachableProt_triple` becomes provable.
  - Then re-run the proof, which is kept in the cloud-NARTop work dir and diff.

### `NARTop.currSince_del_bcWait`

- **Where:** `src/NARTop.v` line 280 · **Corollary** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `incomplete-definition (overlapState/listenerState)`
- **Fix (audit summary):** Fix reachableProt_triple (compReach) and currSince_bc_state, then re-run the existing conditional proof.

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof depends on an admitted lemma that is inconsistent as stated)
- **Intent:** See the in-file comment and `(*Proof: …*)` sketch.
- **Failure:** A complete proof was written in the cloud session, and for `currSince_del_bcWait` it was re-checked here. It rests on admitted lemmas that are inconsistent as stated (`ovWait_prev_net_strong` and/or `reachableProt_triple`, transitively). So it can't be accepted until those statements or definitions are fixed. See CONDITIONAL_PROOFS.md.
- **Ripple-up:** In the safety cone: `ovWait_sent` feeds `nextSince_periodic_sent`, and `currSince_del_bcWait` feeds `currSince_periodic_sent`.
- **Suggested fix:**
  - Add `reachableNet n` to `ovWait_prev_net_strong`.
  - Make the protocol component state predicates reachability-based (`compReach`), so that `reachableProt_triple` becomes provable.
  - Then re-run the proof, which is kept in the cloud-NARTop work dir and diff.

### `NARTop.bcWait_currSince_time`

- **Where:** `src/NARTop.v` line 288 · **Theorem** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** FALSE-ARGUED · root cause: `other:wake-up-corner-case (bcWait m 0 right after switchBc)`
- **Fix (audit summary):** Add 0 < x (the only caller currSince_periodic_sent passes x + d > 0).

- **Status:** FALSE (counterexample, argued trace)
- **Intent:** If the broadcaster is `bcWait m x` while `currSince m t`, then the last broadcast of `m` was `period m - x` ago, and that is at most `t`.
- **Failure:** No axiom relates `period` to `waitTime`. Take `m_prev -mtr-> m` with `W := waitTime m_prev m < period m`. Then this run happens with no time passing:
  1. `init m` → `ovWait(m, W, W, period m)`
  2. after `W`, `chanPause!` → `switchBc m`
  3. `switchBc m` wakes the broadcaster to `bcWait m 0`
  4. `switchCurr` → `switchListen`, which can come before `bcWait m 0`'s zero-timeout `chanPos?`

  `currSinceBase` now gives `currSince m W` with `bcWait m 0`, so the goal `period m <= W` fails. The 2015 sketch's base case "x = period m" overlooks this wake-up state.
- **Ripple-up:** The only user is `currSince_periodic_sent` (`NARTop.v:448`), which feeds `currSince_fst_deliv_suff`, then `pre_del_suff`, then `safety`. The caller always passes `x + d > 0`, so the false corner case never arises there.
- **Suggested fix:** Add `0 < x ->`. With that, the induction's base case is vacuous, and the caller already has `0 < x + d` from `delPos`.

### `NARTop.init_ovWait_track_net`

- **Where:** `src/NARTop.v` line 104 · **Lemma** · 2015 label: `#lift-track-net` · **in safety cone:** no
- **Audit:** BLOCKED-ON-DEFINITION · root cause: `other:missing-bisimulation-injectivity-infrastructure (not a failure)`
- **Fix (audit summary):** Weaken the conclusion to y = zeroTime (all that ovWait_sent uses) or add an ovWait_bisim_inj helper.

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** A discrete step from `init m` into `ovWait m' t' x y` forces `m = m'`, `x = t'` and `y = 0`.
- **Failure:** It needs injectivity of `ovWait`'s parameters up to bisimilarity, i.e. `ovWait m t x y ~p~ ovWait m' t' x' y' -> ...`, which needs coinductive timed reasoning. The development has no infrastructure for that, and even the sibling tracking lemmas are admitted. (Other provers showed several sibling `*_track_net` lemmas are false because truncated subtraction makes different `t` bisimilar, so check that this one asserts nothing about `t` beyond what is observable.)
- **Ripple-up:** It is used only by `ovWait_sent` (init case), then `nextSince_periodic_sent`, then `currSince_fst_deliv_suff`, then `safety`. Only `y = 0` is consumed.
- **Suggested fix:** Weaken the conclusion to `y = zeroTime`, which is all the caller needs, or add an `ovWait_bisim_inj` helper.

### `NARTop.tfsBc_not_currSince`

- **Where:** `src/NARTop.v` line 239 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `other:failSafeSucc-may-be-identity`
- **Fix (audit summary):** Add ~ failSafe m, or model axiom failSafeSucc m <> m (owner approval).

- **Status:** NEEDS-HYPOTHESIS
- **Intent:** An entity in `tfsBc` is not currSince any mode.
- **Failure:** No axiom forbids `failSafeSucc m = m`, or `m -mtr-> m`. Take a fail-safe `F` with `failSafeSucc F = F`. Then `currSince F` survives the whole tfs path through `tfsStart`, `tfsNext F` and `tfsCurr` to `tfsBc`. The 2015 sketch's "mode transition relation is anti-reflexive" is not an axiom.
- **Ripple-up:** It is used only by the intended proof of `currSince_bc_state`; grep finds no direct Rocq users.
- **Suggested fix:** Either:
  - add the model axiom `failSafeSucc m <> m` (needs owner approval), or
  - restate the lemma with `~ failSafe m ->`.

### `NARTop.currSince_bc_state`

- **Where:** `src/NARTop.v` line 256 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** FALSE-ARGUED · root cause: `other:new-transition-wakes-broadcaster-in-new-mode`
- **Fix (audit summary):** Add ~ switchCurrStateNet i n (currSince_del_bcWait then needs net-level switchCurr urgency).

- **Status:** FALSE (counterexample, argued trace)
- **Intent:** While `currSince m` holds, the broadcaster is `bcWait m _` or `bcReady m _`.
- **Failure:** Start a new transition to `m' <> m`: `stepMsInit`, dormant reads mNext, then `init m'`, `ovWait m'`, `ovReady m'`, `switchBc m'`. The current mode stays `m`, so `currSince m` survives. Then `switchBc m'` does `chanWake<m'>!`, and the broadcaster's `chanWake?` branch makes it `bcWait m' 0`. Now `currSince m` holds with broadcaster `bcWait m' 0`, and neither disjunct holds.
- **Ripple-up:** It is used by `currSince_del_bcWait`, then `currSince_periodic_sent`, then on to `safety`. The counterexample state `switchCurr` is urgent, and every current use is under a delay, so those uses avoid it.
- **Suggested fix:** Add `~ switchCurrStateNet i n ->`. The knock-on is that `currSince_del_bcWait` then needs a network-level lemma that switchCurr is urgent.

## ProtAuxResults

### `ProtAuxResults.listening_AN_prot`

- **Where:** `src/ProtAuxResults.v` line 354 · **Lemma** · 2015 label: `C` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `listener-arity` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add length v = 2 (proved) or, better, make listening input 3-tuples [vR, vM'', vL'] to match the interface and require length v = 3; NetAuxBasics.incomingNetNotif_del then needs a notification-shape invariant.

- **Status:** FALSE (counterexample, verified in Rocq)
- **Intent:** a protocol process whose listener component is in the `listening` state can accept an adaptation notification on channel `chanAN`.
- **Failure:** the statement quantifies over an arbitrary tuple `v`, but `listening` only inputs on `chanAN` through the prefix `chanAN$<[vR, vM'']>$? ...`, and `stepDpIn` needs `length v = length [vR; vM''] = 2`. No other component of a protocol process (broadcast: inputs on `chanWake`/`chanTrans`; overlap: on `chanMNext`/`chanAbort`/`chanBad`/...) inputs on `chanAN`, and parallel synchronisation produces only `tauAct`. So for any `v` with `length v <> 2` the conclusion fails.
  Counterexample: `p := procProtocol = sleeping $||$ dormant $||$ listening`, `v := []`. Verified (compiles with `Qed`, explore run):
  ```
  Lemma listening_AN_prot_counterexample :
    listeningStateProt procProtocol /\ ~ discActEnabled procProtocol (chanAN ;? []).
  Proof.
    split.
    - unfold listeningStateProt, procProtocol. constructor. unfold listeningState.
      apply bisim_refl.
    - intro D. inversion D as [q TR]. clear D. unfold procProtocol in TR.
      repeat invert_trans;
      try match goal with [H : length _ = length _ |- _] => simpl in H; inversion H end.
  Qed.
  ```
- **Deeper modelling issue (affects the fix):** notifications that actually reach the notification list have length 3, not 2. `stepIntFwdOut` (InterfaceLanguage.v ~l.310) enqueues `(baseDistance r) :: v` where `v` is the outgoing message, and messages are `[baseMode m, basePosition l]` (`bcReady`/`ovReady` output `chanOutProc$<[m, l]>$!`). NARInsuff.v also uses `incomingNetNotif [baseDistance r, baseMode m, basePosition l] ...`. So with the current `listening` definition the listener can **never** accept a real notification, even with a length hypothesis on `v`.
- **Ripple-up:** in the safety cone. Used in NetAuxBasics.v `incomingNetNotif_del` (lines ~699 and ~707) with an arbitrary `v` taken from `incomingNetNotif v t i n`. That proof breaks if this lemma is false; the user would need a shape invariant on notifications in reachable networks.
- **Suggested fix (two parts):**
  1. Make the listener accept 3-tuples, matching the interface: in SoftwareLanguage.v,
     `Definition listening := chanAN$<[vR, vM'', vL']>$? checkRangeN $([eVar vM'', eVar vR])$ $+$ ...`
     (any third fresh variable, `vL'` is unused in `checkRange`). Then restate
     ```
     Lemma listening_AN_prot p v :
       length v = 3%nat -> listeningStateProt p -> discActEnabled p (chanAN ;? v).
     ```
  2. In `incomingNetNotif_del`, discharge `length v = 3` from a reachability invariant ("every element of every notification list in a reachable network has length 3"), which follows from `stepIntFwdOut` plus the fact that a protocol process only outputs `[m, l]` on `chanOutProc` (`bc_outProc_out`, `ovlp_outProc_out`, `listener_outProc_out_not`).
  With the current `listening` definition, the analogous statement with `length v = 2%nat` is provable (checked, `Qed`):
  ```
  Lemma listening_AN_prot_fixed p v :
    length v = 2%nat -> listeningStateProt p -> discActEnabled p (chanAN ;? v).
  Proof.
    intros L LS. inversion LS as [p1 p2 p3 Q]; subst.
    apply daeParR; apply daeParR.
    eapply bisim_dae; [apply bisim_symm; apply Q | ]. unfold listening.
    apply daeSumL; apply daeSumL; apply daeSumL. apply dae_inPfx. simpl. rewrite L. reflexivity.
  Qed.
  ```
  The same script proves the 3-variable version after fix 1 (with `3%nat`).

### `ProtAuxResults.ovWait_del_pres`

- **Where:** `src/ProtAuxResults.v` line 658 · **Lemma** · 2015 label: `#delay-pres` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `other:timers-count-down-under-delay` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude exists x' y', ovWaitState m t x' y' p' (proved, model axioms only, enough for del_pres_nextSinceState), or the quantitative minusTime version (proved).

- **Status:** FALSE (counterexample, verified in Rocq). Corrected statements are proved (see below).
- **Intent:** A delay keeps the overlap-waiting process in the `ovWait` state for the same mode `m` and time `t`. Thesis Remark 5.10 / p.~6390ff: `ovWait(m',t,t')` after a delay is the same sum with both timers decremented, e.g. `ovWait(m',21,9) --9--> ... + ε(0)chanPos?... + ε(3)cPause!...`.
- **Failure:** `ovWait m t x y` contains two timeouts, `$<y>$chanPos?...` and `$<x>$chanPause!switchBcN(m)`. A delay `d` counts both down (`stepTpDelSub` gives `$<x-d>$`, and `stepTpDelAdd` lets the delay run past expiry into the continuation). So `p'` is (bisimilar to) `ovWait m t (x-d) (y-d)`, truncated at 0, never to `ovWait m t x y`.
  Concrete counterexample, for every `m t d`: `x = y = d`, `p = ovWait m t d d`. Then `p -PD- d -PD> p'` with `p' = ... + $<0>$chanPos?... + $<0>$chanPause!...`. `p'` can do `outAct chanPause [m]` immediately via `stepDpTimeOut`, but `ovWait m t d d` cannot, because its timer is `d > 0`. So `~ p' ~p~ ovWait m t d d`. Lemmas `ovWait_del_pres_cex` and `ovWait_del_pres_refuted` in `ProtAuxResults.ovWait_del_pres.v` prove this; they compile in `--explore` and rest only on model axioms and the stdlib classical axioms.
- **Ripple-up:** The only user is `ProtAuxResults.del_pres_nextSinceState` (line 680, proved, `lets AUX : ovWait_del_pres H U0. eapply nexsOvwSt`). That is used by `NARMisc.v:166`. The target is in the safety cone. `del_pres_nextSinceState` only needs *some* `ovWaitState m t x' y' p'`, so nothing up the chain breaks under the existential fix below. Related: `NetAuxBasics.ovWait_del_pres_net` (line 1026, an iff with the *same* `x y` across a network delay) is false for the same reason. It is used in NARMisc's commented-out `(*R*)` proof (line 494). `ovWait_del_pres_bkwd_net_strong` already has the correct `x +dt+ d` shape.
- **Suggested fix:** replace the statement with either of the following (both proved, `Qed`, in the HELPERS of my `.v` file):
  ```coq
  (* minimal: sufficient for del_pres_nextSinceState, holds for every d *)
  Lemma ovWait_del_pres m t x y p p' d :
    ovWaitState m t x y p -> p -PD- d -PD> p' ->
    exists x' y', ovWaitState m t x' y' p'.
  (* quantitative, for delays within both timers *)
  Lemma ovWait_del_pres_strong (m : Mode) (t x y : Time) (p p' : ProcTerm) (d : Delay)
    (Hx : d <= x) (Hy : d <= y) :
    ovWaitState m t x y p -> p -PD- d -PD> p' ->
    ovWaitState m t (minusTime x d Hx) (minusTime y d Hy) p'.
  ```
  The existential version needs one helper, `$<0>$ q ~p~ q` (`ovWait_del_pres_zero_bisim`). It covers the case where a timer is overrun: `$<x>$P -d-> P` via `stepTpDelAdd` when `d > x`, and `P ~ $<0>$P`. With that and `choice_bisim_context`, the delayed term is bisimilar to `ovWait m t x' y'`. To drop it into `del_pres_nextSinceState`, change its first bullet to `destruct (ovWait_del_pres H U0) as [x' [y' AUX]]. eapply nexsOvwSt; eassumption.` (checked as `ovWait_del_pres_user_ok`).
- **Partial proof:** the whole of `(prover work area; evidence for audited targets is in `2026-10-14-proof-completion-pass-1-evidence/audit/`) ProtAuxResults.ovWait_del_pres.v` HELPERS. The helpers are `ovWait_del_pres_zero_bisim`, `ovWait_del_pres_timer_aux`, `ovWait_del_pres_fixed` (existential), `ovWait_del_pres_timer_aux2`, `ovWait_del_pres_strong` and `ovWait_del_pres_user_ok`. The counterexample is by the earlier prover ProtAuxResults-3, and I re-verified it.

### `ProtAuxResults.reachableProt_triple`

- **Where:** `src/ProtAuxResults.v` line 843 · **Theorem** · 2015 label: `Need support lemmas: disc pres & del pres for ovlp, broadcast, listener state components.` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `incomplete-definition (overlapState/listenerState)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Define broadcastState/overlapState/listenerState as closure of sleeping/dormant/listening under component steps (compReach); reachableProt_triple then holds (reachableProt_triple_fix proved, model axioms only); consumers must be re-proved by induction on compReach.

- **Status:** FALSE (counterexample). The negation can be proved from the model axioms alone, so **the admitted lemma is inconsistent**. Add it to the blacklist: any proof that uses it, directly or through the `reachprot`, `urgency_pre_tac*` or `reach_net_prot_tac` tactics, is vacuous.

- **Intent:** every process reachable from `procProtocol` (`sleeping || dormant || listening`) through the process-level semantics has the form `p1 || p2 || p3`, where p1 is a broadcast-component state, p2 an overlap-component state and p3 a listener-component state. Users invert `protocolState` to get `broadcastState p1`, `overlapState p2` and `listenerState p3`, and pass these to the brute-force lemmas (`bc_outProc_out`, `listen_mCurr_out_not`, `link_reach_triple_tau`, ...).

- **Failure:** three independent counterexamples, all compiled in `--explore` mode in `ProtAuxResults.reachableProt_triple.v` (this dir, HELPERS section). `Print Assumptions` shows only model axioms plus stdlib classical/FE/PI, and no admitted lemma.
  1. **`overlapState` is incomplete.** Its definition says `(*INCOMPLETE- Need to add constructors for ALL the overlap states.*)` and has only `dormant` and `ovWait`. The step `procProtocol -PA- chanBad ;? [] -PA> sleeping $||$ tfsStartN $||$ listening` takes dormant's `chanBad? tfsStartN` branch. `tfsStartN` is not bisimilar to `dormant` or to any `ovWait m t x y`, because both of those can do `chanAbort ;? []` and `tfsStart` can only input on `chanMCurr`. Lemmas: `reachableProt_triple_cex_step`, `reachableProt_triple_cex_not_ovlp`, `reachableProt_triple_cex`, and
     ```
     Lemma reachableProt_triple_false : ~ (forall p, reachableProt p -> protocolState p).
     ```
     This is the statement under review, refuted.
  2. **`listenerState` is incomplete.** It has no `paused`, `gotMsg` or `gotRange`. The step `procProtocol -PA- chanPause ;? [] -PA> sleeping $||$ dormant $||$ pausedN` leads to `pausedN`, which is bisimilar to none of the 6 listener states: each of those has an enabled action that `paused` (which only does `chanUnpause?`) lacks. Lemmas: `reachableProt_triple_cex2_not_list`, `reachableProt_triple_cex2`.
  3. **Typing gap, which no completion with named states fixes.** At process level, inputs are unconstrained (`stepDpParL/R` with `inAct` and any `list BaseType` of the right length). So an ill-typed value can be input. Listening inputs `chanAN ;? [baseTime 0; baseTime 0]`, giving `checkRangeN([0,0])`. Both of its guards (`bSufficient` and its negation) evaluate to `false` through `evalBoolExpFunTot` (`None ↦ false`), so this state has **no discrete transitions at all** (`reachableProt_triple_stuck_dead`). Every named listener state with `Mode`/`Distance`/`Position` parameters has an enabled discrete action, so the stuck state is bisimilar to none of them (`reachableProt_triple_cex3`). The same holds for any completed `listenerState` built from named states. Similar ill-typed inputs on `chanWake`, `chanMNext` or `chanMCurr` give broadcast and overlap states with ill-formed parameters. Those break `broadcastState`, even though its 3 constructors are complete by name (argued by hand, not mechanised).

- **Ripple-up:** in the safety cone. Direct users: `NARMsgPosition.sent_pos_bound`, `NARNonFS_currSince.nonFS_currSince`. Through `reach_net_prot_tac` (NetAuxBasics): `NARIncomp.msgAbort_not_nextSince` and `NARInsuff.notifAbort_not_nextSince`. Through `reachprot` and `urgency_pre_tac*` (EntAuxResults): `tfsStartStateEnt_urgent`, `tfsListen_urgent`, `tfsNext_urgent`, `bcReady_urgent`, `ovAbort_urgent`, `tfsBc_urgent`, `switchBc_urgent`, `swithcCurr_urgent`, `switchListen_urgent` and the other `*_urgent` lemmas. Accepted wave-1 proofs whose files mention these names, so their `.ok` needs re-auditing with `Print Assumptions`: `EntAuxResults-2/{abortOvlpStateEnt_urgent, del_listening_pre, del_ovlp}`, `NARInsuff/notifAbort_not_nextSince`, `w1b-20/NetAuxBasics.del_listening_net`. Because the lemma is refutable, everything proved from it is vacuous. Its downstream uses are sound only once `protocolState` is redefined as below.

- **Suggested fix (definition change; needs owner approval):** define the component predicates as closure under the component-level semantics instead of as finite lists of named states:
  ```
  Inductive compReach (p0 : ProcTerm) : ProcTerm -> Prop :=
    | crBase : compReach p0 p0
    | crDisc p p' a : compReach p0 p -> p -PA- a -PA> p' -> compReach p0 p'
    | crDel  p p' d : compReach p0 p -> p -PD- d -PD> p' -> compReach p0 p'.
  Definition broadcastState := compReach sleeping.
  Definition overlapState   := compReach dormant.
  Definition listenerState  := compReach listening.
  (* protocolState unchanged *)
  ```
  With this, `reachableProt_triple` is **proved** (the validated form is `reachableProt_triple_fix` in my `.v`: induction on `reachableProt`, inverting par/sync disc steps and `stepTpPar` delays; about 15 lines). The brute-force consumers (`bc_outProc_out`, `ovlp_outProc_out`, `prot_outProc_in_not`, `bc_mCurr_out_not`, `listen_mCurr_out_not`, `listener_outProc_out_not`, `link_reach_triple_tau`, ...) then become induction-on-`compReach` tracking lemmas. They should stay true because they constrain only which actions a reachable component can do, and ill-typed values cannot produce well-typed outputs such as `[baseMode m, basePosition l]`. Their conclusions about named states (for example `bcReadyState m l p`) still need well-typed matching, which follows from the output's values.
  Alternative: keep the named predicates but (a) add every missing constructor (`init`, `ovReady`, `switchBc/Curr/Listen`, `ovAbort`, `tfs*` for overlap; `paused`, `gotMsg`, `gotRange` for listener) **and** (b) restrict `reachableProt` to well-typed inputs, or state the lemma only for software components of reachable networks. (b) is needed because of counterexample 3. This is a larger change.

- **Partial proof:** none for the stated lemma, which is impossible. See the `.v` for the counterexamples and the validated replacement (`reachableProt_triple_fix`).

### `ProtAuxResults.currOK_listening_track`

- **Where:** `src/ProtAuxResults.v` line 377 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:nextEq-else-branch-returns-to-listening (plus untyped-input)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude a = chanMStable *? \/ exists v, a = chanMNext ;? [v] /\ v <> baseMode m (proved, model axioms only).

- **Status:** FALSE (counterexample checked in Rocq; needs one `m : Mode`). A corrected statement is **proved** in the same file.
- **Intent:** the listener goes from `currOK m` back to `listening` only by reading `chanMStable` from the mode state, i.e. when there is no pending mode transition.
- **Failure:** `currOK m'' = chanMStable? listeningN $+$ chanMNext<vM'>? nextEqN[vM', m'']` and `nextEq m' m'' = (m' =b= m'') $> abortOvlpN $+$ !~(m' =b= m'') $> listeningN`.
  - Conditionals are not steps in this semantics, so `nextEq v m ~p~ listening` whenever `v <> baseMode m`. The `ProcEquiv.if_then_bisim_false` lemma gives exactly this.
  - So `currOK m -(chanMNext ;? [v])-> nextEqN[v, m]`, and the derivative is in `listeningState`, with action `<> chanMStable *?`.
  - The thesis (`thesis.txt` l. 6724, Ch. 5: "Otherwise the process effectively returns to the listening state which is essentially the 'else' branch of the process nextEq") describes exactly this path, so it is intended protocol behaviour. Only the lemma is wrong.
  - Rocq evidence (`ProtAuxResults.currOK_listening_track.v`, --explore, all `Qed`; `Print Assumptions` shows only model axioms and stdlib axioms, **no admitted lemmas**):
    - `currOK_listening_track_cex_gen m v : v <> baseMode m -> exists p p', currOKState m p /\ listeningState p' /\ p -PA- chanMNext ;? [v] -PA> p'`
    - `currOK_listening_track_cex_modes m m' : m' <> m -> …`. This is the protocol-realistic instance: the next mode differs from the notified mode.
    - `currOK_listening_track_cex m : ~ (statement)`, using `v := baseTime zeroTime`, so a single Mode suffices.
- **Ripple-up:**
  - Not in the safety cone itself.
  - Its only users are in the **commented-out** old proof of `NARInsuff.notifAbort_not_nextSince` (NARInsuff.v:249, 255, 272; that theorem is an `R` target **in the safety cone**). There it eliminated LEP sub-cases by `inversion` on `a = chanMStable *?`. Whoever re-proves `notifAbort_not_nextSince` must not rely on the false statement.
  - In that context the bad case is harmless. `napCuok` gives `currOKStateProt m' p` with `nextModeMState k = Some m'`. A `chanMNext` read synchronised with the mode state reads `m'` itself (`stepMsOutNext`), so `v = baseMode m'`, which the corrected lemma excludes.
  - A synchronisation of the listener's `chanMNext` input with an **overlap** output on `chanMNext` (`tfsNext` outputs `chanMNext<eFailSafeSucc m>`) is a separate case the user must discharge with state reasoning. The original lemma papered over it.
- **Suggested fix:** weaken the conclusion to the honest disjunction:
  ```coq
  Lemma currOK_listening_track m p p' a : currOKState m p ->
    listeningState p' -> p -PA- a -PA> p' ->
    a = (chanMStable *?) \/ exists v, a = chanMNext ;? [v] /\ v <> baseMode m.
  ```
  This is **proved** as `currOK_listening_track_fixed` (Qed, no admitted dependencies). The proof inverts the matching step of `currOK m`. In the `v = baseMode m` case it shows `nextEq m m` can output `chanAbort` while `listening` cannot, which contradicts bisimilarity via `bisim_dae`. The fixed proof can be spliced in verbatim once the statement change is approved; it needs only the helper `currOK_listening_track_listening_no_abort`.
- **Partial proof:** see above. Everything in the HELPERS is demonstration-only until the statement is changed.

### `ProtAuxResults.rangeBad_next`

- **Where:** `src/ProtAuxResults.v` line 522 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** NEEDS-HYPOTHESIS · root cause: `untyped-input`
- **Fix (audit summary):** Recommended tracking form: p -PA- chanMCurr ;? [baseMode m] -PA> p' -> rangeBadState m'' p -> currEqState m m'' p' (proved, model axioms only); minimal alternative adds (exists m0, m0 <> m'') (proved).

- **Status:** NEEDS-HYPOTHESIS. Independent of the model axioms: it is equivalent to "every mode has a distinct other mode", which fails in the one-mode model. Proved in Rocq in both directions, see below.
- **Intent:** forward tracking for the listener. From `rangeBad m''`, the only discrete step is reading the current mode `m` on `chanMCurr`, after which the listener is in `currEq m m''`. That state is the conditional `m = m'' ? badOvlp : currOK m''`.
- **Failure:**
  - `rangeBad m'' = chanMCurr<vM>? currEqN(vM, m'')` accepts **any** base value `v` (`stepDpIn` only checks list length), not just modes. For a non-mode `v`, e.g. `baseTime 0`, `bEqual` still evaluates to `Some false` (it compares any base values with `eqDecBase`). So the derivative is `currEqN(v, m'') ~ currOKN(m'')`.
  - That process is `~ currEq m m''` exactly when `m <> m''`. `currEq m'' m'' ~ badOvlp` can output `chanBad`, and `currOK` cannot.
  - So the conclusion `exists m, currEqState m m'' p'` needs a mode other than `m''`. Nothing in `ComhBasics.v` provides one. All model axioms hold with `Mode := unit`: `failSafe := True`, `failSafeSucc := id`, `modeTransRel := fun _ _ => True`, all times and distances 0 or 1, and `period`/`msgLatency`/`adaptNotif`/`speedMax := 1`. In that model the lemma is false.

  Machine-checked in `ProtAuxResults.rangeBad_next.v` (HELPERS, `--explore`, assumptions: model axioms + trusted stdlib only):
  - `rangeBad_next_needs_two_modes : (<target statement>) -> forall m'' : Mode, exists m, m <> m''`.
- **Ripple-up:** used in `NARInsuff.notifAbort_not_nextSince` (line ~212, the rangeBad case). The proof there continues with `currEq_cond_false` and `EntAuxResults.currEq_mode` to tie the existential `m` to the mode state's current mode. The existential form loses exactly that information, so the user needs the *tracking* form below anyway. In the safety cone (per `show`). Related: `NetAuxBasics.rangeBad_next_net` (NetAuxBasics-2 write-up) proposes a prot-level `rangeBad_track`; `rangeBad_next_track` below is that lemma, proved.
- **Suggested fix (recommended, proved):** state the tracking form, which pins `m` to the value read.
  ```coq
  Theorem rangeBad_next (p p' : ProcTerm) (m m'' : Mode) :
    p -PA- chanMCurr ;? [baseMode m] -PA> p' -> rangeBadState m'' p ->
    currEqState m m'' p'.
  ```
  It is proved as `rangeBad_next_track`. In a reachable entity the only `chanMCurr` value the listener can read is `baseMode (currModeMState k)` (`stepDeCurrRead`; see the NetAuxBasics-2 note on excluding internal mCurr syncs). So the caller gets `currEqState (currModeMState k) m'' p'` directly, which is what `notifAbort_not_nextSince` then needs for `currEq_cond_false`.
  Supporting lemma, also proved: `rangeBad_next_inv : rangeBad m'' -PA- a -PA> q -> exists b, a = chanMCurr ;? [b] /\ q ~p~ currEq (eBase b) m''`. It shows that every step is an mCurr read.
  **Minimal-diff alternative (proved):** keep the conclusion and add `(exists m0, m0 <> m'') ->` as a hypothesis (`rangeBad_next_two_modes`). The alternative of adding a model axiom "at least two modes" changes the trust base and needs owner approval. Either way the existential still doesn't link `m` to the read value, so the tracking form is preferable.
- **Partial proof:** everything is in the HELPERS of `ProtAuxResults.rangeBad_next.v`:
  - `rangeBad_next_app_bisim`: `n $(l)$ ~ body[l]`.
  - `rangeBad_next_inv`, `rangeBad_next_track` and `rangeBad_next_isMode`.
  - `rangeBad_next_currOK`, `rangeBad_next_nonmode` and `rangeBad_next_two_modes`.
  - `rangeBad_next_needs_two_modes`.
  The target's own PROOF stays `Admitted`.
- **Note for siblings (unchecked):** other "input then conditional" fwd-tracking lemmas with an existential over a typed parameter and **no** fallback disjunct (e.g. `gotMessage_next`) may have the same ill-typed-input issue. I have not checked them. `currOK_next` escaped it only because its `\/ listeningState p'` disjunct absorbs non-mode reads.

### `ProtAuxResults.gotMessage_next`

- **Where:** `src/ProtAuxResults.v` line 526 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `eSubtract-vs-bPossInc-typing` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Definition fix: let bPossInc accept a nonneg third argument (evalBaseNonnegFun), then restate for a chanPos ;? [basePosition l'] read with the canonical range. Needs owner approval.

- **Status:** FALSE (counterexample, checked in Rocq, no admitted lemmas used). The root cause is BLOCKED-ON-DEFINITION, a type mismatch in the expression language. **This is a modelling bug that affects reachable behaviour, not just this lemma.**
- **Intent:** a listener in `gotMsg m'' l` (it has received a message `[m'', l]`) reads its own position on `chanPos` and moves to `gotRange m'' r`, where `r = |l' - l| - speedMax*msgLatency`.
- **Failure:**
  - **The type bug.** `gotMsg m'' l' := chanPos<vL>? gotRangeN([m'', (|vL, l'|) (-) speedMax (.) msgLatency])` passes the range as an `eSubtract` expression. Both `evalExpFun` and `evalExp` (`evalSub`) evaluate `eSubtract` to a `baseNonneg _`, never to a `baseDistance _`. But `evalBoolExpFun (bPossInc e1 e2 e3)` (and `evalBoolExp`'s `bevalPossInc`) only fires when `e3` evaluates to `Some (baseDistance d)`. So in `currPincCheck m m'' r := !~bPossInc m m'' r $> currCompN.. $+$ bPossInc m m'' r $> badOvlpN` **both guards evaluate to `None` and hence `false` (`evalBoolExpFunTot`)**. The process is stuck (it can only idle via `stepTpIfFalse`). By contrast, `gotRange m'' r` with a genuine `r : Distance` (coerced to `eBase (baseDistance r)`) always has exactly one guard true after reading a mode on `chanMCurr`: `chanBad!` via `badOvlp` if `possIncBool` holds, `chanMStable?` via `currComp` otherwise.
  - **Counterexample, honest input.** Take `p := gotMsg m l` (so `gotMsgState m l p` by `bisim_refl`), `a := chanPos ;? [basePosition l]`, and `p'` its `stepDpIn` derivative. Suppose `p' ~p~ gotRange m r`. `gotRange m r` inputs `chanMCurr;?[m]` to `currPincCheckN [m, m, r]`, which can act. The matching derivative of `p'` is `currPincCheckN [m, m, (|l,l|) (-) speedMax (.) msgLatency]`, which has no discrete transition (lemmas `gotMessage_next_cx_none` and `_none2`: `evalBoolExpFun (bPossInc x y (eSubtract e1 e2)) = None` for **all** `x y e1 e2`). That is a contradiction.
  - The HELPERS of `ProtAuxResults.gotMessage_next.v` contain `gotMessage_next_cx (m) (l) : exists p p' a, p -PA- a -PA> p' /\ gotMsgState m l p /\ ~ exists r, gotRangeState m r p'` and `gotMessage_next_false : (statement) -> forall m l, False`. They compile under `--explore`. `Print Assumptions` shows only model axioms plus `proof_irrelevance`, `functional_extensionality_dep` and `ClassicalDedekindReals`.
  - **Second independent problem (as w1b-06 also noted):** at process level `a` can be `chanPos ;? [v]` for any single value `v`, e.g. `baseMode _`. Then `eDist` fails to evaluate, giving the same stuck derivative. So even after fixing the type bug, the statement needs the action restricted to a position input.
- **Consequence beyond this lemma (for the owner):** in the current model every listener that processes an incoming message (`listening -> gotMsg -> gotRange -> currPincCheck`) gets **permanently stuck** at `currPincCheck`. It never reaches `badOvlp` (so it never signals `chanBad` to start a fail-safe transition), and it never returns to `listening`. The admitted lemmas that describe the message-handling path (`gotMessage_next`, `gotMsg_gotRange_track_ent`, `msgAbortPath`/`msgBadPath` tracking, `incomp_tfs`, ...) therefore don't describe the actual semantics. Arguments in the safety chain that rely on incompatible messages triggering `tfs` rest on false lemmas until this is fixed. `nextPincCheck` has the same `bPossInc` issue with the same `r`.
- **Ripple-up:** `in_safety_cone=False` per `show`. Used in `NARIncomp.v:131` (inside the `msgAbortPathNet` preservation proof, case `gotMsg`), together with `gotMsg_gotRange_track_ent`, which is also false (see `w1b-06`).
- **Suggested fix (definition, needs owner approval):** let `bPossInc` accept any nonneg-valued third argument, as timers already do through `evalExpFunTime`/`evalBaseNonnegFun`. In `LanguageFoundations.v`:
  ```coq
  | bPossInc e1 e2 e3 =>
    match (evalExpFun e1), (evalExpFun e2), (evalExpFun e3) with
    | Some (baseMode m1), Some (baseMode m2), Some b3 =>
      option_map (fun d => possIncBool m1 m2 (mkDistance d)) (evalBaseNonnegFun b3)
    | _, _, _ => None
    end
  ```
  The relation needs the matching change: `bevalPossInc : evalExp e1 m1 -> evalExp e2 m2 -> evalExp e3 b -> b \_/ d -> evalBoolExp (bPossInc e1 e2 e3) (possIncBool m1 m2 (mkDistance d))`. Then restate the lemma for a position read with the canonical range:
  ```coq
  Theorem gotMessage_next (p p' : ProcTerm) (m'' : Mode) (l l' : Position) :
    p -PA- chanPos ;? [basePosition l'] -PA> p' -> gotMsgState m'' l p ->
    gotRangeState m'' (mkDistance (dist2d l' l -nn- speedMax *nn* msgLatency)) p'.
  ```
  The existential form `exists r, gotRangeState m'' r p'` is also fine under that action restriction. Why provable: by `bisim_disc_match`, `gotMsg` is the only source, and its derivative is `gotRangeN [m'', E]` with `E` evaluating to the same nonneg as the literal. A cofix bisimulation "up to expression evaluation" over the finite derivative set `gotRange -> currPincCheck -> {currComp -> nextPincCheck -> {listening, abortOvlp}, badOvlp}` closes it. The user in `NARIncomp` gets `a = chanPos;?[basePosition l]` from the entity step (`stepDePosRead`, with reachability excluding other `chanPos` writers).
- **Partial proof:** none for the target. The verified counterexample is in the `.v` file.

### `ProtAuxResults.gotRange_next`

- **Where:** `src/ProtAuxResults.v` line 531 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Expose the action: exists b, a = chanMCurr ;? [b] /\ (forall m, b = baseMode m -> currPincCheckState m m'' r p') (writer proved it with copied helpers).

- **Status:** FALSE (counterexample, machine-checked). **The statement implies `Mode -> False`**, so it is inconsistent with the model axioms whenever `Mode` is inhabited. Add it to the known-inconsistent list.
- **Intent:** a listener in `gotRange m'' r` reads the current mode `m` on `chanMCurr` and moves to `currPincCheck m m'' r`.
- **Failure:** `gotRange m'' r = chanMCurr<vM>? currPincCheckN [vM, m'', r]`. `stepDpIn` accepts **any** base value of the right arity, so `gotRange m'' r -PA- chanMCurr ;? [baseTime zeroTime] -PA> currPincCheckN $([zeroTime, m'', r])$`. In that derivative both guards, `!~bPossInc zeroTime m'' r` and `bPossInc zeroTime m'' r`, fail to evaluate because the first argument is not a mode. `evalBoolExpFunTot` maps both to `false`, so the derivative has **no discrete step**. For every genuine `m : Mode`, `currPincCheck m m'' r` does have a discrete step: `chanBad *!` via `badOvlp` if `possIncBool m m'' r = true`, else `chanMStable *?` via `currComp`. So no `m` makes the two bisimilar.
  Checked in Rocq (`--explore`, rc=0, HELPERS of `ProtAuxResults.gotRange_next.v`). It uses no admitted lemma, and `Print Assumptions` shows only model axioms, proof irrelevance, functional extensionality and the stdlib reals axioms:
  - `gotRange_next_inert` (the ill-typed derivative is stuck)
  - `gotRange_next_step` (`currPincCheck m m'' r` always steps)
  - `gotRange_next_refuted : (target statement) -> Mode -> False`
  This is the same defect w1b-06 found for `currComp_next`. Their note already predicted it for `gotRange_next` and `gotMessage_next`.
- **Ripple-up:** not in the safety cone. One user: `NARIncomp.v:155` (`msgAbort_not_nextSince`, case 2 "gotRange"). That `Qed` proof therefore rests on an inconsistent assumption, though there the step comes from an entity transition. The listener's `chanMCurr` input can only synchronise with the mode state (`stepDeCurrRead`, value `baseMode m`). Process-internal `chanMCurr` outputs (`switchCurr`, `tfsCurr`) carry `[]`, so the arity check blocks them. Nothing true is lost by restricting the lemma.
- **Suggested fix:** expose the action, and conclude only for well-typed values:
  ```coq
  Theorem gotRange_next (p p' : ProcTerm)
    (a : DiscAct) (m'' : Mode) (r : Distance) :
    p -PA- a -PA> p' -> gotRangeState m'' r p ->
    exists b, a = chanMCurr ;? [b] /\
    (forall m, b = baseMode m -> currPincCheckState m m'' r p').
  ```
  **This corrected statement is proved** (`gotRange_next_fixed` in the same HELPERS, compiled at the target's position). It reuses the forward-tracking helpers of ProtAuxResults-1's accepted `currOK_next`, copied under the prefix `gotRange_next_cp_`. At `NARIncomp.v:155` the user then gets `a = chanMCurr ;? [b]`. Inverting the entity step (`stepDeCurrRead`) gives `b = baseMode m` with `m = currModeMState k`, which is exactly what `gotRange_currPincCheck_track_ent` is later used for. An alternative with the same strength adds the hypothesis `forall b, a = chanMCurr ;? [b] -> exists m, b = baseMode m` and keeps the old conclusion.
- **Partial proof:** the proof of the fixed statement (`gotRange_next_fixed`) is in the `.v`. If the owner approves the restated lemma, it can be spliced with its helpers. Its body:
  ```coq
  intros TR CS. unfold gotRangeState in CS. unfold gotRange in CS.
  gotRange_next_cp_fwd_pre.
  all: eexists; split; [reflexivity | ]; intros m0 Eb; subst;
    unfold currPincCheckState; eapply bisim_trans; [eassumption | ];
    gotRange_next_cp_unfold_app; apply bisim_refl.
  ```

### `ProtAuxResults.currComp_next`

- **Where:** `src/ProtAuxResults.v` line 536 · **Theorem** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis (forall v, a = chanMNext ;? v -> exists m, v = [baseMode m]) or expose the action in the conclusion; caller discharges it from stepDeNextRead.

- **Status:** FALSE (counterexample, Rocq-checked). The statement implies `False` given any `m'' : Mode` and
  `r : Distance`, so this admitted lemma is **inconsistent with the model axioms** whenever `Mode` is inhabited.
  Add it to the known-inconsistent list.
- **Intent:** a listener in `currComp m'' r` steps either to `listening` (on `chanMStable?`) or to
  `nextPincCheck m m'' r` (on `chanMNext?[m]`).
- **Failure:** `currComp m'' r = chanMStable? listeningN $+$ chanMNext<vM'>? nextPincCheckN [vM', m'', r]`, and
  `stepDpIn` accepts **any** base value of the right arity, e.g. `chanMNext ;? [baseTime zeroTime]`. The derivative
  `nextPincCheckN [zeroTime, m'', r]` is **stuck**. Both guards `!~bPossInc ..` and `bPossInc ..` fail to evaluate
  (first argument not a mode), so `evalBoolExpFunTot` gives `false` for both. Every `nextPincCheck m m'' r` with
  `m : Mode` has a discrete action (`chanAbort *!` if `possIncBool m m'' r = true`, else `listening`'s `chanPause ;? []`),
  and so does `listening`. So neither disjunct holds. Checked in Rocq (`--explore`, rc=0; full script in the `.v`):
  ```
  Lemma currComp_next_cex (m'' : Mode) (r : Distance) :
    (forall p p' a, p -PA- a -PA> p' -> currCompState m'' r p ->
       (exists m, nextPincCheckState m m'' r p') \/ listeningState p') -> False.
  ```
  Helpers: `currComp_next_stuck` (derivative has no discrete step), `currComp_next_bisim_act`,
  `currComp_next_listening_act`.
- **Ripple-up:** not in the safety cone. One user: `NARIncomp.v:177` (`msgAbort_not_nextSince`). There the step
  comes from an entity transition where the mode state outputs `chanMNext .! m` (`stepDeNextRead`), so the input is
  always `[baseMode m]`. Nothing true is lost by restricting the lemma.
- **Same defect elsewhere (not my targets, likely the same verdict):** `gotRange_next` (input `chanMCurr ;? [b]`
  with `b` not a mode makes `currPincCheckN` stuck) and `gotMessage_next` (input `chanPos ;? [b]` with `b` not a
  position gives an ill-typed distance, so `currPincCheck` gets stuck one step later). Every `*_next` forward-tracking lemma
  whose continuation guards on a `bPossInc`/`bSufficient` of the input value should be checked for this.
- **Suggested fix:** restrict the input to well-typed values. Either add a hypothesis
  ```
  Theorem currComp_next (p p' : ProcTerm) (a : DiscAct) (m'' : Mode) (r : Distance) :
    p -PA- a -PA> p' -> currCompState m'' r p ->
    (forall v, a = chanMNext ;? v -> exists m, v = [baseMode m]) ->
    (exists m, nextPincCheckState m m'' r p') \/ listeningState p'.
  ```
  or make the conclusion carry the action:
  `(exists m, a = chanMNext ;? [baseMode m] /\ nextPincCheckState m m'' r p') \/ (a = chanMStable *? /\ listeningState p') \/ (exists b, a = chanMNext ;? [b] /\ forall m, b <> baseMode m)`.
  Both are provable by the forward-tracking idiom used for `currOK_next` (bisim to `currComp`, invert its steps,
  unfold `nextPincCheckN`/`listeningN` with an app-unfolding bisim lemma). At `NARIncomp.v:177`, the extra hypothesis is
  discharged from the entity step (`stepDeNextRead` gives `chanMNext ;? [baseMode m]`).

### `ProtAuxResults.tfsStart_next`

- **Where:** `src/ProtAuxResults.v` line 550 · **Lemma** · 2015 label: `#fwd-track` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `untyped-input` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Restrict to a mode read: p -PA- chanMCurr ;? [baseMode m] -PA> p' -> tfsStartState p -> tfsNextState m p' (proved, model axioms only).

- **Status:** FALSE (counterexample, machine-checked). **The lemma is inconsistent with the model axioms alone: it proves `False` without any hypothesis, not even an inhabited `Mode`.**
- **Intent:** From `tfsStart = chanMCurr$<vM>$? tfsNextN $(eVar vM)$`, any discrete step leads to `tfsNext m` for the mode `m` that was read.
- **Failure:** `stepDpIn` lets a process input **any** `BaseType` list of the right length, not only modes. Take `tfsStart -PA- chanMCurr ;? [baseTime zeroTime] -PA> p'`, where `p' = tfsNextN $([eBase (baseTime 0)])$`. Its body is `chanMNext$<eFailSafeSucc (baseTime 0)>$! … $+$ chanMStable! …`.

  For every `m : Mode`, `tfsNext m` can do `chanMNext ;! [baseMode (failSafeSucc m)]` (`tfsNext_mNext_out`). `p'` cannot, because `evalExp (eFailSafeSucc (eBase (baseTime 0))) _` has no derivation. So `~ p' ~p~ tfsNext m`.

  Verified as `tfsStart_next_cex : ~ (statement)` in `w1b-15/ProtAuxResults.tfsStart_next.v` (`Qed`). `Print Assumptions` lists only model-axiom declarations and stdlib classical/FE/PI.
- **Ripple-up (important):**
  - `EntAuxResults.tfsStart_next_ent` (**in safety cone**) is also **FALSE** for unreachable entities. Counterexample, verified in `w1b-15/EntAuxResults.tfsStart_next_ent.cex.v`, lemma `tfsStart_next_ent_cex (k : ModeState) : ~ (statement)`, `Qed`, model axioms only:
    - The entity is `[| chanMCurr$<[baseTime 0]>$! nilProc $||$ tfsStart $||$ nilProc, origin, emptyIface, k |]`.
    - The broadcaster slot syncs a *time* into the overlap component (`stepDpSyncLR`, `stepDeProcTau`).
    - The result is neither `tfsStartStateEnt` nor `tfsNextStateEnt m` for any `m`.
  - **steal-2 has `EntAuxResults.tfsStart_next_ent.ok`, and its proof calls `tfsStart_next`. That proof must be rejected.** `ProtAuxResults.tfsStart_next` and `EntAuxResults.tfsStart_next_ent` should both go into `blacklist_hard.txt`.
  - Further up: `NetAuxBasics.tfsStart_next_net` (Qed, by `fwd_track_net_tac tfsStart_next_ent`) and `NetAuxBasics.tfs_currMode_disc_pres` (uses `tfsStart_next_net`; no reachability hypothesis). Both inherit the problem. The same entity, placed in a network with `currMode_intro`, falsifies them (not separately machine-checked).
- **Suggested fix:**
  - Prot level, restricting to reading a mode:
    ```coq
    Lemma tfsStart_next (p p' : ProcTerm) (m : Mode) :
      p -PA- chanMCurr ;? [baseMode m] -PA> p' -> tfsStartState p -> tfsNextState m p'.
    ```
    **Proved** (as `tfsStart_next_fixed`, `Qed`, no admitted dependencies; model axioms and stdlib only) in `w1b-15/ProtAuxResults.tfsStart_next.v`, together with the helper `tfsStart_next_app_bisim` (`n $( l )$ ~p~ body[l/xs]`).
    - Alternative that keeps the original shape: `(exists m, a = chanMCurr ;? [baseMode m] /\ tfsNextState m p') \/ (exists b, a = chanMCurr ;? [b] /\ forall m, b <> baseMode m)`.
  - Entity level: add `reachableEnt e ->` (stub) to `tfsStart_next_ent`, and `reachableNet n ->` to `tfsStart_next_net` and `tfs_currMode_disc_pres`. Under reachability, the broadcaster and listener never output on `chanMCurr` (`bc_mCurr_out_not`, `listen_mCurr_out_not`). The only way to the overlap's `chanMCurr` input is then `stepDeCurrRead` with the mode state's `chanMCurr .! m`, which carries a mode, and the fixed prot lemma applies. This is BLOCKED-ON-STUB (`reachableEnt`) until the stub is defined.
- **Partial proof:** `tfsStart_next_cex`, `tfsStart_next_app_bisim` and `tfsStart_next_fixed` are in `w1b-15/ProtAuxResults.tfsStart_next.v`.

### `ProtAuxResults.paused_switch`

- **Where:** `src/ProtAuxResults.v` line 834 · **Theorem** · 2015 label: `5` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:reachableProt-allows-unsynchronised-internal-actions` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Definition change: restrict reachableProt steps to entity-visible actions (internal channels only via tau), or delete and prove paused_switch_net directly by induction on reachableNet.

- **Status:** FALSE (counterexample, verified in Rocq; uses no admitted lemmas)
- **Intent:** in a reachable protocol process `p1 | p2 | p3`, the listener `p3` is `paused` exactly when the overlap `p2` is in a switch state (`switchBc m`, `switchCurr` or `switchListen`). Pausing and unpausing happen only through the synchronisations `ovWait --chanPause!--> switchBc` ∥ `listening --chanPause?--> paused` and `switchListen --chanUnpause!--> dormant` ∥ `paused --chanUnpause?--> listening`.
- **Failure:** `reachableProt` (ProtAuxDefs.v:240) is closed under **every** process step `p -PA- a -PA> p'`, including unsynchronised half-actions on the protocol's internal channels. The parallel rules `stepDpParL`/`stepDpParR` let a single component input or output on its own. So the listener can take `chanPause?` alone, without any synchronisation:
  `procProtocol = sleeping | dormant | listening  --chanPause *?-->  sleeping | dormant | pausedN`.
  This target is reachable, and `pausedN ~p~ paused`, so `pausedStateProt` holds. But `dormant` enables `chanAbort *?`, which no switch state (`switchBc`, `switchCurr`, `switchListen`) can match, so `~ switchStateProt`. The script compiles at the target's position with `--explore`. It is adapted from ProtAuxResults-3's draft, with the `S` Ltac-binding bug fixed. The helper tactics `paused_switch_inv`/`paused_switch_noact` (a copy of `link_reach_triple_tau_noact`) are in `w1b-09/ProtAuxResults.paused_switch.v`.
  ```coq
  Lemma paused_switch_reach : reachableProt (sleeping $||$ dormant $||$ pausedN).
  Proof.
    eapply reachprDisc; [apply reachprBase | ].
    unfold procProtocol. apply stepDpParR. apply stepDpParR.
    unfold listening. apply stepDpChoiceL. apply stepDpChoiceR.
    instantiate (1 := chanPause *?). apply stepDpIn. reflexivity.
  Qed.
  (* + paused_switch_pausedN : pausedN ~p~ paused   (unfold app via def)
     + ~ switchStateProt (... dormant ...)   (dormant enables chanAbort*?, no switch state does) *)
  Lemma paused_switch_refuted :
    ~ (forall p, reachableProt p -> (pausedStateProt p <-> switchStateProt p)).
  ```
  The converse direction fails in the same way: an unsynchronised `chanPause!` by `ovWait` reaches `switchBc` while the listener is still `listening`.
- **Ripple-up:**
  - In-file: used by `EntAuxResults.switchListen_urgent` (EntAuxResults.v:364).
  - **Safety cone (important):** `NetAuxBasics.paused_switch_net` (in the safety cone) was accepted in wave 1 (`NetAuxBasics-2/NetAuxBasics.paused_switch_net.v`) with a proof that is just `link_net_prot_reach` + `paused_switch`. If that proof is spliced, the safety cone rests on this **false** lemma. `paused_switch_net` is used by NARIncomp.v:394 and NARInsuff.v:68, 463-464.
  - `paused_switch_net` itself is plausibly **true**. At entity level, internal-channel half-actions cannot fire: `stepDiscEnt` lifts only `tau` and the entity-interface channels. The information is lost in the projection `reachableNet → reachableProt`.
- **Suggested fix (definition change, needs owner approval):** restrict `reachableProt` to process steps that the entity semantics can actually lift. Internal channels (`chanPause`, `chanUnpause`, `chanAbort`, `chanBad`, `chanWake`, `chanTrans`) must synchronise.
  ```coq
  Inductive entVisibleAct : DiscAct -> Prop :=
    | evTau : entVisibleAct tauAct
    | evOutProc v : entVisibleAct (chanOutProc ;! v)
    | evInProc v : entVisibleAct (chanInProc ;? v)
    | evAN v : entVisibleAct (chanAN ;? v)
    | evStableIn : entVisibleAct (chanMStable *?)
    | evStableOut : entVisibleAct (chanMStable *!)   (* if WRITE-STBL is added, see below *)
    | evCurrOut : entVisibleAct (chanMCurr *!)
    | evCurrIn v : entVisibleAct (chanMCurr ;? v)
    | evNextOut v : entVisibleAct (chanMNext ;! v)
    | evNextIn v : entVisibleAct (chanMNext ;? v)
    | evPosIn v : entVisibleAct (chanPos ;? v).
  Inductive reachableProt : ProcTerm -> Prop :=
    | reachprBase : reachableProt procProtocol
    | reachprDisc (p p' : ProcTerm) (a : DiscAct) : reachableProt p ->
      entVisibleAct a -> p -PA- a -PA> p' -> reachableProt p'
    | reachprDel (p p' : ProcTerm) (d : Delay) : reachableProt p ->
      p -PD- d -PD> p' -> reachableProt p'.
  ```
  `link_net_prot_reach` / `reachable_ent_prot` stay provable, since every `stepDiscEnt` rule moves the process with one of these actions or leaves it fixed. With this definition `paused_switch` is a routine induction on `reachableProt`. The invariant is the biconditional itself. `chanPause`/`chanUnpause` now only occur inside `tau` synchronisations between overlap and listener, and the `tfsListen --chanUnpause!--> dormant` ∥ `listening --chanUnpause?--> listening` sync keeps both sides non-switch/non-paused.
  - Alternative that leaves `reachableProt` alone: delete `paused_switch` and prove `paused_switch_net` directly by induction on `reachableNet`, through an entity-level `paused_switch_ent` under `reachableEnt`.
- **Side note:** the entity semantics also lacks the thesis WRITE-STBL rule; see `w1b-09/EntAuxResults.ovAbort_unstable.fail.md`. Separately, `reachableProt_triple` (ProtAuxResults.v:843) concludes `protocolState`, whose `overlapState` only covers `dormant`/`ovWait` ("INCOMPLETE" comment, ProtAuxDefs.v:126), so it is false for reachable `init`/`ovReady`/… states, with or without this fix.
- **Partial proof:** none for the target (it is false). The counterexample is in `w1b-09/ProtAuxResults.paused_switch.v` (HELPERS).

### `ProtAuxResults.gotMsg_state`

- **Where:** `src/ProtAuxResults.v` line 922 · **Lemma** · 2015 label: `6` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:missing-protocolState-hypothesis (p unconstrained)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add protocolState p (or reachableProt p); writer proved this fixed form in explore mode (not re-checked here); user incomp_incomingNet_bad then needs reachableNet n.

- **Status:** FALSE (counterexample) / NEEDS-HYPOTHESIS (`protocolState p`)
- **Intent:** if a *protocol* process `p` inputs `[m, l]` on `chanInProc`, then its
  listener component ends up in `gotMsgState m l`, i.e. `gotMsgStateProt m l p'`.
  The source comment already says: "NEEDS TO BE EDITED! PROTOCOL PROCESS HYPOTHESIS
  DOESN'T LOOK LIKE IT'S THERE."
- **Failure:** `p` is unconstrained. Take
  `p := chanInProc $<[vM'', vL']>$? nilProc`. By `stepDpIn`,
  `p -PA- chanInProc;? [baseMode m, basePosition l] -PA> nilProc`, because
  `subProcTerm _ nilProc = nilProc`. But `gotMsgStateProt m l nilProc` needs
  `nilProc = p1 $||$ p2 $||$ p3`, so it fails. This was checked in Rocq (`--explore`, compiles with `Qed`):
  ```coq
  Lemma gotMsg_state_cex m l : ~ (forall p p',
    p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p').
  Proof.
    intro H.
    assert (TR : (chanInProc $<[vM'', vL']>$? nilProc) -PA-
      chanInProc;? [baseMode m, basePosition l] -PA> nilProc).
    { change nilProc with (subProcTerm (listsToSub [vM'', vL']
        (listBaselistExp [baseMode m, basePosition l])) nilProc) at 2.
      constructor. reflexivity. }
    specialize (H _ _ TR). inversion H.
  Qed.
  ```
  So the statement is false for every `m`, `l`. It can't be refuted outright in Rocq only
  because `Mode` is an abstract `Axiom` type that might be empty.
- **Ripple-up:** used only in `NARIncomp.incomp_incomingNet_bad` (line 77, which ends in `Qed`).
  That lemma is used by `NARIncomp.instant_incomp_tfs` (line 407). `show` reports
  `in_safety_cone=False` for `gotMsg_state`. At the use site, `Q0` is the software transition
  of entity `i` in network `n`. `incomp_incomingNet_bad` has no reachability hypothesis,
  so the corrected lemma can't be applied there without one more premise.
- **Suggested fix:**
  ```coq
  Lemma gotMsg_state p p' m l : protocolState p ->
    p -PA- chanInProc;? [baseMode m, basePosition l] -PA> p' -> gotMsgStateProt m l p'.
  ```
  (`reachableProt p ->` would also do, via `reachableProt_triple`.) **This corrected version is
  proved** (`--explore`, `Qed`). It uses the HELPERS of my accepted proofs of
  `prot_outProc_in_not` and `ovlp_abort_in`. Those are the Ltacs `prot_outProc_in_not_*` and the lemmas
  `ovlp_abort_in_bisim_step` and `ovlp_abort_in_appbisim`:
  ```coq
  Proof.
    intros PS TR. inversion PS as [p1 p2 p3 BS OS LS]; subst; clear PS.
    inversion TR; subst; clear TR.
    - inversion BS; prot_outProc_in_not_contra.
    - match goal with [V : p2 $||$ p3 -PA- _ -PA> _ |- _] =>
        inversion V; subst; clear V end.
      + inversion OS; prot_outProc_in_not_contra.
      + unfold gotMsgStateProt. constructor.
        inversion LS as [B|m0 B|m0 B|B|B|m0 r B]; prot_outProc_in_not_unfold;
          try prot_outProc_in_not_contra.
        match goal with [V : p3 -PA- _ -PA> _ |- _] =>
          destruct (ovlp_abort_in_bisim_step _ _ _ _ B V) as [q'' [TQ BQ]] end.
        unfold listening in TQ. prot_outProc_in_not_inv.
        eapply bisim_trans; [exact BQ | ].
        eapply bisim_trans; [apply ovlp_abort_in_appbisim | ].
        simpl. remove_resets. remove_updates. apply bisim_refl.
  Qed.
  ```
  The user needs a matching change. Add `reachableNet n ->` to
  `incomp_incomingNet_bad`. In its proof, get `protocolState p` from
  `reachableProt_triple (link_net_prot_reach rn H)`, where `H` is the entity-in-network
  hypothesis, and pass it to `gotMsg_state`. The only caller is `instant_incomp_tfs`, inside the
  `receivedDisc` case of `dependent induction`. There the pre-state reachability proof
  `p : reachableNet n` is in scope, so it can pass it.
- **Partial proof:** see `ProtAuxResults.gotMsg_state.v` in this directory. Its HELPERS
  contain both the counterexample and the corrected lemma. The target itself is left `Admitted`.

## NARInsuff

### `NARInsuff.insuff_incomingNotif_abort`

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

### `NARInsuff.insuff_incomingNotif_bad`

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

### `NARInsuff.tfs_state_rel`

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

## NARNonFS_currSince

### `NARNonFS_currSince.switchCurr_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 114 · **Theorem** · 2015 label: `2` · **in safety cone:** yes
- **Audit:** unaudited

- **Status:** FALSE (in any model with two or more modes; not refutable inside Rocq because `Mode` is abstract)
- **Intent:** An entity in switchCurr has been `nextSince` its next mode, so `currSinceBase` can pass the timestamp on.
- **Failure:** `forall m, switchCurrStateNet i n -> exists t, nextSince m t i n p` leaves `m` unconstrained. `nextSince m` is only created by `nextSinceBase`, an ovReady m → ovWait m step, and the mode is fixed within each stretch. So for a switchCurr entity whose transition was to `m0`, the statement fails for every `m <> m0`.
- **Ripple-up:** In the safety cone. It is used only by `nonFS_currSince`, where `m` is the current mode of `n'`, which feeds the currSince chain in NARIncomp and NARTop.
- **Suggested fix:** `switchCurrStateNet i n -> exists m t, nextSince m t i n p`. Then in `nonFS_currSince`, identify `m` via `switchCurr_nextSince_nextMode_net`, `switch_states_mState` and a new `currModeNet_unique`. Alternatively add the hypothesis `nextModeNet m i n`.

### `NARNonFS_currSince.ovWait_nextSince_pending`

- **Where:** `src/NARNonFS_currSince.v` line 31 · **Theorem** · 2015 label: `In the discrete inductive case, we backtrack for cases of the previous state.` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS (ordering and dependencies)
- **Intent:** An entity in ovWait is `pending` or `nextSince m`.
- **Failure:** It is a mutual induction with `ovReady_nextSince_pending`. The delay cases need `pending_urgent`, which is stated later in the file. A scratch proof compiled, but it used `ovWait_prev_net_strong`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, which are all inconsistent as stated.
- **Ripple-up:** `ovWait_zero_nextSince`, then `switchBc_nextSince`, then `switchCurr_nextSince`, then `nonFS_currSince`.
- **Suggested fix:**
  1. Move `pending_urgent` first.
  2. Restate the backtracking lemma for ovWait: the predecessor is ovWait, ovReady (with `x = t`, `y = period`) or init (with `x = t`, `y = 0`).
  3. Restate backward delay preservation with `x+d` and `y+d`, guarded by `d <=` the remaining timer.
  4. Prove both targets by mutual induction on `p`.

### `NARNonFS_currSince.ovReady_nextSince_pending`

- **Where:** `src/NARNonFS_currSince.v` line 49 · **Theorem** · 2015 label: `Discard base case as initiality contradicts the state predicate` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS. This is the second conjunct of the mutual lemma with `ovWait_nextSince_pending`; see that write-up.

### `NARNonFS_currSince.pending_urgent`

- **Where:** `src/NARNonFS_currSince.v` line 80 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** A pending entity cannot delay.
- **Plan:** Induction on `pending`.
  - **ovReady case:** contradiction via `del_ovlp`. The delaying overlap is dormant, tfsCurr or ovWait, all of which can input `abort`; ovReady cannot.
  - **ovWait case:** needs `y = 0` for pending ovWait states, plus entity-level urgency of ovWait with `y = 0`.
- **Suggested fix:** The statement is fine. Add `ovWait_pos_urgent : reachableEnt e -> ovWaitStateEnt m t x zeroTime e -> e -ED- d ->> e' -> False`.

### `NARNonFS_currSince.ovWait_zero_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 90 · **Theorem** · 2015 label: `2` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (needs consistent backtracking and delay lemmas)
- **Intent:** ovWait with `x = 0` implies `nextSince`.
- **Failure:** A `Qed` proof existed, but it used `ovWait_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, both inconsistent as stated. Everything else in it is consistent: for example, init → ovWait never gives `x = 0`, because of `period_positive`. The prover reverted it.
- **Suggested fix:** The statement is fine. It becomes provable once timer-correct versions of the ovWait backtracking and backward-delay lemmas exist.

### `NARNonFS_currSince.switchBc_nextSince`

- **Where:** `src/NARNonFS_currSince.v` line 103 · **Theorem** · 2015 label: `2` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION
- **Intent:** switchBc m implies `nextSince m`.
- **Failure:** A `Qed` proof existed, but it used `reachableProt_triple` (to get the triple shape and `overlapState`, both incomplete) and `ovWait_del_pres`, both inconsistent as stated, plus `ovWait_zero_nextSince`. The prover reverted it.
- **Suggested fix:** The statement is fine. Either:
  - restate `switchBc_prev` without the `overlapState` premise, or complete `overlapState`;
  - and use a timer-correct `ovWait_del_pres` (`ovWait m t x y -d-> ovWait m t (x-d) (y-d)`).

## NAROvlpTime

### `NAROvlpTime.nextSince_switchCurr_lower`

- **Where:** `src/NAROvlpTime.v` line 125 · **Theorem** · 2015 label: `1` · **in safety cone:** yes
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

### `NAROvlpTime.pending_urgent`

- **Where:** `src/NAROvlpTime.v` line 28 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE in the current semantics (argued; consistent with w1b-13's machine-checked finding on `noSyncNow`)
- **Intent:** A pending entity (ovWait right after init, or ovReady) cannot delay.
- **Failure:** With `y = 0`, `del 0 (chanPos?..)` can delay, because input prefixes delay (`stepTpIn`), and after init `x = tw + P > 0`. `stepTeDel` only requires `noSync` with the interface and the mode state. The local position read `stepDePosRead` doesn't block a delay, unlike the thesis's noComm clause (Def 4.22).
- **Ripple-up:** It has no users. `NARNonFS_currSince` has a separate lemma of the same name.
- **Suggested fix (semantics):** Add `forall l', ~ discActEnabled p (chanPos ;? [basePosition l'])` to `stepTeDel`/`noSyncNow`, restoring the thesis's rule.

### `NAROvlpTime.pending_time1`

- **Where:** `src/NAROvlpTime.v` line 39 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NOT-FOUND-YET (believed true)
- **Intent:** In ovWait while pending, `u = tw(m0, m) + P`.
- **Failure:** Induction on `pending` works except the base case. That needs: from `initStateNet m0 i n`, a step `n -a-> n'` and `ovWaitStateNet m u x y i n'`, conclude `exists m1 q, u = waitTime m1 m q +t+ period m`. No lemma gives the value of `t`, and `init_ovWait_track_net` in NARTop only gives `x = t` and `y = 0`.
- **Ripple-up:** `pending_time2`, then `nextSince_ovWait_ovReady_time`, then the `*_lower` lemmas, then `safety`.
- **Suggested fix:** Add a tracking lemma `init_ovWait_track_time_net : initStateNet m i n -> ovWaitStateNet m' t x y i n' -> n -NA- a -NA> n' -> exists m0 q, t = addTime (waitTime m0 m' q) (period m')`.

### `NAROvlpTime.pending_time2`

- **Where:** `src/NAROvlpTime.v` line 52 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

### `NAROvlpTime.nextSince_ovWait_ovReady_time`

- **Where:** `src/NAROvlpTime.v` line 66 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

### `NAROvlpTime.nextSince_switchBc_lower`

- **Where:** `src/NAROvlpTime.v` line 110 · **Theorem** · 2015 label: `1` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** BLOCKED-ON-DEFINITION (proved conditionally; the proof uses admitted lemmas that are inconsistent as stated)
- **Intent:**
  - `switchCurr_lower` / `switchBc_lower`: in the switch states, t > mL + max(AN, transMax).
  - `ovWait_ovReady_time`: the timing invariants t + x = tw and u + y = x + P in ovWait, and t + u = tw + P in ovReady.
  - `pending_time2`: in ovReady while pending, u = tw + P.
- **Failure:** A complete proof exists in the cloud session, kept as an optional patch, but it goes through only via:
  1. `reachableProt_triple`, to get `overlapState` of the previous component;
  2. `nextSince_del_ovWait` plus `ovWait_del_pres_net`, for the delay cases;
  3. `ovWait_prev_net`, `ovReady_prev_net_strong` and `ovWait_del_pres_bkwd_net_strong`, for backtracking.

  All of these are inconsistent as stated. Everything else in the proof is sound, including the bisimulation exclusivity lemmas and tw > mL + max(AN, transMax).
- **Ripple-up:** `nextSince_switchCurr_lower` is in the safety cone; the chain goes through NARTop to `safety`.
- **Suggested fix:** Add sound versions of the support lemmas, then re-apply the existing proof skeleton:
  - (a) an overlap-component invariant for reachable processes, weaker than `reachableProt_triple`;
  - (b) a sound "nextSince ∧ delay ⇒ ovWait";
  - (c) sound backward-delay and backtracking lemmas for ovWait/ovReady, with the timer arithmetic right and `reachableNet` hypotheses.

## InterfaceLanguage

### `InterfaceLanguage.inList_received_in`

- **Where:** `src/InterfaceLanguage.v` line 361 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `typo (copy-paste from outList_received_in: stepIlBuff stamps zeroTime, not msgLatency)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Conclude <(v, zeroTime)> _: inList l' (proved, model axioms only), or delete the conjecture (no users).

- **Status:** FALSE (counterexample)
- **Intent:** after an input list buffers `v` (rule `stepIlBuff`), `v` is in the list with its initial timestamp.
- **Failure:** `stepIlBuff` stamps the new element with `zeroTime`, not `msgLatency`
  (the statement was copy-pasted from `outList_received_in`, where `stepOlBuff` does use `msgLatency`).
  The lift case is vacuous (timed lists have no input rule), so `l' = mkInputList (<(v, zeroTime)> :: inList l)`.
  Counterexample: `l := mkInputList []`, `v := []`, `l' := mkInputList [<([], zeroTime)>]` via `stepIlBuff [] []`.
  The conclusion needs `<([], zeroTime)> = <([], msgLatency)>`, i.e. `0 = msgLatency`, which contradicts `msgLatency_positive`.
  Rocq check (compiles, `--explore`): `inList_received_in_false : ~ (forall l l' v, l -il- v ?? -il> l' -> <(v, msgLatency)> _: inList l')`
  in `InterfaceLanguage.inList_received_in.counterexample.v`.
- **Ripple-up:** no users anywhere in the frozen sources (`grep -n inList_received_in *.v` hits only the declaration). Not in the safety cone. Nothing breaks.
- **Suggested fix:**
  ```coq
  Lemma inList_received_in : forall (l l' : InputList) (v : list BaseType),
    l -il- v ?? -il> l' -> <(v, zeroTime)> _: inList l'.
  Proof.
    intros l l' v H. inversion H; subst.
    - simpl. left. reflexivity.
    - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
  Qed.
  ```
  This proof is checked (as `inList_received_in_fixed`) in the counterexample file. Alternatively, delete the conjecture, since nothing uses it.

### `InterfaceLanguage.notifList_received_in`

- **Where:** `src/InterfaceLanguage.v` line 365 · **Conjecture** · 2015 label: `-` · **in safety cone:** no
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `typo (copy-paste: stepNlBuff stamps adaptNotif, not msgLatency)`
- **Fix (audit summary):** Conclude <(v, adaptNotif)> _: notifList l' (proved), or delete (no users).

- **Status:** FALSE in the intended model (independent of the axioms). NEEDS-HYPOTHESIS `msgLatency = adaptNotif` if kept as stated.
- **Intent:** after a notification list buffers `v` (rule `stepNlBuff`), `v` is in the list with its initial timestamp.
- **Failure:** `stepNlBuff` stamps the new element with `adaptNotif`, not `msgLatency` (copy-paste from `outList_received_in`).
  The other `stepNotifList` rules carry delay actions, and the lift case is vacuous (timed lists have no input rule), so
  `l' = mkNotifList (<(v, adaptNotif)> :: notifList l)`.
  Proved in Rocq (`--explore`, compiles): `notifList_received_in_iff : (statement) <-> msgLatency = adaptNotif`
  in `InterfaceLanguage.notifList_received_in.counterexample.v`. The `->` direction instantiates `l := mkNotifList []`, `v := []`.
  The only axioms constraining `msgLatency` and `adaptNotif` are `msgLatency_positive` and `adaptNotif_positive`
  (checked: `grep` over all `Axiom`/`Parameter`/`Conjecture` declarations). So e.g. `msgLatency = 1`, `adaptNotif = 2`
  is consistent with the model, and the statement is unprovable.
- **Ripple-up:** no users anywhere in the frozen sources. Not in the safety cone. Nothing breaks.
- **Suggested fix:**
  ```coq
  Lemma notifList_received_in : forall (l l' : NotifList) (v : list BaseType),
    l -nl- v ?? -nl> l' -> <(v, adaptNotif)> _: notifList l'.
  Proof.
    intros l l' v H. inversion H; subst.
    - simpl. left. reflexivity.
    - match goal with [Htl : stepTimedList _ _ _ |- _] => inversion Htl end.
  Qed.
  ```
  This proof is checked (as `notifList_received_in_fixed`) in the counterexample file. Alternatively, delete the conjecture, since nothing uses it.

### `InterfaceLanguage.inList_pres_input`

- **Where:** `src/InterfaceLanguage.v` line 371 · **Lemma** · 2015 label: `5` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:missing-non-delay-hypothesis (stepIlDel empties any input list)` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis (forall d, a <> atlDel d); fixed lemma and the unchanged user inList_inter_pres_input re-proved (model axioms only).

- **Status:** FALSE (counterexample)
- **Intent:** a timed-out message `<(v, zeroTime)>` in an input list survives any step except the output of `v` itself.
- **Failure:** the rule `stepIlDel : forall l d, l -il- d -il> mkInputList []` lets *any* input list (including one that holds a
  timed-out message) delay and drop everything. The conclusion's left disjunct is then `In _ []` (false), and the right one,
  `atlDel d = v !!`, is a constructor clash.
  Counterexample: `v := []`, `l := mkInputList [<([], zeroTime)>]`, `l' := mkInputList []`, `a := atlDel (mkDelay (mkposreal 1 Rlt_0_1))`.
  Rocq check (compiles, `--explore`): `inList_pres_input_false` in `InterfaceLanguage.inList_pres_input.counterexample.v`.
  The other cases are fine. Buffering conses onto the list. A lifted timed-list delay is impossible when there is a zero
  timestamp (it needs `0 = t' + d` with `d > 0`). A lifted output either removes `<(v,0)>` itself (`a = v!!`) or preserves it.
- **Ripple-up:** used only in the proof of `inList_inter_pres_input` (InterfaceLanguage.v:395/397). That lemma already
  assumes `forall d, a <> aiDel d` and only invokes this lemma on the `?? ` and `!!` input-list steps, so the delay case never
  arises there. `inList_inter_pres_input` is used in NARIncomp.v:64,71. Not in the safety cone.
- **Suggested fix:** add a non-delay hypothesis:
  ```coq
  Lemma inList_pres_input v l l' a :
    (forall d, a <> atlDel d) ->
    <( v, zeroTime )> _: inList l -> l -il- a -il> l' ->
    <( v, zeroTime )> _: inList l' \/ a = v !!.
  ```
  The counterexample file checks a full proof of this (`inList_pres_input_fixed`, with helper `inList_pres_input_tl_out`).
  It also re-proves `inList_inter_pres_input` with its statement unchanged on top of the fixed lemma (`inList_pres_input_user_check`).
  So the only change needed upstream is the proof of `inList_inter_pres_input`: build the non-delay side condition with
  `assert (ND : forall d, act <> atlDel d) by (intros dd EE; discriminate EE)` and pass `ND` first.
- **Partial proof:** see `InterfaceLanguage.inList_pres_input.counterexample.v` (all helpers compile; target left `Admitted`).

## NARIncomp

### `NARIncomp.incomingNet_urgent`

- **Where:** `src/NARIncomp.v` line 30 · **Theorem** · 2015 label: `3` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** NEEDS-HYPOTHESIS (message shape and/or reachability)
- **Intent:** A pending input message forbids a delay.
- **Failure:** `stepIlDel` always lets an input list delay. Urgency can come only from `noSync`, with `listening` accepting `chanInProc v`, and `listening` only inputs 2-element lists. The statement quantifies over arbitrary `v`.
- **Ripple-up:** It is used by `incomp_abort` and `incomp_tfs`, both with `v = [baseMode m', basePosition l']`.
- **Suggested fix:** Restrict `v` to `[baseMode m, basePosition l]`. Proof plan: `link_net_ent_del_bkwd`, then `del_listening_net`, then listening enables `chanInProc ;? [m,l]`, then the interface can output `chanInProc {! v`, which contradicts `noSyncNow`.

### `NARIncomp.incomp_incomingNet_abort`

- **Where:** `src/NARIncomp.v` line 91 · **Theorem** · 2015 label: `3` · **in safety cone:** no
- **Audit:** unaudited

- **Status:** FALSE as stated (missing case), also BLOCKED-ON-STUB (`nextModeNet`)
- **Intent:** A pending message incompatible with the *next* mode either stays incoming or moves the entity onto `msgAbortPath`.
- **Failure:** `mapMsg` also requires the message to be compatible with the *current* mode. If it is incompatible with both modes, consuming it via `gotMsg` lands in `msgBadPathNet i n'`, which is neither disjunct.
- **Ripple-up:** In the safety cone, via `instant_incomp_abort`, then `incomp_abort`, then `incomp_tfs`, then `safety`.
- **Suggested fix:**
  - Add a third disjunct `\/ msgBadPathNet i n'`. `incomp_abort` still works because `msgBadPathNet_urgent` kills that case; note that lemma is itself admitted and refuted without reachability.
  - Define `nextModeNet` via the mode state of the entity at `i`.

## NetAuxDefs

### `NetAuxDefs.msgBad_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 168 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change). No users: could simply be deleted.

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

### `NetAuxDefs.notifBad_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 171 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change). No users: could simply be deleted.

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

### `NetAuxDefs.msgAbort_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 174 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change).

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

### `NetAuxDefs.notifAbort_modeState_eq`

- **Where:** `src/NetAuxDefs.v` line 177 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `stepDeTest-env-mode-change` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Weaken to mState_in_net k i n' \/ (nextModeMState k = None /\ entity i only changed its mode state), and case-split in callers; or remove/restrict stepDeTest (definition change).

- **Status:** FALSE (counterexample, machine-checked).
- **Intent:** while entity `i`'s listener is on a bad/abort path, a discrete network step does not change `i`'s mode state `k`. The `(*LOCAL TIDY*)` sketch argues that a mode change needs the listener paused, which contradicts the path predicate.
- **Failure:** the entity semantics has
  `| stepDeTest : forall p l i k k' m, k -ms- chanMNext .? m -ms> k' -> [|p,l,i,k|] -EA- aeTau ->> [|p,l,i,k'|]`.
  - This rule changes the mode state with no synchronisation by the process. In effect it is the environment requesting a mode change, which `dormant` later reads via `chanMNext?`.
  - The model axiom `failSafeSucc_successor : forall m, m -mtr-> failSafeSucc m` means `stepMsInit` is always enabled from `sing m`.
  - Counterexample:
    - `n = [ [|q,l,h,sing m|] ]`, where `q = badOvlp $||$ badOvlp $||$ badOvlp` (for the `*Bad` lemmas) or `abortOvlp $||$ abortOvlp $||$ abortOvlp` (for the `*Abort` lemmas);
    - `n' = [ [|q,l,h,<|m, failSafeSucc m, modeTransTime …|>|] ]`, reached via `stepDnTauHead` + `stepDeTest` + `stepMsInit`.
  - The path predicate holds via `mbpBad`/`nbpBad`/`mapAbort`/`napAbort` with `bisim_refl`, and `mState_in_net (sing m) 0 n` holds, but `mState_in_net (sing m) 0 n'` fails.
  - The prover proved `~(forall n n' a i k, ...)` for all four with `Qed`. `Print Assumptions` shows only model axioms and stdlib axioms; no admitted lemma is used.
  - Adding `reachableNet n` would not help, because the counterexample state is plausibly reachable.
- **Ripple-up:**
  - `msgAbort_modeState_eq` is used by `NARIncomp.msgAbort_not_nextSince` (line ~110).
  - `notifAbort_modeState_eq` is used by `NARInsuff.notifAbort_not_nextSince` (line ~195).
  - The `*Bad` lemmas have no users.
  - The callers' own statements still look true. Their "process unchanged" branch only needs the path to be preserved, and where `stepDeTest` fires `k` is `sing`, so `mapAbort`/`napAbort` survive. The exception is `napRng`, which needs its own case.
  - What the callers actually rest on is the false equality step (`mState_in_net_unique MSI' NME`). Their proofs need restructuring; their statements don't.
- **Suggested fix:** weaken the lemma to what holds and case-split in the callers:
  `Theorem msgAbort_modeState_eq n n' a i k : msgAbortPathNet i n -> mState_in_net k i n -> n -NA- a -NA> n' -> mState_in_net k i n' \/ (nextModeMState k = None /\ exists p l h k', [|p,l,h,k|] @ i .: n /\ [|p,l,h,k'|] @ i .: n').`
  - Use the same pattern for all four.
  - In the callers, the second disjunct falls into the existing "p unchanged ⇒ path preserved" branch.
  - For the `*Bad` lemmas (no users), either delete them or use the same weakened form.
  - Alternative: remove `stepDeTest` and model mode requests differently. That is a definition change and needs the owner's approval.
  - Not yet verified: the `chanMNext!` and `chanMCurr!` writes in the tfs branch may also change `k` while the listener is on a message path. If so, the second disjunct must also allow an overlap write.

## ProcEquiv

### `ProcEquiv.evalBoolExpFalseTot`

- **Where:** `src/ProcEquiv.v` line 477 · **Theorem** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:ill-formed-expression-evaluates-to-false` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Keep only the -> direction (re-proved, model axioms only) or add evalBoolExpFun e <> None.

- **Status:** FALSE (counterexample, machine-checked in the cloud session; refutes the statement from the definitions alone, so admitting it is inconsistent)
- **Intent:** The `false` counterpart of `evalBoolExpTrueTot`: the relational evaluation gives `false` exactly when the total function returns `false`.
- **Failure:**
  - The `->` direction holds and is already proved in the existing script. The `<-` direction fails.
  - `evalBoolExpFunTot` returns `false` both when the evaluation really is false and when `evalBoolExpFun e = None` (an ill-formed expression). `evalBoolExp` has no derivation for ill-formed expressions.
  - Counterexample: `e := bEqual (eVar (var 0)) (eVar (var 0))`.
  - Refutation proved: `~ (forall e, evalBoolExp e false <-> evalBoolExpFunTot e = false)`.
- **Ripple-up:** None; it has no users and is not in the safety cone.
- **Suggested fix:** Pick one:
  - keep only the `->` direction (already proved);
  - add the premise `evalBoolExpFun e <> None ->` to the iff.

## SoftwareLanguage

### `SoftwareLanguage.delProc_minus_guard`

- **Where:** `src/SoftwareLanguage.v` line 2000 · **Lemma** · 2015 label: `-` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `other:unconstrained-guard-expression` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add hypothesis evalExpFunTime e = Some t (delAddSoft has it in context at the call).

- **Status:** FALSE / NEEDS-HYPOTHESIS (counterexample, machine-checked in the cloud session from the definitions alone, so admitting it is inconsistent)
- **Intent:** If a guard counted down to `t - d` delays by `d'` to `p'`, then the original guard, which evaluates to `t`, delays by `d + d'` to `p'`. This is the `stepTpDelSub` case of `delAddSoft`.
- **Failure:**
  - The guard expression `e` in the conclusion is unconstrained.
  - Counterexample: `t := d`, `p := nilProc`, `e := eVar (var 0)`. The premise holds with `p' := nilProc`. But `evalExpFunTime e = None`, so only `stepTpDelIll` applies, which forces `p' = $<e>$ nilProc`.
  - Refutation proved: `~ (forall t d d' H p p' e, $<minusTime t d H>$ p -PD- d' -PD> p' -> $<e>$ p -PD- d +d+ d' -PD> p')`.
- **Ripple-up:**
  - Its only user is `SoftwareLanguage.delAddSoft`, an existing `Qed` lemma, in the `stepTpDelSub` case, where `evalExpFunTime e = Some t` is already in context.
  - Through `delAddSoft`, it underlies `EntityLanguage.timeSplit_ent`, then `NetworkLanguage.timeSplit_net`, which is in the safety cone.
  - `delAddSoft` itself is true; only its route through this lemma is unsound.
- **Suggested fix:** Add the missing hypothesis `evalExpFunTime e = Some t ->`. The corrected lemma was proved in full in the cloud session, and `delAddSoft`'s existing call (`eapply ...; eassumption`) should go through unchanged.

