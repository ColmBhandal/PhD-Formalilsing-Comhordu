# Unproved lemmas in `NetAuxBasics`

[← Lemma index](README.md) · [Proof completion, pass 1](../README.md)

33 lemmas here could not be proved as stated, 11 of them in `safety`'s assumption cone.

The **Audit** line is the independently checked verdict. The text below it is the prover's own write-up.

## `switch_states_mState`

- **Where:** `src/NetAuxBasics.v` line 201 · **Lemma** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** FALSE-IN-INTENDED-MODEL · root cause: `stub; missing-reachability; mode-chan-internal-sync`
- **Fix (audit summary):** Define the currModeNet/nextModeNet stubs and add `reachableNet n ->` (call site NARMisc.currSince_curr has p; `try assumption` closes it). Fixed version only argued.

- **Status:** BLOCKED-ON-STUB (`currModeNet`, `nextModeNet`). It also NEEDS-HYPOTHESIS `reachableNet n`: even with the intended stub definitions the statement is false without it. The counterexample is checked in Rocq.
- **Intent:** if entity `i` moves its overlap component from `switchCurr` to `switchListen` in one discrete network step, and its next mode was `m`, then its current mode afterwards is `m`. The step is the `chanMCurr` write that makes the mode state finalise the switch (thesis Def. 6.11, base case of `currSince`).

### Failure

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

### Ripple-up

- The target is in the safety cone.
- Its only user is `NARMisc.currSince_curr` (NARMisc.v:260, base case). That result is used in NARIncomp.v:402 and NARInsuff.v:483 and 593.
- `currSince_curr` already has `p : reachableNet n` in scope, so the fix costs nothing upstream.

### Suggested fix

1. Define the stubs as above. For `nextModeNet`, the EntAuxDefs `Parameter nextModeEnt` shadows `EntityLanguage.nextModeEnt : Entity -> option Mode`, so write the definition through `nextModeMState (mstEnt e)`.
2. Add reachability to the statement, matching the neighbouring `mState_switch_states`:
   ```coq
   Lemma switch_states_mState : forall (n n' : Network) (i : nat) (a : ActDiscNet)
     (m : Mode), reachableNet n -> n -NA- a -NA> n' -> switchCurrStateNet i n ->
     switchListenStateNet i n' -> nextModeNet m i n -> currModeNet m i n'.
   ```
   The call site `eapply switch_states_mState; try apply w; try assumption.` in `currSince_curr` still works unchanged, because `try assumption` closes `reachableNet n` with `p`.

### Proof plan for the fixed statement under the intended definitions

1. Destruct the hypotheses into `e = [|p,l,h,k|] @ i .: n` (switchCurr overlap, `nextModeMState k = Some m`, by `entInNetUnique`) and `e' = [|p',l',h',k'|] @ i .: n'` (switchListen overlap).
2. Apply `link_net_ent_disc_fwd`. Either `e = e'`, or `e -EA- b ->> e'`.
   - In the `e = e'` case, and in every entity rule that keeps `p`, the overlap would be bisimilar to both `switchCurr` and `switchListen`. That is impossible: `switchCurr` enables `chanMCurr *!` (`switchCurr_mCurr_out`) and `switchListen` does not.
3. `reachableProt p` (`link_net_prot_reach`) makes slots 1 and 3 broadcast and listener states. Neither can input `chanMCurr []` (the listener reads `chanMCurr ;? [m]`, which has a different arity). So the overlap changed by its own output `chanMCurr *!`.
4. The only entity rule that consumes `chanMCurr *!` is `stepDeCurrWrite`, giving `k -ms- chanMCurr @? -ms> k'`.
5. Invert with `stepMsSwitch`: `k = <|m0,m',0|>` and `k' = m'`. With `nextModeMState k = Some m` this gives `m' = m`, so `currModeEnt e' = m`.

Missing auxiliary facts:
- a process lemma "switchCurr-overlap triple steps to switchListen-overlap ⇒ action is `chanMCurr *!`, or a tau sync with slot 1 or 3 on `chanMCurr []`";
- "reachable broadcast and listener states are not enabled on `chanMCurr *?`".

### Partial proof

Not applicable: the target's conclusion is the opaque stub. The validation script is in the `.cex.v` file next to this note.

## `rangeBad_next_net`

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

## `tfsListen_failSafe_net`

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

## `bcWaitNet_del_bkwd`

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

## `nextSince_del_ovWait`

- **Where:** `src/NetAuxBasics.v` line 424 · **Lemma** · 2015 label: `3` · **in safety cone:** yes
- **Audit:** INCONSISTENT · root cause: `missing-reachability; noSyncNow-missing-pos-clause` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Needs a semantics change (make chanPos reads urgent, e.g. extra clause in noSyncNow / stepTeDel premise; owner approval) AND `reachableNet n ->` (in scope at NARTop.nextSince_periodic_sent).

- **Status:** FALSE (counterexample, machine-checked in Rocq; uses no admitted lemma)
- **Intent:** if entity `i` is in a `nextSince` overlap state (ovWait / ovReady / switchBc / switchCurr) and the network can delay by `d`, then the overlap component is `ovWait m t X Y` with both timers `X, Y >= d` (written `x +dt+ d`, `y +dt+ d`). In words: the only nextSince state that can idle is ovWait, and it can idle at most as long as its timers.

### Failure

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

### Ripple-up
* Used once: `NARTop.v:196` in `nextSince_periodic_sent` (in the safety cone), in the delay
  case of an induction on `nextSince`. There `reachableNet n` is available (`p`). The user
  needs only `0 < y + d` (to call `ovWait_sent`) and `m0 = m`.
* With the lemma false, `nextSince_periodic_sent`'s delay case has no justification: the
  position timer may sit at 0 while time passes, so "a message was sent within the last
  period" can fail. This is a genuine modelling gap, not just a missing hypothesis.

### Suggested fix
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

### Partial proof
None of the target. The counterexample script is the HELPERS section of
`NetAuxBasics.nextSince_del_ovWait.v` (compiles in `--explore`; the target itself is left `Admitted`).

## `currMode_pres_bkwd`

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

## `currMode_intro`

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

## `reachable_net_ent`

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

## `currModeNet_del_pres`

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

## `inPos_ent_net`

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

## `currMode_ent_ex`

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

## `tfsCurrStateNet_bktrk_net`

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

## `tfsCurrState_del_pres_net`

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
  Callers change to `addHyp (tfsCurrState_del_pres_net n n' d i p w)`. Alternatively, split it into an unconditional forward lemma and a reachable-only backward lemma. With reachability, the backward direction follows from `EntAuxResults.del_ovlp`: a reachable entity that can delay is dormant, tfsCurr or ovWait. It then remains to rule out dormant/ovWait delaying to something bisimilar to `tfsCurr`. That depends on `reachable_net_ent`/`reachableEnt` (stub), so the fixed version is BLOCKED-ON-STUB (`reachableEnt`) until the stub is defined.
- **Partial proof:** The file contains the full counterexample and reusable helpers:
  - `_acts`: `tfsCurr`'s discrete actions.
  - `_tdel`: `tfsCurr` delays only to itself.
  - `_derP`, `_actsP`, `_nosyncC`.

## `mState_switch_states`

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

## `tfsState_del_pres_net`

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

## `init_nextMode_net`

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

## `ovReady_prev_net_strong`

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

## `ovWait_prev_net_strong`

- **Where:** `src/NetAuxBasics.v` line 457 · **Lemma** · 2015 label: `#lift-track-net #strong` · **in safety cone:** no
- **Audit:** INCONSISTENT · root cause: `missing-reachability` · **inconsistent (held out of proofs)**
- **Fix (audit summary):** Add `reachableNet n ->` (argued; same proof route as ovWait_prev_net).

- **Status:** FALSE (counterexample, checked in Rocq). NEEDS-HYPOTHESIS `reachableNet n`.
- **Intent:** backward tracking for the overlap state `ovWait(m,t,x,y)` of entity `i`. If entity `i` is in `ovWait(m,t,x,y)` after a discrete network step, then before the step it was already in `ovWait(m,t,x,y)`, or in some `ovReady(m,t0,l0)`, or in `init(m)`. (Thesis: the overlap automaton is entered only from `init` and from `ovReady`.)

### Failure

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

### Ripple-up

- The target is not in the safety cone.
- Its only textual uses are inside commented-out proofs:
  - `NetAuxBasics.ovWait_ovReady_nextMode_net` (NetAuxBasics.v:502). Its proof body is commented out and it ends `Admitted`.
  - `NARTop.ovWait_sent` (NARTop.v:127, also commented out).
- Both callers have reachability in scope. In each, the inductive `reachNetDisc` case has `reachableNet n` for the predecessor network.
- The same counterexample, with slot 2 = `chanMCurr ! ovReady m t l`, refutes the sibling `NetAuxBasics.ovReady_prev_net_strong` (line 451). It also refutes `ovWait_prev_net` (line 1072), which has the same shape and also lacks reachability.
- `ovReady_prev_net` (line 1018) has been accepted as a one-line consequence of `ovReady_prev_net_strong`, so it inherits that lemma's falsity. Its statement also lacks `reachableNet n`. Flagging this for the lead.

### Suggested fix

```coq
Lemma ovWait_prev_net_strong m t x y n n' i a :
  reachableNet n ->
  ovWaitStateNet m t x y i n' -> n -NA- a -NA> n' ->
  ovWaitStateNet m t x y i n \/
  (exists t0 l0, ovReadyStateNet m t0 l0 i n) \/
  initStateNet m i n.
```
(Make the same change to `ovReady_prev_net_strong`, `ovReady_prev_net` and `ovWait_prev_net`.)

### Why the fixed statement should be provable

1. `link_net_ent_disc_bkwd` gives an entity `e = [|p,l,h,k|]` at `i` in `n`, with either `e = e'` or `e -EA- b ->> e'`.
2. Reachability, through `reachable_net_prot` and `reachableProt_triple`, makes `p` a `protocolState` triple `p1 $||$ q $||$ p3`. Here `overlapState q`, and `p1` and `p3` are broadcast and listener states.
3. Invert the entity step and then the `parComp` step:
   - If `q` is unchanged, we get the first disjunct.
   - If `q -PA- a -PA> q'` (alone or as half of a sync), the process-level `ProtAuxResults.ovWait_prev` (Qed) gives `ovReadyState m (t + period m) l q` (second disjunct) or its init branch.

Caveat for whoever proves the fixed version: `ovWait_prev`'s init branch is stated as `initStateProt m p` (= `liftOverlap (initState m) p`) about the *overlap component* `p`. It should almost certainly say `initState m p`. As stated, that branch would need `q` itself to be a triple, so the third disjunct cannot be produced from it directly. It may be vacuous, since the lemma is Qed via `backtrack_weed`, but check this before relying on it.

### Partial proof

None. The counterexample settles the target as stated.

## `nextMode_pres_fwd_net`

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

## `ovWait_del_pres_bkwd_net_strong`

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
  - The remaining cases need a "timer shift" lemma, `ovWait m0 t0 a b ~ ovWait m t a' b' -> ovWait m0 t0 (a+d) (b+d) ~ ovWait m t (a'+d) (b'+d)`. Use bisimulation up to the delay prefix. Note that `t` is *not* recoverable from bisimilarity in general: `eSubtract t (period m)` is ill-defined below 0 and idles. So stick to shift-invariance rather than injectivity.
- **Partial proof:** none for the target. The verified counterexample and its reusable helpers (`del e Y ~ Y` for a zero guard, and no discrete action under a positive guard in the middle component) are in `NetAuxBasics.ovWait_del_pres_bkwd_net_strong.v`.

## `ovReady_del_pres_bkwd_net`

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

## `nextModeNet_del_pres`

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

## `currMode_pres_fwd`

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

## `transGuard_disc_pres`

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

## `transGuard_del`

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

## `nextMode_ent_ex`

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

## `tfsNext_currModeNet_eq`

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

## `tfsStart_prev_net`

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

## `ovWait_del_pres_net`

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

## `del_pres_bkwd_tfsStart`

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

## `ovReady_wait_track_net`

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

## `ovWait_track_net`

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

## `ovWait_prev_net`

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
