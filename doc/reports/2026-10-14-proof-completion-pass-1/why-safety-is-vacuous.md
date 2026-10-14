# Why `safety` proves nothing yet

[← Proof completion, pass 1](README.md)

`safety` in `src/Main.v` ends in `Qed`, but `Print Assumptions safety` still lists admitted lemmas. If any of those can be refuted, then `False` follows from what `safety` rests on, and the theorem says nothing. Two independent problems make that true today, and either one is enough on its own.

## 1. Inconsistent admitted lemmas in the cone

Every lemma below is used by `safety`, directly or indirectly. For each one, an auditor compiled a Rocq refutation that uses only the `ComhBasics` model axioms and the stdlib. Most of the refutations also need an inhabitant of `Mode`, which any real model has. So admitting any one of these lemmas lets you prove `False`.

| Lemma | What goes wrong | Proposed fix |
|---|---|---|
| [`ProtAuxResults.reachableProt_triple`](lemmas/ProtAuxResults.md#reachableprot_triple) | It says every reachable protocol process is a triple of component states. But `overlapState` and `listenerState` are marked INCOMPLETE and miss some states. A single `chanBad?` step from the start reaches `sleeping \|\| tfsStartN \|\| listening`, and `overlapState` doesn't cover `tfsStartN`. | Define each component predicate as "reachable from that component's initial process". Proved to work (`reachableProt_triple_fix`). |
| [`ProtAuxResults.listening_AN_prot`](lemmas/ProtAuxResults.md#listening_an_prot) | The listener inputs `chanAN⟨r, m''⟩`, 2 fields, but notifications are `⟨r, m, l⟩`, 3 fields. The lemma already fails for an empty input. | Make the listener input 3 fields, matching the interface. |
| [`ProtAuxResults.ovWait_del_pres`](lemmas/ProtAuxResults.md#ovwait_del_pres) | It says a delay leaves the `ovWait` timers unchanged, but they count down. | Conclude `exists x' y', ovWaitState m t x' y' p'`, which is proved and is all the caller needs. |
| [`NetAuxBasics.bcWaitNet_del_bkwd`](lemmas/NetAuxBasics.md#bcwaitnet_del_bkwd) | An unreachable entity whose broadcast slot is `del 1 (bcWait m 0)` refutes it. | Add `reachableNet n` and `zeroTime < x`. The caller has both in scope. |
| [`NetAuxBasics.nextSince_del_ovWait`](lemmas/NetAuxBasics.md#nextsince_del_ovwait) | Refuted the same way, by an unreachable entity. It also stays false for reachable networks, because position reads aren't urgent ([root cause 6](root-causes-and-fixes.md#6-nosyncnow-is-missing-the-thesiss-position-read-clause)). | Add `reachableNet n` **and** restore the position-read clause in `noSyncNow`. |
| [`NARMisc.notifBadPathNet_urgent`](lemmas/NARMisc.md#notifbadpathnet_urgent) | Refuted by an unreachable `badOvlp` entity. | Add `reachableNet n`. The caller has it, and the fixed proof compiles. |
| [`NARMisc.outgoing_timeout_disc`](lemmas/NARMisc.md#outgoing_timeout_disc) | It quantifies the message position universally where it should be existential. The counterexample is a genuinely reachable network. | Move the position into the existential. Fully proved. |
| [`EntAuxResults.link_ent_outList`](lemmas/EntAuxResults.md#link_ent_outlist) | The input case uses the wrong step relation: `-tl-`, which has no rules, where `-ol-` was meant. | Use `-ol-`. The fixed statement is proved. |

## 2. A pair that makes `safety` trivial

[`NetAuxBasics.tfsListen_failSafe_net`](lemmas/NetAuxBasics.md#tfslisten_failsafe_net) and the conjecture [`NetAuxBasics.currMode_intro`](lemmas/NetAuxBasics.md#currmode_intro) are both in the cone. Together they imply that **every** mode is fail-safe. `minDistComp` is 0 for fail-safe modes, so `safe n` then holds for every network, reachable or not. The auditor compiled exactly this implication: from the two statements to `forall n, safe n`.

Neither statement can be refuted from the axioms alone, because nothing in the axioms requires a mode that isn't fail-safe. But `tfsListen_failSafe_net` is false in any model with even one non-fail-safe mode. The fix is to define the `currModeNet` stub ([stubs](root-causes-and-fixes.md#parameter-stubs)), then add `reachableNet n` to the lemma and to its caller chain, where it is already in scope.

## What this does and doesn't mean

- **It doesn't mean the protocol is unsafe.** The defects are in the formalisation: statements, definitions and stubs. The one exception is the listener arity, which is in the thesis as well.
- **It does mean the formal proof establishes nothing until these are fixed.**
- **None of the 123 new proofs rest on the section 1 lemmas.** The harness rejected any proof whose assumptions included one of them, and that is why [25 proofs are held back](results.md#held-back-proofs). Proofs that were already `Qed` before this pass can still rest on them, `safety` included.
- **The fixes are mostly mechanical once you approve them.** Many of the dependent proofs already exist in conditional form, so pass 2 should be quick.

## Checking it yourself

Each refutation is a standalone file under [`evidence/audit/`](evidence/README.md). From the repository root, after `make`, compile one, for example:

```
rocq compile -R src ComhCoq doc/reports/2026-10-14-proof-completion-pass-1/evidence/audit/rest/A_PAR_reachableProt_triple.v
```

Its `Print Assumptions` output lists only `ComhBasics` model axioms, stdlib axioms, and the refuted lemma itself.

| Lemma | Evidence file |
|---|---|
| `reachableProt_triple` | `evidence/audit/rest/A_PAR_reachableProt_triple.v` |
| `listening_AN_prot` | `evidence/audit/rest/A_PAR_listening_AN_prot.v` |
| `ovWait_del_pres` | `evidence/audit/rest/A_PAR_ovWait_del_pres.v` |
| `bcWaitNet_del_bkwd` | `evidence/audit/net/a_bcWaitNet_del_bkwd.v` |
| `nextSince_del_ovWait` | `evidence/audit/net/a_nextSince_del_ovWait.v` |
| `notifBadPathNet_urgent` | `evidence/audit/rest/A_NM_notifBadPathNet_urgent.v` |
| `outgoing_timeout_disc` | `evidence/audit/rest/A_NM_outgoing_timeout_disc.v` |
| `link_ent_outList` | `evidence/audit/ent/A_link_ent_outList.v` |
| `tfsListen_failSafe_net` + `currMode_intro` | `evidence/audit/net/a_tfsListen_safety.v` |
