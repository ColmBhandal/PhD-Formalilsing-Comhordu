# Conditional proofs from cloud prover NARTop (not spliced)
- `NARTop.ovWait_sent`: proved in the cloud session by reviving the 2015 proof, repaired for bisimulation-based state predicates. It uses `ovWait_prev_net_strong`, which is inconsistent (implies Mode -> False), so it can't be accepted until that lemma gets a `reachableNet n` hypothesis.
- `NARTop.currSince_del_bcWait`: proved relative to `currSince_bc_state` (false), `bcWaitNet_del_bkwd`, `bcReady_urgent` and `reachable_net_ent`. The harness rejected it because it transitively depends on `reachableProt_triple`.
