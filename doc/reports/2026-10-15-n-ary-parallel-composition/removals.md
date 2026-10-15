[← Report](README.md)

# Removed lemmas and tactics

Every lemma or tactic removed, with the n-ary result or the tactic that does its job now. The n-ary results are in `src/lang/SoftwareLanguage.v` unless said otherwise; the tactics are in `src/protocol/ProtAuxResults.v`.

## `src/lang/SoftwareLanguage.v`

| Removed | Replaced by |
|---|---|
| `del_triple_sort` | `parAll_del_sort_not`: no two components offer complementary actions while the whole delays, for any two positions. |
| `parTriple_disc_intro1`, `_intro2`, `_intro3` | `parAll_disc_intro`: a `stepAt` of one component is a step of the whole. |
| `parTriple_dae_intro1`, `_intro2`, `_intro3` | `parAll_dae_intro`, for any component in the list; in the protocol, `dae_broadcast`, `dae_overlap` and `dae_listener`. |
| `parTriple_disc_inv` | `parAll_disc_inv`; in the protocol, `triple_disc_inv`. |
| `parTriple_del_inv` | `parAll_del_inv`; in the protocol, `triple_del_inv`. |
| `par_del_sync_not` | `parAll_del_sync_not` with the list `[q]`. |
| `parTriple_del_sync_not_12`, `_13`, `_23` | `parAll_del_sync_not`; in the protocol, `triple_del_sync_not`. |
| `link_par_triple_discEx`, `link_par_triple_delEx` | `parAll_disc_weak` and `parAll_del_inv`, whose `Forall2` fixes the shape of the derivative; in the protocol, `triple_shape` under the `link_partripdiscex_tac` and `link_partripdelex_tac` families. |
| `link_par_triple_out`, `link_par_triple_in` | `parAll_disc_nonTau`: a step on an action other than tau is a step of exactly one component; in the protocol, `link_partripout_tac` and `link_partripin_tac`. |
| `link_par_triple_del` | `parAll_del_inv`; in the protocol, `link_partripdel_tac`. |
| `link_par_triple_discW_1`, `_2`, `_3` | `parAll_disc_weak`: a step changes each component by at most one step; in the protocol, `link_partripdiscW1_tac`, `_W2_tac`, `_W3_tac`. |
| `link_par_triple_out_neq1`, `_neq2`, `_neq3`, `link_par_triple_in_neq1`, `_neq2`, `_neq3` | `parAll_disc_nonTau`; in the protocol, `link_partripneq_out_tac` and `link_partripneq_in_tac`. |
| `par_triple_inv_cases`, `par_triple_close` (tactics) | Nothing: they only proved the removed lemmas. |

## `src/lang/ProcEquiv.v`

| Removed | Replaced by |
|---|---|
| `par_bisim_triple` | `parAll_bisim_context`: bisimilarity is a congruence for the composition of any number of processes. |

## `src/lang/EntityLanguage.v`

| Removed | Replaced by |
|---|---|
| `del_triple_sort_tac` (tactic) | Nothing: it was unused, and rested on `del_triple_sort`. |

## `src/lang/NetworkLanguage.v`

| Restated | Now |
|---|---|
| `net_del_elim` | Over an entity `[|p, l, h, k|]` with no process structure: the entity at index `i` delays with each component, and moves at most `speedMax * d`. The process delay splits with `parAll_del_inv` where a proof needs the components. |

## `src/protocol/ProtAuxResults.v`

No lemma is removed. `link_reach_triple_tau` keeps its statement and is now proved by `triple_disc_inv`. The `link_partrip*` tactics keep their names and the hypotheses they produce.
