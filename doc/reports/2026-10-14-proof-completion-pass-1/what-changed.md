# What changed in the repository

[← Report summary](README.md)

What this pass actually changed, area by area. **Statements, definitions, model axioms and `Parameter` stubs are unchanged everywhere.** Every change of that kind is a proposal in [root causes and fixes](root-causes-and-fixes.md), waiting for approval.

| Area | Change |
|---|---|
| Toolchain | Rocq 9.2.0 + `rocq-stdlib`. Explicit `From Stdlib` imports, LibTactics compatibility fixes, a `rocq makefile`-based `Makefile`, and `rocq-comhordu.opam`. No proof broke in the upgrade: `Print Assumptions safety` came out identical to the Coq 8.15 baseline. |
| CI | `.github/workflows/build.yml`, on the `rocq/rocq-prover:9.2.0` image. It builds everything and writes the `make assumptions` summary to the job page. |
| Rules | `AGENTS.md` files by directory (top level, `src/`, `doc/**`), plus a `CLAUDE.md` pointer. |
| Docs | The 2015 project plan moved to `doc/archive/` after a relevance check. This report, the [workstream](../../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md) and the [reals ADR](../../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md) are new. |
| Reals | 58 hand-rolled inequality proofs in `RInequalities.v` and `StandardResults.v` replaced by one-line `lra`/`nra` calls. Statements are unchanged, and the trust base is byte-identical. |
| Model axioms | New `src/ModelConsistency.v`, which shows the axioms are consistent ([below](#model-axioms-are-consistent)). |
| Proofs | 123 targets proved: `Admitted`/`Conjecture` replaced by `Qed`, with **statements unchanged**. Helper lemmas are prefixed with their target's name and placed just before it. |

## Model axioms are consistent

`src/ModelConsistency.v` defines three things:

- `ComhModel`, a record with one field per `ComhBasics` axiom.
- `global_model`, which shows the global axioms form an instance of `ComhModel`.
- `concrete_model`, an instance built without any axioms. It has a fail-safe mode `Safe` and a non-fail-safe mode `Moving`, and two `Moving` entities must stay distance 1 apart. So safety is a real constraint in this model, not something every network trivially meets.

`Print Assumptions concrete_model` lists only the stdlib reals' own axioms. So the 28 axioms are jointly satisfiable, by a model that isn't degenerate.

For how the axioms could be packaged as a `Module Type`, see [smaller decisions](root-causes-and-fixes.md#smaller-decisions).

## Reals clean-up notes

- Nothing needed the mathcomp `Rstruct` bridge. The [ADR](../../adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md) keeps it as an escape hatch.
- Candidates for removal, and a naming trap in `Rplus_lt_reg_l`/`_r`, are under [smaller decisions](root-causes-and-fixes.md#smaller-decisions).
