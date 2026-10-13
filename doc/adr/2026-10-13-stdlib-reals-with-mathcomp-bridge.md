# ADR: Rocq stdlib reals, with mathcomp's `Rstruct` bridge as escape hatch

| | |
|---|---|
| **Status** | Accepted |
| **Date** | 2026-10-13 |
| **Deciders** | Project owner (Colm Bhandal), agreed with the lead agent |
| **Workstream** | [Rocq upgrade & proof completion](../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md), Phase 1 step 3 |

## Context

- The model is built on the stdlib's real numbers. `Time`, `Distance` (over `nonnegreal`) and `Delay` (over `posreal`) are records with coercions to `R` (`src/ComhBasics.v`). `Position` is a pair of `R` (`src/StandardResults.v`).
- The reals are everywhere. **About 880 lines in 18 of the 25 `src/*.v` files** use stdlib reals directly: `Rle`/`Rlt`/`Rplus`/`Rmult`/`Rmax`/`Rmin`, `nonnegreal`/`posreal`/`mkposreal`, `R` in signatures, `%R`, and so on. **About 370 of those lines** are hand-rolled inequality lemmas and tactics in `src/RInequalities.v` (186) and `src/StandardResults.v` (181). The other ~510 lines are in the protocol and safety files (`NARTop.v` 116, `ComhBasics.v` 74, `NARIncomp.v` 73, `SoftwareLanguage.v` 66, `Main.v` 45, …). Counts were taken with grep on 2026-10-13.
- The code uses no `omega`/`fourier`/`lra`/`nra`/`Psatz`. Arithmetic on reals is done by chaining small lemmas by hand.
- Rocq 9.x moves the stdlib into the separate `rocq-stdlib` package (`From Stdlib Require Import …`). `lra`/`nra`/`Psatz` remain the standard real-arithmetic automation.
- The proof fan-out (Phase 3) needs a stable base it can start on right away. Every real-touching line we rework before the fan-out delays it.

## Options considered

| | Option | Pros | Cons |
|---|---|---|---|
| **a** | Stay on Rocq stdlib `Reals` + `lra`/`nra`/`Psatz` | No migration. Lean build: only `rocq-stdlib`. Automation already covers most of the hand-rolled inequality chains. | The stdlib's real-analysis library is thinner and less uniform than mathcomp's. Some lemmas may be missing. |
| **b** | Switch to mathcomp-analysis reals natively (`realType`) | Rich, uniform algebra/order hierarchy. Strong lemma library. | Swapping the number type is cheap, but mathcomp comparisons are **boolean** (`<=` : `bool` in `ssrnum`), and lemma names and rewrite idioms (`ssreflect`) differ. **All ~880 real-touching lines need rework before the fan-out can start.** The subtype records (`Time`/`Delay`/`Distance`) would also need re-basing. Heavier deps in the build and CI. |
| **c** | Stay on stdlib `R`; borrow from mathcomp through `Rstruct` when needed | Keeps (a)'s zero-migration start. `Rstruct` gives stdlib's `R` mathcomp's `realType` structure, so any missing lemma can be taken from mathcomp/analysis with `RleP`/`RltP`/`RealsE` conversions, locally, in the proof that needs it. | The bridge adds conversion boilerplate where it is used. If it is ever used, we pay for the mathcomp dependency (see Consequences). |

## Decision

**Option (c).**

- The stdlib's `Reals` stays the primary representation. Real arithmetic uses `lra`/`nra`/`Psatz`. Hand-rolled inequality lemmas are replaced by these where that makes the proof simpler (Phase 1 step 3). We don't rewrite them wholesale.
- mathcomp's `Rstruct` bridge is the **escape hatch** for a real-analysis fact the stdlib lacks.
- The mathcomp dependency is **added lazily**: only when a proof first needs the bridge. Until then, the build and CI depend on `rocq-stdlib` alone.

## Consequences

- ✅ The fan-out can start as soon as the Rocq 9.2.0 build is green. No representation migration is needed first.
- ✅ The build and CI stay lean: the official `rocq/rocq-prover:9.2.0` image plus `rocq-stdlib`.
- ⚠️ **Cost of adding the bridge later.** `Rstruct.v` now lives in mathcomp-analysis's `reals_stdlib/` directory, in the opam package `rocq-mathcomp-reals-stdlib`. That package depends on `rocq-stdlib` and `rocq-mathcomp-reals`, which pull in mathcomp-classical, mathcomp core (algebra) and Hierarchy Builder. It does **not** need the full `rocq-mathcomp-analysis`. Expect several extra minutes on a cold CI build unless the image is cached.
- 🐳 **Prebuilt images (checked on Docker Hub, 2026-10-13):**
  - `mathcomp/mathcomp:2.6.0-rocq-prover-9.2` (also `latest-rocq-prover-9.2`) is official and has mathcomp core on Rocq 9.2. It is a good base if the bridge is ever needed: install `rocq-mathcomp-reals-stdlib` on top of it.
  - There is **no official mathcomp-analysis image**. The only one found is the community image `yoshihiro503/mathcomp-analysis`, which tops out at `1.18.0-rocq-9.0` (Rocq 9.0, not 9.2), so it doesn't fit our toolchain pin.
  - `rocq/rocq-prover:9.2.0` exists (also `9.2.0-native`, `-flambda` variants).
- ⚠️ **Network constraint.** opam.ocaml.org is **not reachable** from the current agent build environment, but Docker Hub and the Nix binary cache are. In that environment, adding mathcomp means building from a Docker image or Nix rather than `opam install`. GitHub Actions has normal opam access.
- 🔁 **Revisit if** the bridge ends up being used in many proofs, or option (b)'s benefits (e.g. heavy real analysis in new lemmas) clearly outweigh the migration cost. That would be a new ADR superseding this one.
