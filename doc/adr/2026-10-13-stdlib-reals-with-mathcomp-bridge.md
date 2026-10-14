# Keep the Rocq stdlib reals, with mathcomp's `Rstruct` bridge as an escape hatch

Date: 2026-10-13
Status: 2026-10-13 accepted

## Context

The whole model is built on the standard library's real numbers. Time, distance, delay and position are all stdlib reals or thin wrappers around them, and roughly 880 lines across 18 of the 25 source files use them directly. Much of that is hand-rolled inequality reasoning that arithmetic automation could now do.

Moving to Rocq 9 raised the question of switching to mathcomp-analysis, whose reals come with a richer and more uniform library. Work on proving the outstanding lemmas was about to start at scale and needed a stable base, so any change of representation had to justify the delay it would cause.

## Decision

Keep the stdlib reals as the project's representation, and use the stdlib's `lra` and `nra` tactics for real arithmetic. If a proof ever needs a real-analysis fact the stdlib lacks, borrow it from mathcomp through the `Rstruct` bridge, locally in that proof, and only then add the mathcomp dependency.

## Consequences

- Proving could start as soon as the Rocq 9.2 build was green, with no migration first.
- The build and CI depend only on the Rocq image and its standard library.
- Hand-rolled inequality proofs can be replaced by `lra` and `nra` one at a time, wherever that makes a proof simpler.
- The first proof to use the bridge brings in a sizeable mathcomp dependency and slows cold CI builds.

## Revisit when

The bridge ends up in many proofs, or new work needs heavy real analysis that mathcomp would make much easier.

## Alternatives considered

### Stay on the stdlib reals with no escape hatch

This needs no migration and keeps the build lean, and `lra` and `nra` already cover most of the hand-written inequality chains. Its weakness is the stdlib's thinner real-analysis library, where a missing lemma would have to be proved from scratch. The chosen option keeps all of these strengths and removes that weakness, at no cost until the bridge is first used.

### Switch to mathcomp-analysis reals

Mathcomp's reals sit in a rich, uniform algebraic hierarchy with a strong lemma library. Swapping the number type itself is cheap, but mathcomp's comparisons are boolean rather than propositional, and its lemma names and rewriting style differ. All of the real-touching code, including the time, distance and delay wrappers, would need reworking before proving could start, and mathcomp would become a permanent build dependency. That benefit didn't justify blocking the proving work on a rewrite.

## Implementation notes

- **Where the reals live.** `Time`, `Distance` (over `nonnegreal`) and `Delay` (over `posreal`) are records with coercions to `R`, in `src/ComhBasics.v`. `Position` is a pair of `R`, in `src/StandardResults.v`.
- **Counts,** taken with grep on 2026-10-13. About 880 lines in 18 of the 25 `src/*.v` files use stdlib reals directly: `Rle`, `Rlt`, `Rplus`, `Rmult`, `Rmax`, `Rmin`, `nonnegreal`, `posreal`, `mkposreal`, `R` in signatures, `%R` and so on. About 370 of those lines are hand-rolled inequality lemmas and tactics in `src/RInequalities.v` (186) and `src/StandardResults.v` (181). The rest are in the protocol and safety files: `NARTop.v` 116, `ComhBasics.v` 74, `NARIncomp.v` 73, `SoftwareLanguage.v` 66, `Main.v` 45 and others. The code used none of `omega`, `fourier`, `lra`, `nra` or `Psatz`.
- **Rocq 9.** The stdlib is now the separate `rocq-stdlib` package, imported with `From Stdlib Require Import …`. `lra`, `nra` and `Psatz` remain the standard real-arithmetic automation.
- **Using the bridge.** `Rstruct` gives the stdlib's `R` mathcomp's `realType` structure, and facts cross over with the `RleP`, `RltP` and `RealsE` conversions.
- **Cost of adding the bridge.** `Rstruct.v` now lives in mathcomp-analysis's `reals_stdlib/` directory, in the opam package `rocq-mathcomp-reals-stdlib`. That package depends on `rocq-stdlib` and `rocq-mathcomp-reals`, which pull in mathcomp-classical, mathcomp core and Hierarchy Builder, but not the full `rocq-mathcomp-analysis`. Expect several extra minutes on a cold CI build unless the image is cached.
- **Prebuilt images,** checked on Docker Hub on 2026-10-13. `mathcomp/mathcomp:2.6.0-rocq-prover-9.2` (also tagged `latest-rocq-prover-9.2`) is official and has mathcomp core on Rocq 9.2, so it is the natural base: install `rocq-mathcomp-reals-stdlib` on top. There is no official mathcomp-analysis image, and the community image `yoshihiro503/mathcomp-analysis` stops at Rocq 9.0. `rocq/rocq-prover:9.2.0` also comes in `-native` and `-flambda` variants.
- **Network.** opam.ocaml.org wasn't reachable from the agent build environment used for this work, though Docker Hub and the Nix binary cache were, so there mathcomp would have to come from a Docker image or Nix. GitHub Actions has normal opam access.
- **Action item.** Replace hand-rolled inequality proofs in `RInequalities.v` and `StandardResults.v` with `lra`/`nra` where that is simpler, with statements unchanged. This is step 3 of the [Rocq upgrade and proof completion workstream](../workstreams/2026-10-13-rocq-upgrade-and-proof-completion.md).
