# helper-scripts/: rules for helper scripts

- This folder holds scripts that aren't essential to building the project, such as reporting, checking and maintenance tools. A script the build does need belongs in `scripts/` instead.
- `make`, which builds and checks the proof, must never depend on anything here. Optional targets such as `make assumptions`, and CI reporting steps, may call these scripts.
- Scripts read the sources and build products. They never edit `src/`.
- Each script must run from the repository root, inside the reference environment (the `rocq/rocq-prover:9.2.0` image, see the top-level `AGENTS.md`). Use only Python 3's standard library and the Rocq toolchain, so nothing extra needs installing.
- Start each script with a docstring saying what it does and how to run it.
- When adding, renaming or removing a script, update the table in [`README.md`](README.md). If a `Makefile` target or CI step calls the script, keep those in step too.
