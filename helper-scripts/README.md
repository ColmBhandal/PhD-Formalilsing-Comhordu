# Helper scripts

None of these is part of the proof: the Rocq development in [`src/`](../src) builds and checks without them, and nothing they print changes what is proved.

| Script | What it does | Run it with | Also used by |
|---|---|---|---|
| [`summarise_assumptions.py`](summarise_assumptions.py) | Prints, as Markdown, everything the top-level `safety` theorem still rests on, grouped into model axioms, `Parameter` stubs, unproved project lemmas and stdlib axioms. It also counts every `Admitted` and `Conjecture` in `src/`, used by `safety` or not. | `make assumptions`, after `make` | CI, which writes it to the job summary and diffs it against the base branch on every pull request |
| [`install_rocq.sh`](install_rocq.sh) | Installs Rocq 9.2.0 where there is no Docker daemon and no opam: it downloads the CI image's layers from Docker Hub and unpacks the image's Rocq to `/home/rocq/.opam/4.14.2+flambda`. Does nothing if it's already there. | `helper-scripts/install_rocq.sh`, as root, then `export PATH=/home/rocq/.opam/4.14.2+flambda/bin:$PATH` | Agents in sandboxed sessions, per the top-level `AGENTS.md` |
| [`print_statements.py`](print_statements.py) | Prints the statement of every result and the body of every definition in `src/`, module by module, so that two builds can be compared with `diff`: a refactoring that moves or re-proves results should leave this output unchanged except for the moves. | `python3 helper-scripts/print_statements.py > statements.txt`, after `make` | CI, which diffs it against the base branch on every pull request |

Run scripts from the repository root, with the same Rocq toolchain as the build (see the [main README](../README.md)).
