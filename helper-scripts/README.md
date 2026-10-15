# Helper scripts

None of these is part of the proof: the Rocq development in [`src/`](../src) builds and checks without them, and nothing they print changes what is proved.

| Script | What it does | Run it with | Also used by |
|---|---|---|---|
| [`summarise_assumptions.py`](summarise_assumptions.py) | Prints, as Markdown, everything the top-level `safety` theorem still rests on, grouped into model axioms, `Parameter` stubs, unproved project lemmas and stdlib axioms. It also counts every `Admitted` and `Conjecture` in `src/`, used by `safety` or not. | `make assumptions`, after `make` | CI, which writes its output to the job summary |
| [`print_statements.py`](print_statements.py) | Prints the statement of every result and the body of every definition in `src/`, module by module, so that two builds can be compared with `diff`: a refactoring that moves or re-proves results should leave this output unchanged except for the moves. | `python3 helper-scripts/print_statements.py > statements.txt`, after `make` | Refactoring PRs, to show that no statement changed |

Run scripts from the repository root, with the same Rocq toolchain as the build (see the [main README](../README.md)).
