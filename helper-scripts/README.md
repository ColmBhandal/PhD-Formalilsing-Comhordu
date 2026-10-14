# Helper scripts

None of these is part of the proof: the Rocq development in [`src/`](../src) builds and checks without them, and nothing they print changes what is proved.

| Script | What it does | Run it with | Also used by |
|---|---|---|---|
| [`assumptions.py`](assumptions.py) | Prints, as Markdown, everything the top-level `safety` theorem still rests on, grouped into model axioms, `Parameter` stubs, unproved project lemmas and stdlib axioms. It also counts every `Admitted` and `Conjecture` in `src/`, used by `safety` or not. | `make assumptions`, after `make` | CI, which writes its output to the job summary |

Run scripts from the repository root, with the same Rocq toolchain as the build (see the [main README](../README.md)).
