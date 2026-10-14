# AGENTS.md: project-wide rules

## Meta-rule: where rules live

- Rules live in `AGENTS.md` files, each in the directory whose scope it governs.
- Before touching a file, read the `AGENTS.md` in its directory and in every ancestor directory up to the root.
- When two rules conflict, the one in the nearest directory wins.
- Put a new rule in the narrowest directory that covers its whole scope. This file holds only rules that apply everywhere.
- Don't duplicate a rule across `AGENTS.md` files or into other docs. Link to it instead.

## Project

- This is a Rocq formalisation of the Comhordú real-time coordination protocol and its safety proof, based on a [2014 PhD thesis](doc/thesis/2014-10-28-phd-thesis.pdf).
- The top-level theorem is `safety` in `src/Main.v`.
- Layout:
  - `src/`: the Rocq development. Logical path `ComhCoq`. See `src/AGENTS.md`.
  - `doc/`: workstreams, reports, ADRs, archive, and the thesis with its corrections. See `doc/AGENTS.md`.
  - `helper-scripts/`: scripts the build doesn't need, such as reporting tools. See `helper-scripts/AGENTS.md`.
  - `scripts/`: reserved for scripts the build does need. There are none yet.
  - `.github/workflows/`: CI.

## Toolchain and build

- Use Rocq **9.2.0** with `rocq-stdlib`. Dependencies are declared in `rocq-comhordu.opam`. The reference environment is the Docker image `rocq/rocq-prover:9.2.0`, the same one CI uses.
- `make` builds everything (`_CoqProject` → `rocq makefile` → `Makefile.coq`).
- `make assumptions` prints what `safety` still rests on.
- `make clean` removes build products.
- CI (`.github/workflows/build.yml`) builds every pull request (when it's opened, and on each new commit) and reports remaining assumptions. Keep it green: never merge a red build.

## Writing

- Don't tell readers what a document is or how to read it: no "this page is the short version", "the rest is detail" or "this section goes through…". Write it so it flows, and let them experience that for themselves. This applies to all prose: docs, READMEs and PR descriptions.
- Cite the thesis by its printed page number, not the PDF page, and by definition or remark number where there is one. The two page numbers differ; see [`doc/thesis/`](doc/thesis/README.md).

## Scripts

- Name a script for what it does. A script does something, so the verb matters most; usually a noun follows: `summarise_assumptions.py`, not `assumptions.py`.

## Working rules

- Work is planned and tracked in `doc/workstreams/`, decisions are recorded in `doc/adr/`, and results go in `doc/reports/`.
- Changing what the project *claims* needs explicit human approval: theorem or lemma statements, definitions, model axioms, and deleting results. Agents propose such changes in a report; they don't make them.
- Whenever a change makes the formalisation depart from the thesis, record the correction in [`doc/thesis/thesis-corrections.md`](doc/thesis/thesis-corrections.md) in the same PR.
- Never weaken the trust base silently. If a change adds an entry to `make assumptions` output, call it out in the PR and in the relevant report.
