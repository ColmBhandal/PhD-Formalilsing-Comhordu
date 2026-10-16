# doc/reports/: rules for reports

## When to write one

- Only when a human explicitly asks for a detailed report. A PR is never a reason for one: its description is the record, the workstream links to it, and CI attaches the statements and assumptions diffs. See the working rules in the top-level [`AGENTS.md`](../../AGENTS.md).

## One folder per report

- Each report is a folder named `YYYY-MM-DD-{kebab-title}/`, where the date is the creation date.
- The folder's `README.md` is the entry point: a human-readable summary of the whole report.
  - Write it with empathy for the reader, and treat their time as valuable. Lead with what the reader most needs to know and any decisions needed from a human. It should take minutes, not an hour, to read.
  - Link to the detailed documents instead of repeating them. A "where to go next" table that says when each one is worth reading works well.
- Put the detail in further documents inside the folder, linked from the README or from each other.
  - These must be human-readable too. The deeper a document sits in the detail, the more verbose it can be: the README is the shortest, and per-item write-ups are the longest.
  - Start each one with a link back to the README.
- Put machine-checkable material (Rocq files, logs, JSON) in an `evidence/` subfolder. Give it its own `README.md` that says what each part is and how to re-run it.

## Content

- Don't address the reader as "you". Name who is meant instead: "needs human approval", "decisions needed from a human".
- Treat each report as a point-in-time snapshot. Don't rewrite an old report; write a new dated report and link back to the old one. Only typo fixes are allowed in old reports.
- For every lemma left unproved, include the items below. They can live in a detail document instead of the README.
  1. **Intent:** what it was meant to say.
  2. **Failure:** why it fails (false, missing hypothesis, depends on a stub, …).
  3. **Ripple-up:** its impact up the dependency chain towards `safety`.
  4. **Suggested fix:** a concrete change (a statement edit, an added hypothesis, or a definition).
