# doc/reports/: rules for reports

- Name files `YYYY-MM-DD-{kebab-title}.md`, where the date is the creation date.
- Treat each report as a point-in-time snapshot. Don't rewrite an old report; write a new dated report and link back to the old one. Only typo fixes are allowed in old reports.
- For every lemma left unproved, include:
  1. **Intent:** what it was meant to say.
  2. **Failure:** why it fails (false, missing hypothesis, depends on a stub, …).
  3. **Ripple-up:** its impact up the dependency chain towards `safety`.
  4. **Suggested fix:** a concrete change (a statement edit, an added hypothesis, or a definition).
