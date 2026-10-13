# doc/: rules for all project documentation

- Put every dated document in one of these subfolders. Don't put documents directly in `doc/`.
  - `workstreams/`: living trackers for ongoing work.
  - `reports/`: point-in-time reports.
  - `adr/`: architecture decision records.
  - `archive/`: superseded historical material.
- Name dated documents `YYYY-MM-DD-{kebab-title}.md`, where the date is the **creation** date in ISO format. Never change the date after creation.
- Follow the `AGENTS.md` in each subfolder for its specific rules.
- Link between documents with relative paths.
