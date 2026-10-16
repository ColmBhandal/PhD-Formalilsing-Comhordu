# doc/workstreams/: rules for living trackers

- Name files `YYYY-MM-DD-{kebab-title}.md`, where the date is the day the workstream started.
- Mark every step with its owner, **🤖 Agent** or **🧑 Human-in-the-loop**, and give it a status checkbox (`[ ]` / `[x]`).
- Keep the tracker current: tick each step as its work lands, with the date, a sentence or two on the outcome and any decision taken, and the PR link. Don't restate the PR.
- The log records changes to the plan: new or reordered steps, decisions, changes of process. A step's tick already records that it landed, so that doesn't go in the log too.
- End with an open-ended final phase that holds every undecided or deferred item. Move an item out of that phase once it is decided.
- Keep trackers short and easy to scan. Put detailed write-ups in `../reports/` and decisions in `../adr/`, and link to them.
