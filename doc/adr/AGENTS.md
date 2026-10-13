# doc/adr/: rules for architecture decision records

- Name files `YYYY-MM-DD-{kebab-title}.md`, where the date is the creation date.
- Use these sections: **Status**, **Context**, **Options considered**, **Decision**, **Consequences**.
- Status is one of `Proposed`, `Accepted`, `Superseded by <link>`.
- Don't edit an ADR once it is `Accepted`. To change a decision, write a new ADR that links to the old one, then change only the old ADR's Status line, to `Superseded by <link to new ADR>`.
