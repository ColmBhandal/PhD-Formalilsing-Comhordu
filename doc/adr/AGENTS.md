# doc/adr/: rules for architecture decision records

## When to write one

Write an ADR when a future contributor would need the context to understand why the project is the way it is, not just what it does. That covers adopting a tool or library, changing the toolchain, build or CI, choosing between viable approaches where a real trade-off was made, and setting a cross-cutting pattern that later work should follow. A decision local to one lemma, one file or a routine refactor doesn't need one.

## Human sign-off comes first

Before drafting, interview the human one question at a time, walking the decision tree in dependency order and offering a recommended answer to each question. Answer from the codebase instead of asking wherever that's possible. Don't write the ADR until the human has explicitly signed off on the options, the reasoning and the decision.

## Content and shape

An ADR is a decision record, not a README. It records the options considered, their pros and cons, the choice and why, and it doesn't explain how the resulting code works.

Write it in three tiers, so a reader can stop after any one of them and still come away with a correct, proportionate picture. Detail must never leak upward: if a sentence in tier 1 or 2 needs an exact name, an edge case or an aside to make sense, that content belongs in tier 3.

1. **Tier 1: the decision.** A title, then a date line and a status line (`Status: 2026-10-13 accepted`; the statuses are proposed, accepted and superseded). Then **Context**, **Decision** and **Consequences**, the last as plain bullets of what the decision commits the project to, and optionally **Rationale** and a one- or two-sentence **Revisit when**. Write flowing prose in as few words as read naturally, without parentheticals, asides, emojis or links the reader can't do without.
2. **Tier 2: Alternatives considered.** One subsection per option seriously weighed, with the pros and cons that actually drove the decision. Concise but complete, still flowing rather than fragmented, and sparing with links.
3. **Tier 3: Implementation notes.** Exact names, measurements, edge cases, action items and migration steps. Detail is welcome here, and so are links.

It's easiest to write the tiers in reverse: dump the research into tier 3, draft the options into tier 2, decide, compress the decision into tier 1, then read the whole ADR top to bottom for flow.

## Naming and lifecycle

- Name files `YYYY-MM-DD-{kebab-title}.md`, where the date is the creation date.
- Don't edit an accepted ADR. To change a decision, write a new ADR that links to the old one, then change only the old ADR's status line to superseded, linking to the new one.
