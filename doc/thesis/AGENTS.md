# doc/thesis/: rules for the thesis, its corrections and the remarks on it

- Never edit the thesis. It is a submitted document and can't be changed.
- Make every edit in [`thesis-corrections.md`](thesis-corrections.md) instead.
- Give each correction the printed page and the definition or remark number, what the thesis says, the correction, why, and a link to the PR or report that found it.
- [`thesis-remarks.md`](thesis-remarks.md) holds notable observations about the thesis itself, made while formalising it, that are not departures from it. Add one only when a human has agreed to it, proposed in the PR; most discoveries don't qualify. Write it to last: it is about the thesis, never about the state of the formalisation, so nothing like "yet", "today" or "planned", and no reference to a file or lemma. Give the same references as a correction, the observation at a high level, a minimal example only where one helps, why it matters, and the PR or report that made it.
- Write maths in GitHub's LaTeX syntax: `$...$` inline and `$$...$$` for display.
- Don't use LaTeX spacing commands made of a backslash and punctuation, such as `\;`, `\,`, `\:`, `\!` or `\ `. Some Markdown viewers read them as escaped punctuation and show stray semicolons or commas. Use `\quad` or `\qquad` for space, and `\mathbin{.}` for a dot with space around it.
