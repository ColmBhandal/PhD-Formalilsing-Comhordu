# doc/thesis/: rules for the thesis and its corrections

- Never edit the thesis. It is a submitted document and can't be changed.
- Make every edit in [`thesis-corrections.md`](thesis-corrections.md) instead.
- Give each correction the printed page and the definition or remark number, what the thesis says, the correction, why, and a link to the PR or report that found it.
- Write maths in GitHub's LaTeX syntax: `$...$` inline and `$$...$$` for display.
- Don't use LaTeX spacing commands made of a backslash and punctuation, such as `\;`, `\,`, `\:`, `\!` or `\ `. Some Markdown viewers read them as escaped punctuation and show stray semicolons or commas. Use `\quad` or `\qquad` for space, and `\mathbin{.}` for a dot with space around it.
