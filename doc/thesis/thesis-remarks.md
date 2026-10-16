# Thesis remarks

Small things the formalisation has taught us about the [thesis](2014-10-28-phd-thesis.pdf) that are not errors in it. Each remark gives the printed page and the definition or remark number where there is one, the observation, a minimal example where one helps, and a link to the PR or report that found it. Departures from the thesis are in [`thesis-corrections.md`](thesis-corrections.md) instead.

## 1. A protocol process on its own can get stuck

**Where:** Remark 4.1 (Typing) on p.65; the domain of the transition time $tt$ on p.92, Definition 5.1 on p.107 and Definition 5.8 (Wait Time) on p.114; and the proofs of chapter 6, which reason about entities.

**Observation:** The thesis assumes its processes are well typed and defines the semantics only over such processes (Remark 4.1). It also makes the transition time $tt(m, m')$ a partial function, defined exactly when $m \longrightarrow m'$, so the wait time $tw(m, m')$ is partial too. Inside an entity both assumptions hold: the mode state only ever holds a next mode it can reach, and what a process reads on the mode state's channels and on $chanPos$ is what those components hold. A protocol process taken out of its entity, as an open system whose inputs come from an arbitrary environment, meets neither assumption, and it can reach states that no entity reaches.

**Example:** From $\mathbf{dormant}$, read $m'$ on $chanMNext$, then a mode $m$ on $chanMCurr$ with no transition $m \longrightarrow m'$. The process is now $\mathbf{ovWait}(m', tw(m, m') + period(m'), 0)$ with an undefined timer. It still answers $chanAbort$ and $chanBad$, and it broadcasts once its zero timer fires, but its pause timer never runs out, so it never reaches $\mathbf{switchBc}$. Untyped inputs do worse: read a time instead of a mode on $chanAN$, and the listener reaches $\mathbf{checkRange}$ with a condition that neither holds nor fails, a state with no transitions at all.

**Why it matters:** A result about a lone component, such as which state it is in after an action, has to allow for these states. That is why some process-level lemmas in `src/protocol/ProtAuxResults.v` describe a timer as an expression rather than a time. The typed statements belong at the entity level, where the mode state is in view, as in the thesis's own proofs. The formalisation has no typing rules for inputs yet; adding them is root cause 3 of the [pass-1 report](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#3-untyped-process-inputs).

**Found by:** [#8](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/8).
