# Thesis corrections

Errors found in the [thesis](2014-10-28-phd-thesis.pdf) while formalising it, and how the Rocq development corrects them. Page numbers are the printed ones.

## 1. The listener reads too few fields from a notification

**Where:** Section 5.3.3, the definition of **listening** on p.122, and Example 5.13 on p.124.

**Thesis:**

$$\mathbf{listening} \overset{\text{def}}{=} \mathit{chanAN}\langle r, m'' \rangle?\,.\,\mathbf{checkRange}(m'', r) + \cdots$$

Example 5.13 has the trace label $\mathit{chanAN}\langle m'', r \rangle?$, with the two fields the other way round.

**Correction:**

$$\mathbf{listening} \overset{\text{def}}{=} \mathit{chanAN}\langle r, m'', l' \rangle?\,.\,\mathbf{checkRange}(m'', r) + \cdots$$

The listener reads the position $l'$ and ignores it. The trace label in Example 5.13 becomes $\mathit{chanAN}\langle r, m'', l' \rangle?$.

**Why:** The interface forwards a notification as the original message $\langle m, l \rangle$ with its range in front, so as $\langle r, m, l \rangle$. This is rule IFWD-OUT in Table 4.11 (p.89), explained in Remark 4.15 (p.88). An input only accepts a message of its own length, by the premise $|\vec{v}| = |\vec{x}|$ of PFX-IN-MSG in Table 4.3 (p.67). So as written, the listener can never accept a notification, and an entity never reacts when one of its broadcasts reached too small a range. The proof of Lemma 6.26 (p.154) already assumes that the listener accepts $\langle r, m, l \rangle$, so the correction matches what the proof relies on.

**Found by:** [pass-1 report, root cause 4](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis).
