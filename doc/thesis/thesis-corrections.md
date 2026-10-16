# Thesis corrections

Errors found in the [thesis](2014-10-28-phd-thesis.pdf) while formalising it, and how the Rocq development corrects them. Page numbers are the printed ones.

## 1. The listener reads too few fields from a notification

**Where:** Section 5.3.3, the definition of **listening** on p.122, and Example 5.13 on p.124.

**Thesis:**

$$\mathbf{listening} \overset{\text{def}}{=} \mathit{chanAN}\langle r, m'' \rangle?\mathbin{.}\mathbf{checkRange}(m'', r) + \cdots$$

Example 5.13 has the trace label $\mathit{chanAN}\langle m'', r \rangle?$, with the two fields the other way round.

**Correction:**

$$\mathbf{listening} \overset{\text{def}}{=} \mathit{chanAN}\langle r, m'', l' \rangle?\mathbin{.}\mathbf{checkRange}(m'', r) + \cdots$$

The listener reads the position $l'$ and ignores it. The trace label in Example 5.13 becomes $\mathit{chanAN}\langle r, m'', l' \rangle?$.

**Why:** The interface forwards a notification as the original message $\langle m, l \rangle$ with its range in front, so as $\langle r, m, l \rangle$. This is rule IFWD-OUT in Table 4.11 (p.89), explained in Remark 4.15 (p.88). An input only accepts a message of its own length, by the premise $|\vec{v}| = |\vec{x}|$ of PFX-IN-MSG in Table 4.3 (p.67). So as written, the listener can never accept a notification, and an entity never reacts when one of its broadcasts reached too small a range. The proof of Lemma 6.26 (p.154) already assumes that the listener accepts $\langle r, m, l \rangle$, so the correction matches what the proof relies on.

**Found by:** [pass-1 report, root cause 4](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#4-listener-notification-arity-also-in-the-thesis).

## 2. Patience needs guarded definitions

**Where:** Theorem 4.7 (Patience) on p.80, Remark 4.2 (Guardedness) on p.69, and the definition of **checkRange** in Section 5.3.3 on p.122.

**Thesis:** Theorem 4.7 says that a process that can't do a $\tau$ action can delay:

$$\neg P \xrightarrow{\tau} \quad\Rightarrow\quad \exists d, P \xrightarrow{d}$$

It holds for every process, with no condition on the definitions. Remark 4.2 says that names in a definition "should be guarded", meaning each sits under an action prefix, but it is advice to the programmer, not a hypothesis of the theorem.

**Correction:** Theorem 4.7 holds when the definitions are guarded in this weaker sense: every cycle of names calling each other passes through an action prefix. Equivalently, the names can be ranked so that a definition only calls lower-ranked names outside a prefix. In the Rocq development the condition is the class `GuardedDefs` in `SoftwareLanguage.v`. Patience is `patienceSoft`, which needs it, as do the results it rests on: `progressSoft`, `minGuardExists`, `outListEx`, `inListEx` and `noSyncDec`.

**Why:** Remark 4.2's own example, $\mathbf{nonsense}(x, y) \overset{\text{def}}{=} \mathbf{nonsense}(x, y)$, can neither act nor delay, so Theorem 4.7 fails for it. The original code didn't hit this because it fixed the protocol into the language and proved the theorem by checking each protocol process in turn. Remark 4.2's strict form would be too strong: the protocol itself breaks it, since **checkRange** calls **listening** under an `if`, not an action prefix. The weaker condition allows that, and `ProtocolBridge.v` proves that the protocol meets it.

**Found by:** making the language generic, in [#3](https://github.com/bhandalflip/PhD-Formalilsing-Comhordu/pull/3).
