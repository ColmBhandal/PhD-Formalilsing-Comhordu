# src/: rules for the Rocq development

## Statements are frozen; proofs are not

- **Never change the statement** of an existing `Lemma`, `Theorem`, `Conjecture`, `Definition`, `Inductive`, `Record` or `Fixpoint`, and never delete one, without human approval. If one is false or mis-stated, leave it `Admitted` and write it up in a report (see `doc/reports/AGENTS.md`).
- **Prove as stated.** Replace `Admitted.` with a complete proof ending in `Qed.`. Turn a `Conjecture` into a `Lemma` with the same name and statement.
- **Don't add** `Axiom`, `Parameter`, `Conjecture`, `Hypothesis`/`Variable` outside a section, `Admitted`, `admit`, or the LibTactics `skip`.
- **Model axioms** in `ComhBasics.v` (`Mode`, `msgLatency`, `period`, `minDistComp`, …) are deliberately abstract and are not to be proved or instantiated in place.
- **`Parameter` stubs** (`reachableEnt`, `nextModeEnt`, `inPosEnt`, `currModeNet`, `nextModeNet`) are unfinished definitions. Propose completions in a report; don't fill them in.
- **Extra logical axioms:** the stdlib's classical logic, functional extensionality and proof irrelevance (already in the trust base) are allowed. Any newly used one must be listed in the PR and the report.

## The language and the protocol

- The language files (`LanguageFoundations`, `SoftwareLanguage`, `InterfaceLanguage`, `ModeStateLanguage`, `EntityLanguage`, `NetworkLanguage`, `ProcEquiv`) are generic in the process names and their definitions. They never import a protocol file.
- The protocol plugs in through `Protocol.v`, which defines its processes as instances of `ProcNames` and `ProcDefs`, and `ProtocolBridge.v`, which proves that they meet the language's conditions, such as `GuardedDefs`, and holds facts true only of this protocol. Protocol files import `ProtocolBridge`.
- Put a language file's generic code in one `Section` whose `Context` takes the class instances. Rocq drops a section's notations, tactics and `Open Scope` when it ends, so put `Reserved Notation` above the section, declare each notation again after it, and define after it any tactic a later file uses.
- Avoid closing and reopening a section to fit in a notation or tactic. Each extra `Section`/`End` pair is clutter. If a proof inside the section needs a tactic that has to live after it, write the proof without the tactic.
- Give an `Admitted` lemma inside a section a `Proof using` line. Without one it depends on every instance in the section, including `GuardedDefs`.

## Markers and conventions

- `Admitted (* UPGRADE-BROKEN *)` marks a proof that broke in a toolchain upgrade and couldn't be fixed on the spot.
- Trailing labels such as `Admitted (*4*)`, `(*R*)`, `(*D- foo*)` and `(*#tag*)` are the 2015 triage labels; see the workstream appendix. Remove a label together with its `Admitted` when the proof lands.
- Read the `(*Proof: …*)` sketch comments before proving. Keep them.
- **Helper lemmas** go immediately before the lemma that first needs them. Name them after it (`<lemma>_aux`, `<lemma>_aux2`, …). Make them `Local` if nothing else uses them.

## Libraries and tactics

- Import the stdlib explicitly: `From Stdlib Require Import …`.
- Import project modules as `Require Import ComhCoq.<Module>.` (existing style) or `From ComhCoq Require Import <Module>.`.
- For real-number goals, prefer `lra`/`nra`/`lia` over the hand-rolled lemmas in `RInequalities.v`/`StandardResults.v`. Reach for mathcomp-analysis's `Rstruct` bridge only when the stdlib lacks a lemma (see `doc/adr/2026-10-13-stdlib-reals-with-mathcomp-bridge.md`).
- `Extras/LibTactics.v` is vendored third-party code. Change it only for toolchain compatibility.

## Checks before committing

- `make` must succeed from clean.
- `make assumptions` must not gain any new entry except proofs that left the list.
