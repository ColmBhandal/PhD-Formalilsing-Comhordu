# Type the language's variables, and let an input bind each one only to a value of its type

Date: 2026-10-16
Status: 2026-10-16 accepted

## Context

The software language's input rule accepted any values, as long as there were as many as the prefix had variables. So a process could read a time where it expected a mode, and a protocol component could reach states that no entity reaches: a listener that compares a time with a mode and stops, or an overlap component holding a timer computed from a value that is no mode. The first proving pass found five lemmas false for this reason, and the component shapes of step 18 could only say that a received mode is some base value.

The thesis has the typing the code lacks. On page 64 the variables of an input prefix are typed, and only values of those types may be input. On page 65 the parameters of a definition are typed too, and Remark 4.1 assumes typing rules without giving them and defines the semantics only over well-typed processes. Channels are never typed. The question was how to bring that into the Rocq development, and the workstream named two candidates: a sort on each channel, or a type on each binder.

## Decision

Every variable carries a type, one of the six kinds of value the language has: a mode, a time, a position, a distance, a delay or a non-negative real. The input rule fires only when every arriving value has its variable's type, which also fixes the number of values. Nothing else changes: channels stay untyped, outputs are checked no more than before, and there is no static type system. The word is type, not sort, and the Rocq name is `ValType`.

## Consequences

- A value a component received is a value of the expected type, so the component shapes name modes, positions and distances, and the lemmas that fell to untyped inputs hold as stated.
- The semantics is the thesis's: fewer processes are reachable, and `safety` keeps its statement while meaning more.
- Anything that counted an input's values now types them: the input rule, the sort relation, the stamps on the symbolic channel lists, and the two lemmas about accepting a notification.
- Every variable is declared with its type. The protocol's eleven are, and a new protocol must do the same.
- A proof that needs an input with values left open needs a value of each type. The model does not promise a mode, so a mode has to come from the context.
- Two kinds of ill-formed state remain reachable in a lone process. A timer is undefined when its two modes have no transition between them, which only an entity rules out. The range the listener computes from a message is a plain non-negative real where the compatibility test wants a distance, which is root cause 5.

## Revisit when

Step 24 settles the numeric types. A static well-typedness judgement for definitions, the one page 65 stipulates, then becomes possible, and typed variables are the hook it needs.

## Alternatives considered

### A sort on each channel

Give each of the fourteen channels a list of sorts and check an input against its channel's. One table does the work, and the entity tiers already treat each channel as carrying one kind of value. But the mode state sends a mode on `chanMCurr` when the process reads it and receives nothing on the same channel when the process switches mode, so that channel has no single sort. Typing would have to cover inputs only, or each direction separately, which is an asymmetry to explain forever. An input prefix whose arity disagrees with its channel's sort would also need a separate well-formedness condition for the symbolic channel lists to stay complete. And it is not what the thesis does.

### A type annotation on each binder

Put the types in the syntax, so that an input prefix and a definition carry a list of typed variables, as the thesis writes them. This is the most literal reading of page 64, but it changes the shape of `inPrefix` and `def`, and with them substitution, free variables, matching, decidable equality on terms and every protocol process. Carrying the type on the variable gives the same discipline with none of that: the syntax is untouched and only the input rule gains a premise.

### A static type system now

Add a well-typedness judgement over expressions and processes and require it of every definition, as page 65 stipulates. It would not make a received value a mode; only the check at the input does that. And it would fail on the protocol today, because the overlap timers are arithmetic, which evaluates to a plain non-negative real, while the parameter that receives them is a time. Deciding that belongs with the other numeric typing questions in step 24.

### A typing hypothesis on each affected lemma

Leave the language as it was and add to each false lemma the hypothesis that the value read is a mode. This was the other option of root cause 3. It fixes five statements but none of the junk states, every later lemma about an input would need the same hypothesis, and the shapes would keep saying base value.

## Implementation notes

- **Names and places.** `ValType` with constructors `vtMode`, `vtTime`, `vtPosition`, `vtDistance`, `vtDelay` and `vtNonneg`, `valTypeOf : BaseType -> ValType`, `Var := var : ValType -> nat -> Var`, `varType` and `typedVals xs vs`, all in `src/lang/LanguageFoundations.v`. The protocol's variables are declared in `src/protocol/Protocol.v`: `vM`, `vMF`, `vM'` and `vM''` are modes, `vL` and `vL'` positions, `vT`, `vT'`, `vX` and `vY` times, and `vR` a distance.
- **The rule.** `stepDpIn` has the premise `typedVals l2 l1` in place of `length l1 = length l2`, and `sortIn` the same. `typedVals xs vs` is `Forall2` of "the value's type is the variable's type", and `typedVals_map` states it as `map valTypeOf vs = map varType xs`.
- **Stamps.** `ChanStamped` is `Channel * list ValType`, so an output stamps the types of the values it outputs and an input the types of its variables. The no-sync decision procedure is unchanged apart from the equality it uses. `inListEnabledEx` and `baseListEx` are gone: an input is enabled for the values whose types match, and there is no list of values of a given length any more.
- **Tactics.** `typed_vals` proves `typedVals` for explicit lists, `explicit_typed_input` turns a hypothesis `typedVals [vM] vs` into `vs = [baseMode m]`, and in `ProtAuxResults.v` `typed_witness` builds a value of each type for an input left open, taking a mode from the context. The inhabitants are `origin`, `zeroTime`, `zeroNonneg` and `onePos`.
- **Statements that changed.** `stepDpIn`, `sortIn`, `dae_inPfx`, `inPrefix_bisim_context`, `ChanStamped` with `outlOutEval` and `inlIn`, `outListEnabled`, `inListEnabled`, `enabledOutList` and `enabledInList` in the language. `listening_AN_prot` and `incomingNetNotif_del` take a range, a mode and a position in place of a list of length three. The three shape inductives in `ProtAuxResults.v` take modes, positions and distances, and `shOvWait` loses its side condition.
- **Proved by the change.** `rangeBad_next`, `gotRange_next`, `currComp_next` and `tfsStart_next` as stated, and `tfsStart_next_ent`, which was in the cone of `safety`. `safety` rests on 81 assumptions, down from 82. `currOK_listening_track`, the fifth lemma of root cause 3, stays admitted: it is also false because `nextEq`'s else branch returns to `listening`, which is a statement question for step 23.
- **Still stuck.** `shStuck` stays in `listenerShape` because of root cause 5, and `ovWaitStateExp` and `ovReadyStateExp` stay because of the undefined wait time. Thesis remark 1 describes the latter.
- **Naming.** `BaseType` is the Rocq type of base values, not of their types, so the new type is named for the values, `ValType`, and not `BaseType`-anything. Renaming `BaseType` itself to say what it is touches 145 places in 15 files and is left for later.
- **Report.** Root causes [3](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#3-untyped-process-inputs) and [5](../reports/2026-10-14-proof-completion-pass-1/root-causes-and-fixes.md#5-range-typing-esubtract-vs-bpossinc) of the first proving pass.
- **Thesis.** Pages 64 and 65 and Remark 4.1 for the typing; Table 4.3 on page 67 for PFX-IN-MSG, whose premise is the length check the code had; page 99 for the entity rules, which already pass a mode on `chanCurr` and `chanNext`.
