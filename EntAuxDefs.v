(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Add LoadPath "Extras".

(***************************** Specialised Imports *****************************)

Require Import StandardResults.
Require Import ComhBasics.
Require Import LanguageFoundations.
Require Import InterfaceLanguage.
Require Import ModeStateLanguage.
Require Import SoftwareLanguage.
Require Import EntityLanguage.
Require Import ProtAuxDefs.


(***************************** Lifting *****************************) 

Inductive liftProcEnt (X : ProcTerm -> Prop) : Entity -> Prop :=
  | lifpe (p : ProcTerm) (l : Position) (h : Interface) (k : ModeState) :
    X p -> liftProcEnt X ([|p, l, h, k|]).

(******** Simple Lifted Predicates ********) 

(*Broadcast*)
Definition bcWaitStateEnt (m : Mode) (x : Time) : Entity -> Prop :=
liftProcEnt (bcWaitStateProt m x).
Definition sleepingStateEnt : Entity -> Prop :=
liftProcEnt sleepingStateProt.
Definition bcReadyStateEnt  (m : Mode) (l : Position) : Entity -> Prop :=
liftProcEnt (bcReadyStateProt m l).

(*Overlap*)
Definition dormantStateEnt : Entity -> Prop :=
liftProcEnt dormantStateProt.
Definition tfsStartStateEnt : Entity -> Prop :=
liftProcEnt tfsStartStateProt.
Definition initStateEnt (m : Mode) : Entity -> Prop :=
liftProcEnt (initStateProt m).
Definition ovReadyStateEnt (m : Mode) (t : Time) (l : Position) : Entity -> Prop :=
liftProcEnt (ovReadyStateProt m t l).
Definition switchCurrStateEnt : Entity -> Prop :=
liftProcEnt switchCurrStateProt.
Definition switchListenStateEnt : Entity -> Prop :=
liftProcEnt switchListenStateProt.
Definition tfsListenStateEnt := liftProcEnt tfsListenStateProt.
Definition ovAbortStateEnt := liftProcEnt ovAbortStateProt.
Definition tfsBcStateEnt := liftProcEnt tfsBcStateProt.
Definition switchBcStateEnt m := liftProcEnt (switchBcStateProt m).
Definition ovWaitStateEnt (m : Mode) (t x y : Time) : Entity -> Prop :=
liftProcEnt (ovWaitStateProt m t x y).
Definition tfsCurrStateEnt := liftProcEnt tfsCurrStateProt.
Definition tfsNextStateEnt m := liftProcEnt (tfsNextStateProt m).

(*Listener*)
Definition listeningStateEnt : Entity -> Prop :=
liftProcEnt listeningStateProt.
Definition currCompStateEnt (m : Mode) (r : Distance) : Entity -> Prop :=
liftProcEnt (currCompStateProt m r).
Definition pausedStateEnt := liftProcEnt pausedStateProt.
Definition abortOvlpStateEnt := liftProcEnt abortOvlpStateProt.
Definition badOvlpStateEnt := liftProcEnt badOvlpStateProt.
Definition nextEqStateEnt m m' := liftProcEnt (nextEqStateProt m m').
Definition currEqStateEnt m m'' := liftProcEnt (currEqStateProt m m'').
Definition gotMsgStateEnt m l := liftProcEnt (gotMsgStateProt m l).
Definition gotRangeStateEnt m r := liftProcEnt (gotRangeStateProt m r).
Definition currPincCheckStateEnt m m'' r := liftProcEnt (currPincCheckStateProt m m'' r).
Definition nextPincCheckStateEnt m m'' r := liftProcEnt (nextPincCheckStateProt m m'' r).
Definition rangeBadStateEnt m := liftProcEnt (rangeBadStateProt m).


(******** Compound Lifted Predicates ********) 

(*Broadcast*)

Definition broadcastStateEnt := liftProcEnt broadcastStateProt.

(*Overlap*)
Definition overlapStateEnt : Entity -> Prop :=
liftProcEnt overlapStateProt.
Definition nextSinceStateEnt : Entity -> Prop :=
liftProcEnt nextSinceStateProt.
Definition tfsStateEnt : Entity -> Prop :=
liftProcEnt tfsStateProt.
Definition switchStateEnt : Entity -> Prop :=
liftProcEnt switchStateProt.

(*Listener*)
Definition listenerStateEnt : Entity -> Prop :=
liftProcEnt listenerStateProt.


(***************************** Path predicates *****************************)


Inductive msgBadPathEnt : Entity -> Prop :=
  | mbpMsg p l h k m'' m l' : gotMsgStateProt m'' l' p -> currModeMState k = m -> 
    possiblyIncompatible m m'' (dist l l' -nn- speedMax *nn* msgLatency)
    -> msgBadPathEnt ([| p, l, h, k|])
  | mbpRng p l h k m'' m r : gotRangeStateProt m'' r p -> currModeMState k = m ->
    possiblyIncompatible m m'' r -> msgBadPathEnt ([|p, l, h, k|])
  | mbpBad p l h k : badOvlpStateProt p ->  msgBadPathEnt ([|p, l, h, k|]).

Inductive notifBadPathEnt : Entity -> Prop :=
  | nbpRng p l h k m : rangeBadStateProt m p -> currModeMState k = m ->
    notifBadPathEnt ([|p, l, h, k|])
  | nbpBad p l h k : badOvlpStateProt p -> notifBadPathEnt ([|p, l, h, k|]).

Inductive msgAbortPathEnt : Entity -> Prop :=
  | mapMsg p l h k m'' m m' l' :
    let r' := dist l l' -nn- speedMax *nn* msgLatency in
    gotMsgStateProt m'' l' p -> currModeMState k = m ->
    ~possiblyIncompatible m m'' r' -> 
    nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r' ->
    msgAbortPathEnt ([|p, l, h, k|])
  | mapGrng p l h k m'' m m' r : gotRangeStateProt m'' r p -> currModeMState k = m ->
   ~possiblyIncompatible m m'' r -> nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r -> msgAbortPathEnt ([|p, l, h, k|])
  | mapCuco p l h k m'' m' r : currCompStateProt m'' r p -> nextModeMState k = Some m' ->
    possiblyIncompatible m' m'' r -> msgAbortPathEnt ([|p, l, h, k|])
  | mapAbort p l h k : abortOvlpStateProt p -> msgAbortPathEnt ([|p, l, h, k|]).

Inductive notifAbortPathEnt : Entity -> Prop :=
  | napRng p l h k m m' : rangeBadStateProt m' p -> currModeMState k = m -> m <> m' ->
    nextModeMState k = Some m' -> notifAbortPathEnt ([|p, l, h, k|])
  | napCuok p l h k m' : currOKStateProt m' p -> nextModeMState k = Some m' ->
    notifAbortPathEnt ([|p, l, h, k|])
  | napAbort p l h k : abortOvlpStateProt p -> notifAbortPathEnt ([|p, l, h, k|]).

(***************************** Misc *****************************)

(** incomingEnt v e means v is in the incoming list of the interface of e.*)
Inductive incomingEnt (v : list Base) : Entity -> Prop :=
  | incent P l h K : incomingInter v h -> incomingEnt v ([|P, l, h, K|]).

(*When defining this, I don't think you need to bother with a restriction to "full action"s. First of all,
that would be an issue at the network level anyway. Secondly, it's OK at the network level to include some
"half action"s because it just means we're modelling, say, spurious messages from unkown entities, meaning
the system is in fact more robust than necessary, which is a good thing.*)
Parameter reachableEnt : Entity -> Prop.
(**Idea: Reflexivie transitive closure of initialEnt under entity transition relations*)

Parameter nextModeEnt : Mode -> Entity -> Prop.
(**Idea: Inductive with one constructor, in which the entity has mode state <m, m', d>, with m' the parameter to this relation*)

Parameter inPosEnt : Position -> Entity -> Prop.
(**Idea: Analogous to nextModeEnt except with position vs. mode state*)

(** An entity is initial if its consitutent process is
initial and its mode state is a stable, failSafe mode.*)
Inductive initialEnt : Entity -> Prop :=
  initEnt p l h m : initialProc p -> failSafe m ->
  initialEnt ([|p, l, h, m|]).
