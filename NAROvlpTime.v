(** This file was written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.*)

(***************************** Standard Imports *****************************)

Require Import Equality.

Add LoadPath "Extras".
Require Import LibTactics.

(***************************** Specialised Imports *****************************)

Require Import StandardResults.
Require Import ComhBasics.
(*
Require Import LanguageFoundations.
Require Import SoftwareLanguage.
Require Import ProtAuxDefs.
Require Import InterfaceLanguage.
Require Import ModeStateLanguage.
Require Import EntityLanguage.*)
Require Import NetworkLanguage.
(*Require Import EntAux.*)
Require Import NetAuxBasics.
Require Import NetAuxDefs.


(*If an entity is pending then it cannot delay.*)
Theorem pending_urgent (n n' : Network) (d : Delay) (i : nat) (p : reachableNet n) :
  pending i n p -> ~ n -ND- d -ND> n'. Admitted. (*1*)
(**Proof: *SPAWN SEPARATE URGENCY RESULTS FOR THIS DONE*
Induction on pending. We have 2 cases. Case 1 is that we are
ovWaitStateNet m t x 0 i n- the y parameter can be shown to be 0 (separate proof?).
In this case, the input on pos is enabled and so the process can't delay by
progress [salvaged?]. Case 2 is the ovReadyStateNet m t l i n', which is ready to
output on io. Again by progress this means a delay is not possible.*)

(* If an entity is pending, and the same entity is in the state
ovWaitState m u x y, then we can show that u is equal to tw(m0, m) + period m, for some m0.*)
Theorem pending_time1 (n : Network) (m : Mode) (i : nat)
  (u x y : Time) (p : reachableNet n) :
  pending i n p -> ovWaitStateNet m u x y i n -> exists m0 q,
  u = addTime (waitTime m0 m q) (period m). Admitted. (*1*)
(**Proof: COMMON TACTICS FOR THE ADDTIME SHIT? THERE ARE MORE THEOREMS OF A SIMILAR NATURE.
By induction on pending. In the base case, we have that the previous state was
init m and so by backtracking (...) we can show that y = 0 and u = tw(m0, m) + period m.
In the first inductive case, we can show that u does not change from one state to the next.
The other two inductive cases fail because they involve ovReadyState, which is not
ovWaitState.*)

(* If an entity is pending, and the same entity is in the state ovReadyState m u l,
then we can show that u is equal to tw(m0, m) + period m, for some m0.*)
Theorem pending_time2 (n : Network) (m : Mode) (i : nat)
  (u : Time) (l : Position) (p : reachableNet n) :
  pending i n p -> ovReadyStateNet m u l i n ->
  exists m0 q, u = addTime (waitTime m0 m q) (period m).
  Admitted. (*1*)
(**Proof: Induction on pending. Base case fails because it only applies to ovWait.
Discrete inductive case can be shown by (backtracking + automation) to follow from
ovWaitState m u t' i n. But then by (pending_time1), we have that u = tw(m0, m) + period m.
And since the u is the same across the transition, it holds now. The delay inductive case
fails because delay can be shown to be impossible when a state is pending (pending_urgent).*)

(*If an entity is nextSince m t, and the same entity is in the state ovReadyState m u l,
then t + u is constant, equal to the sum of the wait time to m from some mode, tw(m0, m)
and the period of broadcast for m, period m. This is the combination of two results*)
Theorem nextSince_ovWait_ovReady_time (n : Network) (m : Mode) (i : nat)
  (t u x y : Time) (l : Position) (p : reachableNet n) :
  (nextSince m t i n p -> ovWaitStateNet m u x y i n ->
  exists m0 q, addTime t x = waitTime m0 m q
  /\ addTime u y = addTime x (period m)) /\ (*Half theorem*)
  (nextSince m t i n p -> ovReadyStateNet m u l i n ->
  exists m0 q,
  addTime t u = addTime (waitTime m0 m q) (period m)). Admitted. (*1*)
(**Proof: Mutual induction on nextSince. We don't have to actually use mutual induction,
just effectively we will be by proving these two results together as a conjunction and
the splitting by case analysis later.
!Four applications of ovWait_prev?! could be tidied up! For ovWait: In the base case,
we have that the entity in the previous state was pending, and the previous state was
ovReadySate m u0 l for some u0, l. Well then, by (pending_time2), we have that
u0 = tw(m0, m) + period m, for some m. But we also have by (...ovWait_prev...)
that x = u = u0 - period m, after eliminating the initState possibility because
it causes a contradiction. So substituting for u0 and tidying up we have x = tw(m0, m).
And since this is the base case, t = 0. So t + x = tw(m0, m) as required. Also from
(...ovWait_prev...) we have that on entering the state u = x and y = period m.
So u = x - y + period m holds. In the delay inductive case, t increases and u decreases
proportionately. By the I.H. t + u = tw(m0, m), and so for a delay of d, the new sum
becomes (t + d) + (u - d) = t + u = tw(m0, m), and our constant sum is preserved.
Also, x and y decrease by this d. So we want to show u = x - d - (y - d) + period m.
But this is clearly u = x - y + period m, which is our I.H. In the discrete case,
either the previous state was ovReady, and our result follows by the I.H. or the previous
state was not ovReady. In the latter case, we can use (...ovWait_prev...) and our inductive
hypothesis of nextSince (to eliminate initState) to show that the previous state must have
been ovReadyState m u0 l i n, with u = u0 - period m, and u = x. We then separately show
(the other half of this mutually inductive proof) that this combination of nextSince m t
and ovReadyState m u0 l implies that t + u0 = tw(m0, m) + period m, for some m0. Hence we
get t + u = tw(m0, m), and u = x from before, so t + x = tw(m0, m). Also, by
(...ovWait_prev...), we have much as in the base case, that on entering the state u = x
and y = period m. So u = x - y + period m holds. For ovReady: The base case fails to match,
the delay inductive case fails also because ovReady can't delay by progress [salvaged?],
and we can't go from ovWait to ovReady by a delay. So we're left with the discrete inductive
case, where the parameter t for next since is the same across both states. By
(...ovReady_prev...) then we show that the previous state was ovWaitState m u x 0.
Note the parameter y must be 0 so that the transition is enabled. But we also have by our
mutually inductive I.H. that u = x - y + period m, in this case y = 0, so we have
u = x + period m. So t + u = t + x + period m. But we know again by our mutual I.H.
that t + x = tw(m0, m). And so t + u = tw(m0, m) + period m as required.*)

(* If an entity is nextSince m t, and the same entity is in the state
switchBcState m, then we can show that mL + max AN trans < t.*)
Theorem nextSince_switchBc_lower (n : Network) (m : Mode) (i : nat)
  (t : Time) (p : reachableNet n) :
  nextSince m t i n p -> switchBcStateNet m i n ->
  msgLatency + Rmax adaptNotif transMax < t. Admitted. (*1*)
(**Proof: Induction on nextSince. Base case fails. Delay follows by monotonicity of t with
nextSince, as does the discrete case where the previous state is still switchBCState. So
the only case of any complexity is the discrete inductive case where the previous state was
not a switchBcState m. In which case we can show that it must be ovWaitState m u 0 y for
some u and y (...switchBc_prev...). We then have by (nextSince_ovWait_time), with x = 0,
that t + 0 = tw(m0, m), which simplifies to t = tw(m0, m). We can then expand tw to max
(mL + max(AN, trans) + Dw) (ts m1 m2) which, due to a strictly positive Dw, is greater
than mL + max AN trans as required.*)

(* If an entity is nextSince m t, and the same entity is in the state switchCurrState m,
then we can show that mL + max AN trans < t.*)
Theorem nextSince_switchCurr_lower (n : Network) (m : Mode) (i : nat)
  (t : Time) (p : reachableNet n) :
  nextSince m t i n p -> switchCurrStateNet i n ->
  msgLatency + Rmax adaptNotif transMax < t. Admitted. (*1*)
(**Proof: SIMILAR TO ANALOGOUS PROOF FOR SWITCHBC- SHARED TACTICS?
Induction on nextSince and case analysis on switchCurrState. The base case fails.
For the inductive case, we case analyse the previous state for the predicate switchCurrState.
 If this was true, then by the I.H. the t parameter in that state exceeds the lower bound, 
and so, by monotonicity of nextSince in both delay & discrete cases, so will the t' in this 
state. Otherwise, the previous state is not switchCurrState m. In which case we can show 
that it must be switchBcState m (...switchCurr_prev...). We then prove a similar result for 
this (nextSince_switchBc_lower) & since the t parameter is the same from the last state to 
this one because our transition is discrete, that result carries forward.*)