(** Prints every moved definition and result with the network notations in scope, so that the
    output can be compared across the move. Run from the repository root after make:
    rocq c -q -R src ComhCoq moved_before.v *)

Require Import ComhCoq.lang.NetworkLanguage.
Require Import ComhCoq.protocol.EntAuxDefs.
Require Import ComhCoq.protocol.NetAuxBasics.
Print EntAuxDefs.incomingEnt.
Print NetAuxBasics.inPosNet.
Print NetAuxBasics.distNet.
Print NetAuxBasics.outgoing.
Print NetAuxBasics.incomingNet.
Print NetAuxBasics.incomingNetNotif.
Print NetAuxBasics.mState_in_net.
Print NetAuxBasics.transGuard.
Print NetAuxBasics.liftEntNet.
Check @NetAuxBasics.inPos_pres_disc.
Check @NetAuxBasics.outgoing_del.
Check @NetAuxBasics.outgoing_del_contra.
Check @NetAuxBasics.outgoing_disc_pres.
Check @NetAuxBasics.incomingNetNotif_disc_pres.
Check @NetAuxBasics.inPos_del_bound_bkwd.
Check @NetAuxBasics.inPos_ex.
Check @NetAuxBasics.distNet_intro.
Check @NetAuxBasics.inPos_pos.
Check @NetAuxBasics.disc_pres_distNet_bkwd.
Check @NetAuxBasics.del_link_distNet_bkwd.
Check @NetAuxBasics.distNet_elim.
Check @NetAuxBasics.inRange_out_input.
Check @NetAuxBasics.transGuard_elim.
Check @NetAuxBasics.transGuard_intro.
Check @NetAuxBasics.mState_disc_pres.
Check @NetAuxBasics.mState_in_net_unique.
Check @NetAuxBasics.inPos_unique.
Check @NetAuxBasics.outNet_incomingNetNotif.
Check @NetAuxBasics.incoming_net_ent.
Check @NetAuxBasics.incoming_ent_net.
