(** Prints every moved definition and result with the network notations in scope, so that the
    output can be compared across the move. Run from the repository root after make:
    rocq c -q -R src ComhCoq moved_after.v *)

Require Import ComhCoq.lang.NetworkLanguage.
Print EntityLanguage.incomingEnt.
Print NetworkLanguage.inPosNet.
Print NetworkLanguage.distNet.
Print NetworkLanguage.outgoing.
Print NetworkLanguage.incomingNet.
Print NetworkLanguage.incomingNetNotif.
Print NetworkLanguage.mState_in_net.
Print NetworkLanguage.transGuard.
Print NetworkLanguage.liftEntNet.
Check @NetworkLanguage.inPos_pres_disc.
Check @NetworkLanguage.outgoing_del.
Check @NetworkLanguage.outgoing_del_contra.
Check @NetworkLanguage.outgoing_disc_pres.
Check @NetworkLanguage.incomingNetNotif_disc_pres.
Check @NetworkLanguage.inPos_del_bound_bkwd.
Check @NetworkLanguage.inPos_ex.
Check @NetworkLanguage.distNet_intro.
Check @NetworkLanguage.inPos_pos.
Check @NetworkLanguage.disc_pres_distNet_bkwd.
Check @NetworkLanguage.del_link_distNet_bkwd.
Check @NetworkLanguage.distNet_elim.
Check @NetworkLanguage.inRange_out_input.
Check @NetworkLanguage.transGuard_elim.
Check @NetworkLanguage.transGuard_intro.
Check @NetworkLanguage.mState_disc_pres.
Check @NetworkLanguage.mState_in_net_unique.
Check @NetworkLanguage.inPos_unique.
Check @NetworkLanguage.outNet_incomingNetNotif.
Check @NetworkLanguage.incoming_net_ent.
Check @NetworkLanguage.incoming_ent_net.
