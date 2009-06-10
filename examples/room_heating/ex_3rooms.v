Require Import hybrid.examples.room_heating.conc.

Require Import Coq.Program.Program.

Ltac ref := reflexivity.

Module RHS <: RoomHeatingSpec.

  Definition n := 3.

  Lemma nPos : (n > 0)%nat.
  Proof. compute. auto with arith. Qed.

  Definition off := vec_of_list [21:Q; 21:Q; 21:Q].
  Definition on := vec_of_list [20:Q; 20:Q; 20:Q].
  Definition get := vec_of_list [18:Q; 18:Q; 18:Q].
  Definition diff := vec_of_list [1:Q; 1:Q; 1:Q].

  Definition initHeaters := vec_of_list [true; true; false].
  Definition initTemp := vec_of_list [20:Q; 20:Q; 20:Q].

  Lemma on_lt_off : Vforall2n (fun on off => on < off) on off.
  Proof.
    apply Vforall2n_intro. intros.
    do 3 (destruct i; [vm_compute; trivial | idtac]).
    simpl in ip. elimtype False. omega.    
  Qed.

End RHS.

Module RHSex := RoomHeatingConcrete RHS.
