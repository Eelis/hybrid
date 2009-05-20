Require Import room_heating.
Require Import QArith.
Require Import Program.

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

End RHS.

Module RHSex := RoomHeating RHS.
