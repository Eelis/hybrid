Require Import hybrid.abstract.
Require Import hybrid.geometry.
Require Import hybrid.square_abstraction.

Require Import hybrid.examples.room_heating.conc.

Set Implicit Arguments.

Local Open Scope CR_scope.
Local Open Scope vec_scope.

Module RoomHeatingAbstract (Import RHS : RoomHeatingSpec).

  Module conc := RoomHeatingConcrete RHS.

  Definition room_heating_flow_inv (ds : DS) (a b : OpenRange) : OpenRange :=
    

  Definition clock_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
    square_flow_conditions.one_axis.flow_range
      _ flow.positive_linear.inv_correct flow.positive_linear.mono a b.

  Definition temp_flow_inv (l: Location): OpenRange -> OpenRange -> OpenRange :=
    match l with
    | Heat => flow.scale.inv two_pos (square_flow_conditions.one_axis.flow_range
      _ flow.positive_linear.inv_correct flow.positive_linear.mono)
    | Cool => dec_exp_flow.inv milli
    | Check => flow.scale.inv half_pos (dec_exp_flow.inv milli)
    end.

  Lemma clock_rfis l: range_flow_inv_spec (clock_flow l) (clock_flow_inv l).


(*
  Definition ap : abstract.Space conc.concrete_system :=
  square_abstraction.ap _ _ _ (NoDup_bnats 6) (NoDup_bnats 6)
  _ _ clock_interval temp_interval.

  Definition system (eps : Qpos) : abstract.System ap :=
    abstract.Build_System (initial_dec eps) (disc_trans_dec eps) (abstract_cont_trans_over.cont_sharing_overestimator_from_substantial_overestimator (cont_trans eps)).
*)

End RoomHeatingAbstract.
