Require Import hybrid.tactics.
Require Import hybrid.abstract.
Require Import hybrid.geometry.
Require Import hybrid.square_abstraction.
Require Import hybrid.flow.

Require Import hybrid.examples.room_heating.conc.

Set Implicit Arguments.

Local Open Scope CR_scope.
Local Open Scope vec_scope.

Module RoomHeatingAbstract (Import RHS : RoomHeatingSpec).

  Module Import conc := RoomHeatingConcrete RHS.

  Definition two_pos: CRpos ('2) := positive_CRpos 2.

  Definition room_flow_inv (rs : RoomState) : OpenRange -> OpenRange -> OpenRange :=
    match rs with
    | HeaterOn => flow.scale.inv two_pos (square_flow_conditions.one_axis.flow_range
      _ flow.positive_linear.inv_correct flow.positive_linear.mono)
    | HeaterOff
    | NoHeater => decreasing_exponential_flow.inv milli
    end.

  Lemma room_flow_ok l : range_flow_inv_spec (room_flow l) (room_flow_inv l).
  Proof with auto.
    destruct l; crunch.
  Qed.

End RoomHeatingAbstract.
