Require Import hybrid.abstract.
Require Import hybrid.geometry.
Require Import hybrid.square_abstraction.

Require Import hybrid.examples.room_heating.conc.

Set Implicit Arguments.

Local Open Scope CR_scope.
Local Open Scope vec_scope.

Module RoomHeatingAbstract (Import RHS : RoomHeatingSpec).

  Module conc := RoomHeatingConcrete RHS.

End RoomHeatingAbstract.
