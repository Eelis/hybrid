Require Import QArith.
Require Export vec_util.
Require Import c_util.
Require Import Program.

Set Implicit Arguments.

Definition vectorQ := vector Q.

(** * Parametrization of the room heating example *)
Module Type RoomHeatingSpec.

   (** number of rooms *)
  Parameter n : nat.
  Parameter nPos : (n > 0)%nat.

   (** [initHeaters_i] indicates whether initially there
       is a heater in room [i]. This parameter induces
       the total number of heaters in the system. *)
  Parameter initHeaters : vector bool n.

   (** The [on] and [off] thresholds for thermostats
       in all rooms. *)
  Parameter on : vectorQ n.
  Parameter off : vectorQ n.

   (** heater can be moved to room [i] only if the 
       temperature in this room is below [get_i]. *)
  Parameter get : vectorQ n.

   (** heater can be moved from room [j] to room [i] 
       only if the temperature in room [j] is higher 
       than that in room [i] by at least [diff_i]. *)
  Parameter diff : vectorQ n.

   (** initial temperature in all rooms. *)
  Parameter initTemp : vectorQ n.

End RoomHeatingSpec.


(** * Instantiation of room heating to a given 
      specification *)
Module RoomHeating (Import RHS : RoomHeatingSpec).

   (** A state of the room. *)
  Inductive RoomState :=
  | NoHeater   (**r no heater in the room *)
  | HeaterOn   (**r there is heater and it's on *)
  | HeaterOff  (**r there is heater and it's off *)
  .

   (** The discreet state of the system consists of
       states of all the rooms. *)
  Definition DS := vector RoomState n.

   (** The continuous state of the system consists of
       temperatures of all the rooms. *)
  Definition CS := vector CR n.

  Definition State := (DS * CS)%type.

  Definition initial : DS :=
    let init_room i ip :=
      match Vnth initHeaters ip with 
      | false => NoHeater
      | true =>
          let temp := Vnth initTemp ip in
          let threshold := Vnth on ip in
            match Qlt_le_dec temp threshold with
            | left _ => HeaterOn
            | right _ => HeaterOff
            end
      end
    in
      Vbuild init_room.

End RoomHeating.
