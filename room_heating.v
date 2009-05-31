Require Import QArith.
Require Export vec_util.
Require Import c_util.
Require Import nat_util.
Require Import Program.
Require Import CRln.

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

Local Open Scope CR_scope.

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
  Definition ds : State -> DS := fst.
  Definition cs : State -> CS := snd.

  Program Definition temp (cs : CS) (ip : dom_lt n) : CR :=
    Vnth cs ip.

  Definition initial : DS :=
    let init_room ip :=
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

  Definition invariant (s : State) : Prop :=
    let check_room ip :=
      let temp := Vnth (cs s) ip in
      let roomState := Vnth (ds s) ip in
        match roomState with
          (* no heater, no invariant *)
        | NoHeater => True
          (* heater on, temperature below [off] threshold *)
        | HeaterOn => temp <= '(Vnth off ip)
          (* heater off, temperature above [on] threshold *)
        | HeaterOff => '(Vnth on ip) <= temp
        end
    in
      Vcheck_n check_room.

End RoomHeating.
