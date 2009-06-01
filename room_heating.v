Require Import QArith.
Require Export vec_util.
Require Import c_util.
Require Import nat_util.
Require Import Program.
Require square_abstraction.
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

   (** For every room the [on] threshold needs to be strictly 
       smaller than the [off] threshold. *)
  Parameter on_lt_off : Vforall2 (fun on off => on < off) on off.

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
Local Open Scope vec_scope.

(** * Instantiation of room heating to a given 
      specification *)
Module RoomHeating (Import RHS : RoomHeatingSpec).

   (** A state of the room. *)
  Inductive RoomState :=
  | NoHeater   (**r no heater in the room *)
  | HeaterOn   (**r there is heater and it's on *)
  | HeaterOff  (**r there is heater and it's off *)
  .

  Definition hasHeater rs :=
    match rs with
    | HeaterOn | HeaterOff => true
    | NoHeater => false
    end.

   (** The discreet state of the system consists of
       states of all the rooms. *)
  Definition DS := vector RoomState n.

   (** The continuous state of the system consists of
       temperatures of all the rooms. *)
  Definition CS := vector CR n.

  Definition State := (DS * CS)%type.
  Definition ds : State -> DS := fst.
  Definition cs : State -> CS := snd.

   (** initial state predicate *)
  Definition initial (s : State) : Prop :=
    let init_room i :=
      match initHeaters [[i]] with 
      | false => NoHeater
      | true =>
          let temp := initTemp [[i]] in
          let threshold := on [[i]] in
            match Qlt_le_dec temp threshold with
            | left _ => HeaterOn
            | right _ => HeaterOff
            end
      end
    in
    let check_temp actual prescribed := actual = 'prescribed in
      ds s = Vbuild init_room /\
      Vforall2 check_temp (cs s) initTemp.

   (** invariant *)
  Definition invariant (s : State) : Prop :=
    let check_room i :=
      let temp := (cs s) [[i]] in
      let roomState := (ds s) [[i]] in
        match roomState with
          (* no heater, no invariant *)
        | NoHeater => True
          (* heater on, temperature below [off] threshold *)
        | HeaterOn => temp <= '(off [[i]])
          (* heater off, temperature above [on] threshold *)
        | HeaterOff => '(on [[i]]) <= temp
        end
    in
      Vcheck_n check_room.

  Lemma initial_invariant s : initial s -> invariant s.
  Proof with auto.
    intros [dS cS] [init_dS init_cS].
    simpl in *. subst.
    apply Vcheck_n_holds. intros. simpl in *.
    unfold roomState. rewrite Vnth_Vbuild.
    destruct (initHeaters [[ip]])...
    unfold temp.
    destruct (Qlt_le_dec (initTemp [[ip]]) (on [[ip]]));
      rewrite (Vforall2_elim _ _ _ init_cS ip);
      eapply (proj2 (CRle_Qle _ _))...
    apply Qlt_le_weak. apply Qlt_trans with (on [[ip]])...
    apply (Vforall2_elim _ _ _ on_lt_off).
  Qed.

  Definition temp_reset (l1 l2 : DS) : square_abstraction.Reset :=
    square_abstraction.Reset_id.

  Definition reset (l1 l2 : DS) (cs : CS) : CS :=
    Vmap (square_abstraction.apply_Reset (temp_reset l1 l2)) cs.

  Definition guard (s : State) (l2 : DS) : Prop :=
    let (l1, cs) := s in
      (* a heater is moved from room [j] to room [i] *)
      exists i, exists j,
         (* rooms other than [i] and [j] remain unchanged *)
        (forall p : dom_lt n, 
          dom_lt_val p <> dom_lt_val i -> 
          dom_lt_val p <> dom_lt_val j ->
          l1 [[p]] = l2 [[p]]) /\
         (* room [i] had no heater and now gets one *)
        hasHeater (l1 [[i]]) = false /\ hasHeater (l2 [[i]]) = true /\
         (* room [j] had a heater and now it's removed *)
        hasHeater (l1 [[j]]) = true  /\ hasHeater (l2 [[j]]) = false /\
         (* temperature in room [i] is <= [get_i] *)
        cs [[i]] <= '(get [[i]]) /\
         (* the difference of temperatures in rooms [j] and [i] is at 
            least [diff_i] *)
        '(diff [[i]]) <= (cs [[j]]) - (cs [[i]]).

End RoomHeating.
