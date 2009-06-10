Require Import QArith.
Require Import util.
Require Import c_util.
Require Import nat_util.
Require Import list_util.
Require Import Program.
Require Import CRln.
Require Import hs_solver.
Require Import monotonic_flow.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import vector_setoid.
Require square_abstraction.
Require decreasing_exponential_flow.

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
  Parameter on_lt_off : Vforall2n (fun on off => (on < off)%Q) on off.

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

  Instance DS_eq_dec: EquivDec.EqDec DS eq.
  Proof.
    unfold EquivDec.EqDec. apply eq_vec_dec.
    decide equality.
  Defined.

  Fixpoint exhaustiveRS (n : nat) : list (vector RoomState n) :=
    match n with
    | 0%nat => [ Vnil ]
    | S p => 
        let all rs := List.map (fun vs => Vcons rs vs) (exhaustiveRS p) in
          all NoHeater ++ all HeaterOn ++ all HeaterOff
    end.

  Ltac in_or_app_proof :=
    solve 
    [ apply in_map; auto
    | apply in_or_app; left; in_or_app_proof
    | apply in_or_app; right; in_or_app_proof
    ].

  Lemma exhaustiveRS_correct x : In x (exhaustiveRS n).
  Proof with auto.
    induction x.
    left. ref.
    simpl. destruct a; in_or_app_proof.
  Qed.

  Instance locations : ExhaustiveList DS :=
    { exhaustive_list := exhaustiveRS n }.
  Proof.
    apply exhaustiveRS_correct.
  Defined.

  Lemma exhaustiveRS_NoDup n : NoDup (exhaustiveRS n).
  Proof with auto.
    induction n0; simpl.
    constructor...
    repeat apply NoDup_app; intros;
      try solve 
      [ apply NoDup_map; auto; intros;
        match goal with
        | H: Vcons ?a ?x = Vcons ?b ?y |- _ =>
            set (w := Vcons_eq a b x y); intuition
        end
      | intro;
        match goal with
        | H: In _ (_ ++ _) |- _ =>
            destruct (in_app_or H); clear H
        | _ => idtac
        end;
        match goal with
        | H: In ?x _, H': In ?x _ |- _ =>
          let l := fresh "l" in set (l := ListUtil.in_map_elim H);
          let r := fresh "r" in set (r := ListUtil.in_map_elim H')
        end;
        decomp; subst; discriminate
      ].
  Qed.

  Lemma NoDup_locations : NoDup locations.
  Proof.
    apply exhaustiveRS_NoDup.
  Qed.

   (** The continuous state of the system consists of
       temperatures of all the rooms. *)
  Definition CS := vecCSetoid CRasCSetoid n.

  Definition State := (DS * CS)%type.
  Definition ds : State -> DS := fst.
  Definition cs : State -> CS := snd.

   (** initial state predicate *)
  Definition initial (s : State) : Prop :=
    let init_room i ip :=
      match initHeaters [@ip] with 
      | false => NoHeater
      | true =>
          let temp := initTemp [@ip] in
          let threshold := on [@ip] in
            match Qlt_le_dec temp threshold with
            | left _ => HeaterOn
            | right _ => HeaterOff
            end
      end
    in
    let check_temp actual prescribed := actual = 'prescribed in
      ds s = Vbuild init_room /\
      Vforall2n check_temp (cs s) initTemp.

   (** invariant *)
  Definition invariant (s : State) : Prop :=
    let check_room i ip :=
      let temp := (cs s) [@ip] in
      let roomState := (ds s) [@ip] in
        match roomState with
          (* no heater, no invariant *)
        | NoHeater => True
          (* heater on, temperature below [off] threshold *)
        | HeaterOn => temp <= '(off [@ip])
          (* heater off, temperature above [on] threshold *)
        | HeaterOff => '(on [@ip]) <= temp
        end
    in
      check_n check_room.

  Lemma initial_invariant s : initial s -> invariant s.
  Proof with auto.
    intros [dS cS] [init_dS init_cS].
    simpl in *. subst.
    apply check_n_holds. intros. simpl in *.
    unfold roomState. rewrite Vbuild_nth.
    destruct (initHeaters [@ip])...
    unfold temp.
    destruct (Qlt_le_dec (initTemp [@ip]) (on [@ip]));
      rewrite (Vforall2n_nth _ _ _ ip init_cS);
      eapply (proj2 (CRle_Qle _ _))...
    apply Qlt_le_weak. apply Qlt_trans with (on [@ip])...
    apply (Vforall2n_nth _ _ _ ip on_lt_off).
  Qed.

  Lemma invariant_wd: forall l l', l = l' ->
    forall (p p': CS), p [=] p' -> (invariant (l, p) <-> invariant (l', p')).
  Proof.
    unfold invariant. intros. subst.
    apply check_n_equiv. intros. simpl.
    destruct (l')[@ip].
    tauto.
     (* FIXME: This should be handled by simple rewrite with setoid! *)
    rewrite (Vnth_Cmorph ip _ _ H0). tauto.
    rewrite (Vnth_Cmorph ip _ _ H0). tauto.
  Qed.

  Definition temp_reset (l1 l2 : DS) : square_abstraction.Reset :=
    square_abstraction.Reset_id.

  Definition reset (l1 l2 : DS) (cs : CS) : CS :=
    Vmap (square_abstraction.apply_Reset (temp_reset l1 l2)) cs.

  Definition guard (s : State) (l2 : DS) : Prop :=
    let (l1, cs) := s in
      (* a heater is moved from room [j] to room [i] *)
      exists i, exists ip : (i < n)%nat,
      exists j, exists jp : (j < n)%nat,
         (* rooms other than [i] and [j] remain unchanged *)
        (forall k (kp : (k < n)%nat), 
          k <> i -> k <> j -> l1 [@kp] = l2 [@kp]) /\
         (* room [i] had no heater and now gets one *)
        hasHeater (l1 [@ip]) = false /\ hasHeater (l2 [@ip]) = true /\
         (* room [j] had a heater and now it's removed *)
        hasHeater (l1 [@jp]) = true  /\ hasHeater (l2 [@jp]) = false /\
         (* temperature in room [i] is <= [get_i] *)
        cs [@ip] <= '(get [@ip]) /\
         (* the difference of temperatures in rooms [j] and [i] is at 
            least [diff_i] *)
        '(diff [@ip]) <= (cs [@jp]) - (cs [@ip]).

  Definition room_flow (rs : RoomState) : Flow CRasCSetoid :=
    match rs with
    | HeaterOn => flow.scale.flow ('2) flow.positive_linear.f
    | HeaterOff | NoHeater => decreasing_exponential_flow.f
    end.

  Definition flow (l : DS) := vector_flow (Vmap room_flow l).

  Definition concrete_system: concrete.System :=
    concrete.Build_System _ _ NoDup_locations initial invariant
    initial_invariant invariant_wd flow guard reset.

End RoomHeating.
