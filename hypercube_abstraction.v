Require Import hybrid.hypergeometry.
Require Import hybrid.util.
Require Import hybrid.c_util.
Require Import hybrid.hlist_aux.
Require Import hybrid.square_abstraction.
Require Import hybrid.vector_setoid.
Require Import hybrid.monotonic_flow.
Require Import hybrid.stability.

Require Import CoLoR.Util.Vector.VecUtil.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  (* Let's fix a dimension *)

  Variable n : nat.

  Definition forallDim (F : forall i, (i < n)%nat -> Type) := 
    forall i (ip : (i < n)%nat), F i ip.

  (* If one has a concrete hybrid system.. *)

  Variable chs : concrete.System.

  (* .. and points in that system basically correspond to points in the plane.. *)

  Notation proj_morpher := 
    (morpher (@st_eq (concrete.Point chs) ==> @st_eq CRasCSetoid)%signature).

  Variable proj : vector proj_morpher n.

  Hypothesis xyp : HyperPoint n -> concrete.Point chs.
  
  Definition pxy (p : concrete.Point chs) : HyperPoint n :=
    Vmap (fun pi : proj_morpher => pi p) proj.

  Hypotheses
    (xyp_pxy: forall p, xyp (pxy p) = p)
      (* TODO: should we split this condition into separate dimensions, like in square_abstraction? *)
    (pxy_xyp: forall p, pxy (xyp p) = p). 

  (* .. and flow in that system is separable over the two axes.. *)

  Variables
    (flows : concrete.Location chs -> vector (Flow CRasCSetoid) n)
    (flow_inv : concrete.Location chs -> 
      forall i (ip : (i < n)%nat), OpenRange -> OpenRange -> OpenRange)
    (flow_inv_correct : forall l,
      forallDim (fun i ip => range_flow_inv_spec (Vnth (flows l) ip) (flow_inv l ip)))
    (flow_separable : forall l p t,
      concrete.flow chs l p t = xyp (vector_flow (flows l) (pxy p) t)).

  (* .. and on both axes, abstraction parameters can be formed based on
   OpenRange regions.. *)

  Context
    (intervals : vector Set n)
    (intervals_eq_dec : forallDim (fun i ip => EquivDec.EqDec (Vnth intervals ip) eq))
    (intervals_enum : forallDim (fun i ip => ExhaustiveList (Vnth intervals ip)))
    (intervals_NoDup : forallDim (fun i ip => NoDup (intervals_enum i ip)))
    (intervals_range : forallDim (fun i ip => Vnth intervals ip -> OpenQRange))
    (absInterval : forall (l : concrete.Location chs) (p : concrete.Point chs), concrete.invariant (l, p) ->
      forallDim (fun i ip =>
        DN (sig (fun int : Vnth intervals ip => in_orange (intervals_range i ip int) (Vnth (pxy p) ip))
      ))).

  Definition ap_inv_DN :
    forall (i : nat) (ip : (i < n)%nat) (l : concrete.Location chs) (p : concrete.Point chs),
      concrete.invariant (l, p) ->
      DN {i : Vnth intervals ip | in_orange (intervals_range ip i) (Vnth proj ip p)}.
  Proof.
    intros. set (w := absInterval l p H (ip:=ip)). simpl in w.
    unfold pxy in w. rewrite Vnth_map in w. exact w.
  Qed.

  Definition ap : abstract.Space chs :=
    abstract.hyper_space 
      (list_of_vec (Vbuild (fun i (ip : (i < n)%nat) =>
         interval_abstraction.space chs (Vnth proj ip) (intervals_NoDup ip) (intervals_range ip)
           (Region_eq_dec := intervals_eq_dec ip) (@ap_inv_DN i ip)
      ))).

  Definition region2range :
    forall (i : nat) (ip : (i < n)%nat),
      abstract.Region
        (Vnth (Vbuild (fun i (ip : (i < n)%nat) =>
          interval_abstraction.space 
            (Region_eq_dec:=intervals_eq_dec ip) chs (Vnth proj ip)
            (intervals_NoDup ip) (intervals_range ip) (@ap_inv_DN i ip)
        )) ip) -> OpenQRange.
  Proof.
    intros.
    rewrite Vbuild_nth in X.
    exact (intervals_range ip X).
  Defined.

  Definition square : abstract.Region ap -> OpenQHCube n :=
    hlist_map _ region2range.

  (*  .. then we can define useful things.

  For instance, we can easily make an invariant overestimator 
  (if one's invariant can be overestimated by a list of open squares): *)
  
End contents.
