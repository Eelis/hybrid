(*
Require interval_abstraction square_flow_conditions concrete EquivDec.
Require Import List util list_util geometry monotonic_flow stability.
*)

Require Import hybrid.hypergeometry.
Require Import hybrid.util.
Require Import hybrid.c_util.
Require Import hybrid.square_abstraction.
Require Import hybrid.vector_setoid.
Require Import hybrid.monotonic_flow.

Require Import CoLoR.Util.Vector.VecUtil.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  (* Let's fix a dimension *)

  Variable n : nat.

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

  Variables
    (flows : concrete.Location chs -> vector (Flow CRasCSetoid) n)
    (flow_inv : concrete.Location chs -> 
      forall i (ip : (i < n)%nat), OpenRange -> OpenRange -> OpenRange)
    (flow_inv_correct : forall l i (ip : (i < n)%nat), 
      range_flow_inv_spec (Vnth (flows l) ip) (flow_inv l ip))
    (flow_separable : forall l p t,
      concrete.flow chs l p t = xyp (vector_flow (flows l) (pxy p) t)).

End contents.
