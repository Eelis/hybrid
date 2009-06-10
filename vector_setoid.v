Require Export VecUtil.
Require Export VecEq.
Require Export CSetoids.
Require Export SetoidClass.
Require Import c_util.

Set Implicit Arguments.

Section VectorCSetoid.

  Variables A : CSetoid.
  Variable n : nat.

  Notation vec := (vector A n).
  
  Definition vec_ap (x y : vec) : CProp.
  Proof.
    induction n; intros.
    exact False.
    inversion x. inversion y. 
    exact ((a [#] a0) or (IHn0 X X0)).
  Defined.

  Instance eqA : SetoidClass.Setoid A :=
    { equiv := @st_eq (cs_crr A); setoid_equiv := st_isSetoid A }.

  Let vec_eq := @eq_vec A eqA n.

  Lemma is_vec_CSetoid : is_CSetoid vec vec_eq vec_ap.
  Proof.
    constructor.
     (* irreflexivive *)
admit.
     (* Csymmetric *)
admit.
     (* cotransitive *)
admit.
     (* tight_apart *)
admit.
  Admitted.

  Definition vecCSetoid : CSetoid := 
    Build_CSetoid _ _ _ is_vec_CSetoid.

End VectorCSetoid.

(* FIXME, this should come from CoLoR.Utils.Vector.VecEq.v *)
Add Parametric Morphism A n i (ip : (i < n)%nat) : (fun v : vecCSetoid A n => Vnth v ip)
  with signature (@st_eq _) ==> (@st_eq _)
    as Vnth_Cmorph.

Proof.
  intros. apply Vforall2n_nth with (R := @st_eq _). assumption.
Qed.

(*
Why setoid rewrite doesn't work with this morphism?

Require Import Morphisms.
Print Instances Morphism.

(* Let's test it... *)
Lemma test n (x y : vecCSetoid CRasCSetoid n) :
  x [=] y -> forall i (ip : (i < n)%nat), Vnth x ip [=] Vnth y ip.
Proof.
  intros.
  (* It's just an instance of the morphism: *)
(*  apply Vnth_morph. assumption.*)
  (* and yet we cannot rewrite... *)
  rewrite H.
Qed.
*)
