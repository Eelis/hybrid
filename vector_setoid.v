Require Export VecUtil.
Require Export VecEq.
Require Export CSetoids.
Require Export SetoidClass.
Require Import c_util.
Require Export Coq.Classes.EquivDec.

Set Implicit Arguments.

(** * CSetoid on vectors. *)

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

(*
  Instance eqA : SetoidClass.Setoid A :=
    { equiv := @st_eq (cs_crr A); setoid_equiv := st_isSetoid A }.
*)

  Let vec_eq := @eq_vec A (@cs_eq A) n.

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

(* FIXME, this should come from CoLoR.Util.Vector.VecEq.v *)
Add Parametric Morphism A n i (ip : (i < n)%nat) : 
  (fun v : vecCSetoid A n => Vnth v ip)
  with signature (@cs_eq _) ==> (@cs_eq _)
    as Vnth_Cmorph.

Proof.
  intros. apply Vforall2n_nth with (R := @st_eq _). assumption.
Qed.

(** * Decidable Leibniz equality on vectors *)

Section vector_eqdec.

  Variable n : nat.
  Variable A : Type.
  Variable eqA_dec : EqDec A eq.

  Global Program Instance vector_EqDec : EqDec (vector A n) eq.
  Next Obligation.
    apply eq_vec_dec; auto.
  Qed.

End vector_eqdec.
