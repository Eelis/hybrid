Require Export Bvector.
Require Import Program.
Require Import Omega.

Set Implicit Arguments.

Implicit Arguments Vnil [A].
Implicit Arguments Vcons.

Section Vnth.

  Variable A : Type.

  Program Fixpoint Vnth n (v : vector A n) : forall i, i < n -> A :=
    match v with
    | Vnil => 
        fun i ip => !
    | Vcons x p v' =>
        fun i =>
          match i with
          | 0 => fun _ => x
          | S j => fun H => Vnth v' (i:=j) _
          end
    end.

  Next Obligation.
  Proof.
    inversion ip.
  Qed.
  Next Obligation.
  Proof.
    auto with arith.
  Qed.

End Vnth.

Section Vbuild.

  Variable A : Type.

  Program Fixpoint Vbuild_spec (n : nat) (gen : forall i, i < n -> A) :
    { v : vector A n | forall i (ip : i < n), Vnth v ip = gen i ip } :=
    match n with
    | 0 => Vnil
    | S p => 
        let gen' := fun i ip => gen (S i) _ in
          Vcons (gen 0 _) (@Vbuild_spec p gen')
    end.

  Next Obligation.
  Proof.
    elimtype False. subst n. omega.
  Qed.
  Next Obligation.
    omega.
  Qed.
  Next Obligation.
    omega.
  Qed.
  Next Obligation.
    destruct_call Vbuild_spec. simpl.
    destruct n. discriminate.
    inversion Heq_n. subst.
    simplify_eqs. destruct i. pi.
    rewrite e. pi.
  Defined.

  Program Definition Vbuild n gen : vector A n := Vbuild_spec gen.

End Vbuild.

Require Import List.

Section vec_of_list.

  Variable A : Type.

  Fixpoint vec_of_list (l : list A) : vector A (length l) :=
    match l with
    | nil => Vnil
    | cons x m => Vcons x (vec_of_list m)
    end.

End vec_of_list.
