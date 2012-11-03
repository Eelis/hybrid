Set Implicit Arguments.

Inductive bnat: nat -> Set :=
  | bO n: bnat (S n)
  | bS n: bnat n -> bnat (S n).

Fixpoint to_nat n (b: bnat n): nat :=
  match b with
  | bO _ => 0
  | bS _ x => S (to_nat x)
  end.

Section alt_rect.

  Variables
    (P: forall n: nat, bnat (S n) -> Type)
    (Pz: forall p, P (bO p))
    (Ps: forall n (b: bnat (S n)), P b -> P (bS b)).

  Let R (n: nat): bnat n -> Type :=
    match n with
    | O => fun _ => False
    | S _ => @P _
    end.

  Fixpoint RS (n : nat): forall (b : bnat n), R b -> R (bS b) :=
    match n return forall (b : bnat n), R b -> R (bS b) with
    | O => fun x f => False_rect _ f
    | S n' => fun x f => Ps f
    end.

  Definition bnat_Srect (n: nat) (nb: bnat (S n)): P nb
    := bnat_rect R Pz RS nb.

End alt_rect.

Lemma bnat_cases n (x: bnat (S n)): { p | x = bS p } + { x = bO n }.
  revert n x.
  apply bnat_Srect; [right | left; exists b]; reflexivity.
Defined.

Lemma bnat_0: bnat 0 -> False.
Proof with auto.
  cut (forall n, bnat n -> n <> 0%nat).
    intros H H0. apply (H _ H0)...
  induction 1; intro; discriminate.
Qed.

Require Import List list_util.

Definition bnat_bound n (b: bnat n): nat := n.

Definition pred n (b: bnat n): option (bnat (Peano.pred (bnat_bound b))) :=
  match b return option (bnat (Peano.pred (bnat_bound b))) with
  | bO _ => None
  | bS x y => Some y
  end.

Require Import util.

Lemma eq_bS_inv n (x y: bnat n): bS x = bS y -> x = y.
Proof with auto.
  intros.
  apply option_eq_inv.
  replace (Some x) with (pred (bS x))...
  replace (Some y) with (pred (bS y))...
  rewrite H...
Qed.

Require Import EquivDec.

Instance bnat_eq_dec n: EqDec (bnat n) eq.
  induction n.
    repeat intro.
    elimtype False.
    apply (bnat_0 x).
  repeat intro.
  destruct (bnat_cases x) as [[x' e] | e];
   destruct (bnat_cases y) as [[y' e'] | e']; subst.
        destruct (IHn x' y'); [left | right].
          rewrite e. reflexivity.
        exact (fun H => c (eq_bS_inv H)).
      right. discriminate.
    right. discriminate.
  left. reflexivity.
Defined.

Definition all_bnats := fix F (n: nat): list (bnat n) :=
  match n with
  | O => nil
  | S m => bO m :: map (@bS m) (F m)
  end.

Instance bnats n: ExhaustiveList (bnat n) := { exhaustive_list := all_bnats n }.
Proof with auto.
  dependent induction n; intro x.
    elimtype False. apply bnat_0...
  destruct (bnat_cases x) as [[p e] | e]; subst; [right | left]...
Defined.

Lemma NoDup_bnats n: NoDup (bnats n).
Proof with auto.
  induction n.
    apply NoDup_nil.
  simpl.
  apply NoDup_cons...
    intro.
    destruct (fst (in_map_iff (@bS n) (all_bnats n) (bO n)) H).
    destruct H0.
    discriminate.
  apply NoDup_map...
  intros. apply eq_bS_inv...
Qed.
