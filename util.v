Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import List.
Require Export Program.
Set Implicit Arguments.
Open Local Scope R_scope.

Definition decision (P: Prop): Set := { P } + { ~ P }.
Definition weak_decider T (P: T -> Prop) :=
  forall x, option (~ P x). (* todo: move *)

Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].

Notation " g \u2218 f " := (compose g f) (at level 40, left associativity).

Record decideable_overestimator (A: Type) (Ideal: A -> Prop) :=
  { doe_pred: A -> Prop
  ; doe_dec: forall a, decision (doe_pred a)
  ; doe_correct: forall a, Ideal a -> doe_pred a
  }.

Definition conj_pair {A B: Prop} (P: A /\ B): A * B :=
  match P with conj a b => (a, b) end.

Coercion conj_pair: and >-> prod.

Definition opt_neg_conj (A B: Prop)
  (oa: option (~ A)) (ob: option (~ B)): option (~ (A /\ B)) :=
    match oa, ob with
    | Some na, _ => Some (na \u2218 fst \u2218 conj_pair)
    | _, Some nb => Some (nb \u2218 snd \u2218 conj_pair)
    | None, None => None
    end.

Definition opt_neg_impl (P Q: Prop) (i: P -> Q):
  option (~ Q) -> option (~ P) :=
    option_map (fun x => x \u2218 i).

Definition pair_eq_dec (X Y: Set)
  (X_eq_dec: forall x x': X, {x=x'}+{x<>x'})
  (Y_eq_dec: forall y y': Y, {y=y'}+{y<>y'})
    (p: prod X Y) (p': prod X Y): decision (p=p').
Proof with auto.
  destruct p. destruct p'. unfold decision.
  destruct (X_eq_dec x x0); destruct (Y_eq_dec y y0);
    subst; try auto; right; intro; inversion H...
Defined.

Hint Unfold decision.

Definition and_dec (P Q: Prop) (Pdec: decision P) (Qdec: decision Q):
  decision (P/\Q).
Proof. unfold decision. tauto. Qed.

Hint Resolve and_dec.

Definition list_dec (X: Set) (P: X -> Prop) (d: forall x, decision (P x))
  (l: list X): decision (forall x, In x l -> P x).
Proof with auto.
  induction l.
    left. intros. inversion H.
  simpl.
  destruct (d a).
    destruct IHl; [left | right]...
    intros. destruct H... subst...
  right...
Defined.

Definition unsumbool (A B: Prop) (sb: {A}+{B}): bool :=
  if sb then true else false.

Lemma Rmax_le x y z: x <= z -> y <= z -> Rmax x y <= z.
Proof with auto.
  intros. unfold Rmax. destruct (Rle_dec x y)...
Qed.

Lemma Rmin_le x y z: z <= x -> z <= y -> z <= Rmin x y.
Proof with auto.
  intros. unfold Rmin. destruct (Rle_dec x y)...
Qed.

Definition opt_to_bool A (o: option A): bool :=
  match o with Some _ => true | None => false end.

Lemma unsumbool_true (P Q: Prop) (sb: {P}+{Q}): unsumbool sb = true -> P.
Proof. destruct sb. auto. discriminate. Qed.
Lemma decision_true (P: Prop) (sb: decision P): unsumbool sb = true -> P.
Proof. destruct sb. auto. discriminate. Qed.
Lemma decision_false (P: Prop) (sb: decision P): unsumbool sb = false -> ~P.
Proof. destruct sb. discriminate. auto. Qed.
Lemma semidec_true (P: Prop) (o: option P): opt_to_bool o = true -> P.
Proof. destruct o. auto. discriminate. Qed.
