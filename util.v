Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import List.
Require Import Bool.
Require Export Program.
Set Implicit Arguments.
Open Local Scope R_scope.

Ltac hyp := assumption.
Ltac ref := reflexivity.
Ltac destruct_and :=
  match goal with
  | H: _ /\ _ |- _ => destruct H; destruct_and
  | _ => idtac
  end.

Definition decision (P: Prop): Set := { P } + { ~ P }.

Definition decision_to_bool P (dec : decision P) : bool :=
  match dec with
  | left _ => true
  | right _ => false
  end.

Ltac dec_eq := unfold decision; decide equality.

Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].

Notation "g ∘ f" := (compose g f) (at level 40, left associativity).

Definition uncurry A B C (f: A -> B -> C) (ab: A * B): C := f (fst ab) (snd ab).
Definition curry A B C (f: A * B -> C) (a: A) (b: B): C := f (a, b).

Definition conj_pair {A B: Prop} (P: A /\ B): A * B :=
  match P with conj a b => (a, b) end.

Coercion conj_pair: and >-> prod.

Definition opt_neg_conj (A B: Prop)
  (oa: option (~ A)) (ob: option (~ B)): option (~ (A /\ B)) :=
    match oa, ob with
    | Some na, _ => Some (na ∘ fst ∘ conj_pair)
    | _, Some nb => Some (nb ∘ snd ∘ conj_pair)
    | None, None => None
    end.

Definition opt_neg_impl (P Q: Prop) (i: P -> Q):
  option (~ Q) -> option (~ P) :=
    option_map (fun x => x ∘ i).

Definition pair_eq_dec (X Y: Type)
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
Proof. unfold decision. tauto. Defined.

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

Coercion unsumbool (A B: Prop) (sb: {A}+{B}): bool :=
  if sb then true else false.

Lemma Rmax_le x y z: x <= z -> y <= z -> Rmax x y <= z.
Proof with auto.
  intros. unfold Rmax. destruct (Rle_dec x y)...
Qed.

Lemma Rmin_le x y z: z <= x -> z <= y -> z <= Rmin x y.
Proof with auto.
  intros. unfold Rmin. destruct (Rle_dec x y)...
Qed.

Definition option_eq_dec A (Adec: forall a a': A, decision (a = a'))
  (o o': option A): decision (o = o').
Proof with auto.
  intros.
  destruct o; destruct o'...
      destruct (Adec a a0).
        subst...
      right. intro. inversion H...
    right. intro. discriminate.
  right. intro. discriminate.
Defined.

Coercion opt_to_bool A (o: option A): bool :=
  match o with Some _ => true | None => false end.

Definition opt {A R}: (A -> R) -> R -> option A -> R :=
  option_rect (fun _ => R).

Definition flip_opt {A R} (r: R) (o: option A) (f: A -> R): R :=
  option_rect (fun _ => R) f r o.

Definition opt_prop A (o: option A) (f: A -> Prop): Prop :=
  match o with
  | None => True
  | Some v => f v
  end.

Definition options A (x y: option A): option A :=
  match x, y with
  | Some a, _ => Some a
  | _, Some a => Some a
  | None, None => None
  end.

Lemma unsumbool_true (P Q: Prop) (sb: {P}+{Q}): unsumbool sb = true -> P.
Proof. destruct sb. auto. intro. discriminate. Qed.
Lemma decision_true (P: Prop) (sb: decision P): unsumbool sb = true -> P.
Proof. destruct sb. auto. intro. discriminate. Qed.
Lemma decision_false (P: Prop) (sb: decision P): unsumbool sb = false -> ~P.
Proof. destruct sb. intro. discriminate. auto. Qed.
Lemma semidec_true (P: Prop) (o: option P): opt_to_bool o = true -> P.
Proof. destruct o. auto. intro. discriminate. Qed.

Lemma show_unsumbool A (b: decision A) (c: bool): (if c then A else ~A) -> unsumbool b = c.
Proof. destruct b; destruct c; intuition. Qed.

Class ExhaustiveList (T: Type): Type :=
  { exhaustive_list: list T
  ; list_exhaustive: forall x, In x exhaustive_list }.

Hint Resolve @list_exhaustive.
Coercion exhaustive_list: ExhaustiveList >-> list.

Hint Resolve in_map.

Lemma negb_inv b c: b = negb c -> negb b = c.
Proof. intros. subst. apply negb_involutive. Qed.

Definition prod_map A B C D (f: A -> B) (g: C -> D) (p: A*C): B*D :=
  (f (fst p), g (snd p)).

Definition flip (A B C: Type) (f: A -> B -> C) (b: B) (a: A): C := f a b.

Hint Extern 4 => match goal with
  |- ?P (@proj1_sig ?T ?P ?x) => destruct x; auto
  end.

Definition overestimation (P: Prop): Set := { b: bool | b = false -> ~ P }.

Coercion overestimation_bool P: overestimation P -> bool := @proj1_sig _ _.

Program Definition opt_overestimation (A: Type) (P: A -> Prop)
  (H: forall a, overestimation (P a)) (o: option A): overestimation (opt_prop o P) :=
  match o with
  | None => true
  | Some v => H v
  end.

Program Definition overestimate_conj (P Q: Prop)
  (x: overestimation P) (y: overestimation Q): overestimation (P /\ Q) := x && y.
Next Obligation.
  intros [A B].
  destruct x. destruct y.
  simpl in H.
  destruct (andb_false_elim _ _ H); intuition.
Qed.

Lemma overestimation_false P (o: overestimation P): (o: bool) = false -> ~ P.
Proof. destruct o. assumption. Qed.

Lemma overestimation_true P (o: overestimation P): P -> (o: bool) = true.
Proof. destruct o. destruct x. reflexivity. intros. absurd P; auto. Qed.

Program Definition weaken_decision (P: Prop) (d: decision P):
  overestimation P := d: bool.
Next Obligation. destruct d; firstorder. Qed.
