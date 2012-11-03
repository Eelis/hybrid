Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import List.
Require Import Bool.
Require Export Program.
Require Import EquivDec.
Require Import Relation_Definitions.
Require Import Morphisms.

Set Implicit Arguments.
Open Local Scope R_scope.

Ltac hyp := assumption.
Ltac ref := reflexivity.
Ltac destruct_and :=
  match goal with
  | H: _ /\ _ |- _ => destruct H; destruct_and
  | _ => idtac
  end.

Section predicate_reflection.

  Inductive PredicateType: Type -> Type :=
    | PT_Prop: PredicateType Prop
    | PT_pred X (T: X -> Type): (forall x, PredicateType (T x)) ->
      PredicateType (forall x: X, T x).

  (* We would really like PredicateType to be a type class, but unfortunately
   we cannot make it one with the way type classes currently work. Hence,
   we introduce the following: *)

  Class IsPredicateType (T: Type): Type := is_PT: PredicateType T.

  Instance PT_Prop_instance: IsPredicateType Prop := PT_Prop.
  Instance PT_pred_instance (X: Type) (T: X -> Type) (U: forall x, IsPredicateType (T x)):
    IsPredicateType (forall x: X, T x) := PT_pred T U.

  Variables
     (F: forall T: Type, T -> Type)
     (A: forall P: Prop, F P)
     (B: forall (U: Type) (R: U -> Type) (p: forall u, R u)
            (i: forall u, PredicateType (R u)), (forall u, F (p u)) -> F p).

  Definition pred_rect (T: Type) (i: IsPredicateType T) (t: T): F t.
  Proof.
    induction i.
      apply A.
    exact (B T t p (fun u => X0 u (t u))).
  Defined.

End predicate_reflection.

Existing Instance PT_Prop_instance.
Existing Instance PT_pred_instance.

Class decision (P: Prop): Set := decide: { P } + { ~ P }.

Program Instance decide_conjunction {P Q: Prop} `{Pd: decision P} `{Qd: decision Q}: decision (P /\ Q) :=
  match Pd, Qd with
  | right _, _ => right _
  | _, right _ => right _
  | left _, left _ => left _
  end.

Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Instance decide_equality {A} {R: relation A} `{e: EqDec A R} x y: decision (R x y) := e x y.

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

Definition curry_eq A B C (f: A * B -> C) a b: f (a, b) = curry f a b := refl_equal _.

Definition conj_pair {A B: Prop} (P: A /\ B): A * B :=
  match P with conj a b => (a, b) end.

Coercion conj_pair: and >-> prod.

Definition equivalent_decision (P Q: Prop) (PQ: P <-> Q) (d: decision P): decision Q :=
  match d with
  | left p => left (fst PQ p)
  | right H => right (fun q => H (snd PQ q))
  end.

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
Proof. unfold decision. destruct Pdec, Qdec; firstorder. Defined.

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

Instance option_eq_dec {B: Type} `(Bdec: EquivDec.EqDec B eq): EquivDec.EqDec (option B) eq.
Proof with auto.
  intros o o'.
  unfold Equivalence.equiv.
  destruct o; destruct o'...
    destruct (Bdec b b0).
     unfold Equivalence.equiv in *.
     subst...
    right. intro. inversion H...
   right. discriminate.
  right. discriminate.
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

Lemma option_eq_inv A (x y: A): Some x = Some y -> x = y.
  intros.
  inversion H.
  reflexivity.
Defined.

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

Definition dep_flip (A B: Type) (C: A -> B -> Type) (f: forall a b, C a b) (b: B) (a: A): C a b := f a b.

Hint Extern 4 => match goal with
  |- ?P (@proj1_sig ?T ?P ?x) => destruct x; auto
  end.

Class overestimation (P: Prop): Set := overestimate: { b: bool | b = false -> ~ P }.
Definition underestimation (P: Prop): Set := option P.

Coercion overestimation_bool P: overestimation P -> bool := @proj1_sig _ _.
Coercion underestimation_bool P: underestimation P -> bool := @opt_to_bool _.

Program Instance opt_overestimation {A: Type} (P: A -> Prop)
  (H: forall a, overestimation (P a)) (o: option A): overestimation (opt_prop o P) :=
  match o with
  | None => true
  | Some v => H v
  end.

Program Instance overestimate_conj {P Q: Prop}
  (x: overestimation P) (y: overestimation Q): overestimation (P /\ Q) := x && y.
Next Obligation.
  intros [A B].
  destruct x. destruct y.
  simpl in H.
  destruct (andb_false_elim _ _ H); intuition.
Qed.

Lemma overestimation_false P (o: overestimation P): (o: bool) = false -> ~ P.
Proof. destruct o. assumption. Qed.

Lemma underestimation_true P (o: underestimation P): (o: bool) = true -> P.
Proof. destruct o. intro. assumption. intro. discriminate. Qed.

Lemma overestimation_true P (o: overestimation P): P -> (o: bool) = true.
Proof. destruct o. destruct x. reflexivity. intros. absurd P; auto. Qed.

Section doers.

  Context {T: Type} `{ipt: IsPredicateType T}.

  Definition overestimator: T -> Type :=
    pred_rect (fun _ _ => Type) overestimation (fun U R p i X => forall x, X x) ipt.

  Definition underestimator: T -> Type :=
    pred_rect (fun _ _ => Type) underestimation (fun U R p i X => forall x, X x) ipt.

  Definition decider: T -> Type :=
    pred_rect (fun _ _ => Type) decision (fun U R p i X => forall x, X x) ipt.

End doers.

Program Coercion decision_overestimation (P: Prop) (d: decision P): overestimation P := d: bool.
Next Obligation. destruct d; firstorder. Qed.
  (* todo: rename, because we can do the same for underestimation *)

Definition decider_to_overestimator {T: Type} `{ipt: IsPredicateType T} (P: T): decider P -> overestimator P.
  unfold decider, overestimator.
  unfold IsPredicateType in ipt.
  unfold pred_rect.
  induction ipt; simpl.
    apply decision_overestimation.
  intuition.
Defined.

Coercion decider_to_overestimator: decider >-> overestimator.

Definition LazyProp (T: Prop): Prop := () -> T.
Definition force (T: Prop) (l: LazyProp T): T := l ().

Hint Constructors unit.

Require Import Ensembles.

Implicit Arguments Complement [U].

Definition overlap X (A B: Ensembles.Ensemble X): Prop := exists x, A x /\ B x.

Require Import EqdepFacts.
Require Import Eqdep_dec.

Section eq_dep.

Variables (U : Type) (eq_dec : forall x y : U, {x=y}+{~x=y}).

Lemma eq_rect_eq : forall (p : U) Q x h, x = eq_rect p Q x p h.

Proof.
exact (eq_rect_eq_dec eq_dec).
Qed.

Lemma eq_dep_eq : forall P (p : U) x y, eq_dep U P p x p y -> x = y.

Proof.
exact (eq_rect_eq__eq_dep_eq U eq_rect_eq).
Qed.

End eq_dep.

Definition proj1_sig_relation (T: Type) (P: T -> Prop) (R: relation T): relation (sig P) :=
  fun x y => R (`x) (`y).

Definition product_conj_relation (T T': Type) (R: relation T) (R': relation T'): relation (T * T') :=
  fun p p' => R (fst p) (fst p') /\ R' (snd p) (snd p').

Definition morpher A B: relation (A -> B) -> Type := @sig _ ∘ Proper.
  (* A more general version would be:
    Definition morpher A: relation A -> Type := @sig _ ∘ Morphism.
  However, we need the hard-coded implication to be able to declare the
  coercion below. *)

Let morpher_to_func A B (R: relation (A -> B)): morpher R -> (A -> B) := @proj1_sig _ _.
Coercion morpher_to_func: morpher >-> Funclass.

Instance morpher_morphism A B (R: relation (A -> B)) (f: morpher R):
  Proper R f := proj2_sig f.

Ltac prove_NoDup := simpl;
  match goal with
  | |- NoDup [] => constructor 1
  | |- NoDup _ => constructor 2; [vm_compute; intuition; discriminate | prove_NoDup ]
  end.

Ltac prove_exhaustive_list :=
  destruct 0; vm_compute; tauto.

Definition decision_decider_to_EqDec X (R: relation X) (e: Equivalence R)
  (d: forall x y, decision (R x y)): EquivDec.EqDec X R := d.
Ltac equiv_dec := apply decision_decider_to_EqDec; dec_eq.

Instance bools: ExhaustiveList bool := { exhaustive_list := true :: false :: [] }.
Proof. prove_exhaustive_list. Defined.

Lemma NoDup_bools: NoDup bools.
Proof. prove_NoDup. Qed.

Instance Bool_eq_dec: EquivDec.EqDec bool eq := bool_dec.

Module trans_refl_closure.
Section contents.

  Variables (T: Type) (TR: relation T).

  Inductive R: relation T :=
    | refl' s: R s s
    | step a b c: R a b -> TR b c -> R a c.

  Hint Constructors R.

  Instance trans: Transitive R.
  Proof. repeat intro. induction H0; eauto. Qed.

  Lemma flip (P: T -> Prop) (Pdec: forall s, decision (P s))
   (a b: T): R a b -> P a -> ~ P b ->
    exists c, exists d, P c /\ ~ P d /\ TR c d.
  Proof.
    intros r.
    induction r. firstorder.
    destruct (Pdec b); eauto.
  Qed.

  Lemma flip_inv (P: T -> Prop) (Pdec: forall s, decision (P s))
   (a b: T): R a b -> ~ P a -> P b ->
    exists c, exists d, ~ P c /\ P d /\ TR c d.
  Proof.
    intros r.
    induction r. firstorder.
    destruct (Pdec b); eauto.
  Qed.

End contents.
End trans_refl_closure.

Hint Constructors trans_refl_closure.R.

Section alternate.

  Variables (T: Type) (R: bool -> relation T).

  Inductive end_with: bool -> relation T :=
    | end_with_refl b s: end_with b s s
    | end_with_next b x y:
        end_with (negb b) x y -> forall z, R b y z -> end_with b x z.

  Definition alternate: relation T :=
    fun s s' => exists b, end_with b s s'.

End alternate.

Hint Constructors end_with.

Notation "[= e =]" := (exist _ e _).
