
Require Import CRreal Classic util.

(* Doubly-negated types as a monad: *)

Definition DN (T: Type): Prop := (T -> False) -> False.

Hint Unfold DN.

Definition DN_return {T: Type}: T -> DN T.
Proof. firstorder. Qed.

Definition DN_bind {A: Type}: DN A -> forall B, (A -> DN B) -> DN B.
Proof. firstorder. Qed.

Lemma DN_fmap {A: Type}: DN A -> forall B, (A -> B) -> DN B.
Proof. firstorder. Qed.

Inductive Stable P := mkStable: (DN P -> P) -> Stable P.
  (* Using an Inductive gets us universe polymorphism, which the following
   simpler alternative does not provide: *)

(* Definition Stable P := DN P -> P. *)

Lemma DN_apply {T: Type}: DN T -> forall P, Stable P -> (T -> P) -> P.
Proof. firstorder. Qed.

Lemma decision_stable P: decision P -> Stable P.
Proof. firstorder. Qed.

Lemma Stable_neg (P: Prop): Stable (~P).
Proof. firstorder. Qed.

Lemma Stable_False: Stable False.
Proof. firstorder. Qed.

Hint Immediate Stable_False.

Lemma Qle_dec x y: decision (Qle x y).
  intros.
  destruct (Qlt_le_dec y x); [right | left]; [apply Qlt_not_le |]; assumption.
Defined.
  (* Todo: Don't I have this elsewhere? *)

Lemma CRnonNeg_stable x: Stable (CRnonNeg x).
Proof with auto.
  unfold CRnonNeg.
  intros.
  constructor.
  intros.
  destruct (Qle_dec (-e) (approximate x e))...
  elimtype False...
Qed.

Hint Resolve CRnonNeg_stable.

Lemma CRle_stable (x y: CR): Stable (CRle x y).
Proof. unfold CRle. auto. Qed.

Hint Resolve CRle_stable.

Lemma stable_conjunction (A B: Prop): Stable A -> Stable B -> Stable (A /\ B).
Proof. firstorder. Qed.

Hint Resolve stable_conjunction.

Open Local Scope CR_scope.

Lemma DN_or P Q: Not ((Not P) /\ (Not Q)) -> DN (P + Q).
Proof. firstorder. Qed.

Lemma CRle_cases (x y: CR): x <= y -> DN ((x == y) + (x < y)).
Proof with auto.
  intros.
  apply (@DN_or (x == y) (x < y)).
  intros [A B].
  apply (leEq_less_or_equal _ _ _ H).
  intro. intuition.
Qed.

Lemma CRle_dec x y: DN ((x <= y) + (y <= x)).
  intros.
  apply (@DN_or (x <= y) (y <= x)).
  intros [A B].
  apply (leEq_or_leEq CRasCOrdField x y).
  intro. intuition.
Qed.

Lemma CR_trichotomy x y: DN ((x == y) + (x < y) + (y < x)).
Proof with auto.
  intros.
  apply (DN_bind (CRle_dec x y)).
  intros [P|P]; apply (DN_bind (CRle_cases _ _ P));
    intros [A|B]; apply DN_return; intuition.
Qed.
