Require Import List.
Require Import util.
Require Import Le.
Require Import Lt.
Set Implicit Arguments.

Section with_eq_dec.

Variables (X: Type) (Xeq: forall x x': X, decision (x = x')).

Lemma remove_incl
  (x: X) (l: list X): incl (remove Xeq x l) l.
Proof with auto.
  induction l; simpl.
    apply incl_refl.
  destruct (Xeq x a).
    apply incl_tl...
  do 2 intro. destruct H.
    subst. left...
  right...
Qed.

Lemma remove_length_le (x: X) (l: list X): length (remove Xeq x l) <= length l.
Proof with auto.
  induction l...
  simpl.
  destruct (Xeq x a)...
  apply le_n_S...
Qed.

Lemma remove_length_lt (x: X) (l: list X): In x l ->
    length (remove Xeq x l) < length l.
Proof with auto.
  induction l; intros.
    inversion H.
  simpl.
  destruct (Xeq x a).
    apply le_n_S.
    apply remove_length_le.
  destruct H. elimtype False...
  apply lt_n_S...
Qed.

Definition intersection (a: list X): list X -> list X :=
  filter (fun e => unsumbool (In_dec Xeq e a)).

Definition subtr: list X -> list X -> list X := fold_right (remove Xeq).
    (* removes elements in latter list from former list *)

Lemma remove_eq_filter (x: X) (l: list X):
  remove Xeq x l = filter (fun y => negb (unsumbool (Xeq x y))) l.
Proof with auto.
  induction l...
  simpl.
  destruct (Xeq x a)...
  simpl. rewrite IHl...
Qed.

Definition In_remove (l: list X) (x y: X): (In x l /\ y <> x) <-> In x (remove Xeq y l).
Proof with auto.
  intros.
  rewrite remove_eq_filter.
  destruct (filter_In (fun y0 : X => negb (unsumbool (Xeq y y0))) x l).
  split; intro.
    apply H0. destruct H1.
    destruct (Xeq y x)...
  destruct (H H1).
  destruct (Xeq y x)...
  discriminate.
Qed.

Definition In_remove' (l: list X) (x y: X): In x l -> y <> x -> In x (remove Xeq y l).
  (* redundant, but easier to apply and use as hint. *)
Proof. intros. apply (In_remove l x y); auto. Qed.

Lemma incl_filter (p: X -> bool) (l: list X): incl (filter p l) l.
Proof with auto.
  unfold incl.
  induction l; simpl...
  intros.
  destruct (p a); firstorder.
Qed.

Definition incl_remove (l: list X) (x: X): incl (remove Xeq x l) l.
Proof. intros. rewrite remove_eq_filter. apply incl_filter. Qed.

Lemma In_subtr a b x: In x (subtr a b) -> (In x a /\ ~ In x b).
Proof with auto.
  induction b...
  simpl.
  rewrite remove_eq_filter.
  intros.
  destruct (fst (filter_In _ x (subtr a b)) H).
  destruct (IHb _ H0).
  split...
  intro.
  destruct H4...
  subst.
  destruct (Xeq x x)...
  discriminate.
Qed.

Lemma subtr_In a b x: In x a -> ~ In x b -> In x (subtr a b).
Proof with auto.
  induction b...
  simpl. intros.
  apply (In_remove (subtr a b) x a0).
  split...
Qed.

Lemma incl_subtr a b: incl (subtr a b) a.
Proof with auto.
  induction b.
    simpl. apply incl_refl.
  simpl.
  apply incl_tran with (subtr a b)...
  apply incl_remove.
Qed.

Lemma intersection_In' (x: X) a b:
  In x a -> In x b -> In x (intersection a b).
Proof with auto.
  unfold intersection.
  intros.
  apply (filter_In (fun e : X => unsumbool (In_dec Xeq e a)) x b).
  destruct (In_dec Xeq x a)...
Qed.

Lemma intersection_In (x: X) a b:
  In x (intersection a b) -> (In x a /\ In x b).
Proof with auto.
  induction a...
    unfold intersection.
    simpl.
    intros.
    destruct (filter_In (fun _ => false) x b).
    destruct (H0 H). discriminate.
  unfold intersection in *.
  intros.
  destruct (filter_In (fun e : X => unsumbool (In_dec Xeq e (a :: a0))) x b).
  set (H0 H). clearbody a1. clear H0 H H1.
  destruct a1.
  destruct (In_dec Xeq x (a :: a0))...
  discriminate.
Qed.

Lemma incl_intersection_left (a b c: list X):
  incl a c -> incl (intersection a b) c.
Proof with auto.
  repeat intro.
  destruct (intersection_In a0 a b H0)...
Qed.

Lemma NoDup_map (A B: Type) (f: A -> B) l:
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof with simpl; auto.
  induction l...
    intros.
    apply NoDup_nil.
  intros.
  simpl.
  inversion_clear H0.
  apply NoDup_cons...
  intro.
  apply H1.
  destruct (fst (in_map_iff f l (f a)) H0).
  destruct H3.
  rewrite H with a x...
Qed.

Lemma NoDup_filter (p: X -> bool) (l: list X):
  NoDup l -> NoDup (filter p l).
Proof with auto.
  induction l...
  simpl.
  intros.
  inversion_clear H.
  destruct (p a)...
  apply NoDup_cons...
  intro.
  apply H0...
  apply (incl_filter p l)...
Qed.

Lemma NoDup_intersection_right a b: NoDup b -> NoDup (intersection a b).
Proof with auto.
  unfold intersection.
  intros.
  apply NoDup_filter...
Qed.

Lemma not_In_filter (x: X) p l: ~ In x (filter p l) ->
  In x l -> p x = false.
Proof with auto.
  induction l.
    simpl.
    intros.
    elimtype False...
  simpl.
  intros.
  destruct H0.
    subst.
    case_eq (p x)...
    intros.
    rewrite H0 in H.
    elimtype False.
    apply H. left...
  apply IHl...
  destruct (p a)...
  intro. apply H. right...
Qed.

Lemma not_In_filter' (x: X) p l: ~ In x (filter p l) ->
  (~ In x l \/ p x = false).
Proof with auto.
  intros.
  destruct (In_dec Xeq x l).
    right. apply not_In_filter with l...
  left...
Qed.

Lemma not_in_app (x: X) a b: ~ In x (a ++ b) -> ~ In x a \/ ~ In x b.
Proof with auto.
  induction a...
  simpl.
  intros.
  firstorder.
Qed.

Lemma NoDup_app (a b: list X): NoDup a -> NoDup b ->
  (forall x, In x a -> ~ In x b) -> NoDup (a ++ b).
Proof with auto.
  induction a...
  intros.
  simpl.
  inversion_clear H.
  apply NoDup_cons.
    intro.
    destruct (in_app_or _ _ _ H)...
    apply (H1 a)...
    left...
  apply IHa...
  intros. apply H1. right...
Qed.

Lemma NoDup_subtr a b: NoDup a -> NoDup (subtr a b).
Proof with auto.
  induction b...
  simpl. intros.
  rewrite remove_eq_filter.
  apply NoDup_filter...
Qed.

Lemma NoDup_remove a: NoDup a -> forall b, NoDup (remove Xeq b a).
Proof.
  intros.
  rewrite remove_eq_filter.
  apply NoDup_filter.
  assumption.
Qed.

Definition NoDup_dec (l: list X): decision (NoDup l).
Proof with auto.
  induction l.
    left. apply NoDup_nil.
  destruct IHl.
    destruct (In_dec Xeq a l).
      right.
      intro.
      inversion H. apply (H2 i).
    left. apply NoDup_cons; assumption.
  right. intro. apply n. inversion H...
Defined.

End with_eq_dec.

Lemma NoDup_flat_map (A B: Type) (f: A -> list B) l:
  (forall x a b, In a l -> In b l -> In x (f a) -> In x (f b)
    -> a = b) ->
  (forall x, In x l -> NoDup (f x)) ->
  NoDup l -> NoDup (flat_map f l).
Proof with simpl; auto.
  induction l; simpl; intros.
    apply NoDup_nil.
  inversion_clear H1...
  apply NoDup_app...
    apply IHl...
    intros.
    apply H with x...
  intros. intro.
  destruct (fst (in_flat_map f l x) H4).
  destruct H5.
  apply H2.
  rewrite <- (H x x0 a )...
Qed.

Hint Resolve NoDup_subtr.
Hint Resolve NoDup_filter.
Hint Resolve NoDup_remove.
Hint Resolve NoDup_intersection_right.
Hint Resolve subtr_In.
Hint Resolve In_remove'.
Hint Resolve in_or_app.
Hint Resolve intersection_In'.
Hint Resolve in_eq.
Hint Resolve in_cons.
Hint Resolve NoDup_cons.
Hint Resolve NoDup_nil.

Lemma in_filter (A : Type) (f : A -> bool) (x : A) (l : list A) :
  In x l -> f x = true -> In x (filter f l).
Proof.
  intros. destruct filter_In with A f x l. firstorder.
Qed.

Lemma existsb_forall : 
  forall A (l : list A) P x, 
    existsb P l = false -> In x l -> P x = false.
Proof.
  induction l; intros.
  contradiction.
  destruct (Bool.orb_false_elim _ _ H).
  destruct H0.
  subst. hyp.
  apply IHl; hyp.
Qed.  

Lemma filter_app (A : Type) (f : A -> bool) ls ls' :
  filter f ls ++ filter f ls' =
  filter f (ls ++ ls').
Proof.
  induction ls. ref. intros.
  simpl. destruct (f a); simpl. rewrite IHls. ref. apply IHls.
Qed.

Section ExhaustivePairList.

  Context {A B} {EA: ExhaustiveList A} {EB: ExhaustiveList B}.

  Instance ExhaustivePairList:
     ExhaustiveList (A*B)
      := { exhaustive_list := flat_map (fun i => map (pair i) EB) EA }.
  Proof.
    intros [a b].
    destruct (in_flat_map (fun i => map (pair i) EB) EA (a, b)).
    eauto.
  Defined.

  Lemma NoDup_ExhaustivePairList:
    NoDup EA -> NoDup EB -> NoDup ExhaustivePairList.
  Proof with auto.
    intros H H0.
    simpl.
    apply NoDup_flat_map; intros...
      destruct (fst (in_map_iff (pair a) EB x) H3) as [x0 [C D]].
      destruct (fst (in_map_iff (pair b) EB x) H4) as [x1 [E F]].
      subst. inversion E...
    apply NoDup_map...
    intros. inversion H4...
  Qed.

End ExhaustivePairList.
Existing Instance ExhaustivePairList.
  (* No idea why this is necessary... *)

Instance decide_exists_in `{forall x: T, decision (P x)} l: decision (exists x, In x l /\ P x).
Proof.
  repeat intro.
  case_eq (existsb H l); intro.
    left.
    destruct (fst (existsb_exists _ _) H0).
    exists x.
    destruct H1.
    split. assumption.
    apply (decision_true _ H2).
  right.
  intros [x [H1 H2]].
  exact (decision_false _ (existsb_forall l H x H0 H1) H2).
Defined.

Instance decide_exists `{ExhaustiveList T} `{forall x: T, decision (P x)}: decision (exists x, P x).
Proof.
  intros. destruct (decide_exists_in H); [left | right]; firstorder.
Defined.

Instance In_decision `{EquivDec.EqDec T eq} (x: T) y: decision (In x y) := In_dec EquivDec.equiv_dec x y.
