Require Import List.
Require Import c_util util list_util.
Require Import CSetoids CRreal.
Require Import flow.
Require concrete abstract.
Set Implicit Arguments.
Open Local Scope CR_scope.
Require Import EquivDec.

Section contents.

  Variable (chs: concrete.System) (ap: abstract.Parameters chs).

  Let Location := concrete.Location chs.
  Let Point := concrete.Point chs.
  Let c_State := concrete.State chs.

  Let State := (Location * abstract.Region ap)%type.

  Definition cont_trans_cond (l: Location) (r1 r2: abstract.Region ap): Prop :=
      exists p, exists q,
        abstract.in_region ap p r1 /\ abstract.in_region ap q r2 /\ concrete.cont_trans (l, p) (l, q).

  Definition disc_trans_cond (s : State * State): Prop :=
    let (s1, s2) := s in
    let (l1, r1) := s1 in
    let (l2, r2) := s2 in
      exists p, exists q,
        abstract.in_region ap p r1 /\ abstract.in_region ap q r2 /\ concrete.disc_trans (l1, p) (l2, q).

  Definition Hint (l: Location) (r r': abstract.Region ap): Set :=
    forall p, abstract.in_region ap p r ->
      forall t, '0 <= t -> abstract.in_region ap (concrete.flow chs l p t) r' ->
        abstract.in_region ap (concrete.flow chs l p t) r.

  Definition AltHint (l: Location) (r r': abstract.Region ap): Set :=
    (forall p: Point,
      abstract.in_region ap p r ->
      forall t: Time,
      abstract.in_region ap (concrete.flow chs l p t) r' -> t <= '0).

  Lemma dealt_hint l r r': AltHint l r r' -> Hint l r r'.
  Proof with eauto.
    repeat intro.
    assert (t [=] '0). apply (CRle_def t ('0))...
    rewrite H3, flow_zero...
  Qed.

  Variable hints: forall (l: Location) (r r': abstract.Region ap), r <> r' -> option (Hint l r r').

  Definition dealt_hints (H: forall l r r', r <> r' -> option (AltHint l r r')) l r r' (E: r <> r'): option (Hint l r r') :=
    option_map (@dealt_hint l r r') (H l r r' E).

  Definition hints' (l: Location) (r r': abstract.Region ap):
    option (forall p, abstract.in_region ap p r ->
     forall t, '0 <= t -> abstract.in_region ap (concrete.flow chs l p t) r' ->
       abstract.in_region ap (concrete.flow chs l p t) r) :=
    match r == r' with
    | left _ => None
    | right E => hints l E
    end.

  Variable cont_dec: forall l r r', overestimation (cont_trans_cond l r r').

  (* Using these, we can define the abstract transitions.. *)

  Let cont_trans_b (s : State) (r_dst : abstract.Region ap) : bool :=
    let (l, r_src) := s in
    cont_dec l r_src r_dst &&
    negb (hints' l r_src r_dst).

  Definition raw_cont_trans (s : State) : list (abstract.Region ap) :=
    filter (cont_trans_b s) (abstract.regions ap).

  Lemma cont_refl l r p: abstract.in_region ap p r -> concrete.invariant (l, p) ->
    In r (raw_cont_trans (l, r)).
  Proof with auto.
    intros.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply overestimation_true.
      simpl.
      exists p. exists p.
      repeat split...
      unfold concrete.can_flow.
      exists NonNegCR_zero.
      split.
        intros.
        simpl.
        rewrite (curry_eq concrete.invariant).
        assert ('0 [=] t). apply (snd (CRle_def ('0) t))...
        rewrite <- H3.
        rewrite flow_zero...
      simpl.
      rewrite flow_zero...
    simpl.
    unfold hints'.
    destruct (equiv_dec r r)...
    elimtype False.
    intuition.
  Qed.

  Lemma respects_cont l s1 s2 :
    concrete.can_flow _ l s1 s2 ->
    forall r1, abstract.in_region ap s1 r1 ->
    exists r2, abstract.in_region ap s2 r2 /\ In r2 (raw_cont_trans (l, r1)).
  Proof with auto with real.
    intros l p p' [t [inv f]] r rin.
    assert (concrete.invariant (l, p')).
      rewrite (curry_eq concrete.invariant).
      rewrite <- f.
      apply inv...
      apply -> CRnonNeg_le_zero...
    destruct (abstract.select_region ap l p' H) as [r' rin'].
    case_eq (hints' l r r'); intros.
      exists r.
      split.
        rewrite <- f.
        apply i...
          apply -> CRnonNeg_le_zero...
        rewrite f...
      apply cont_refl with p...
      rewrite (curry_eq concrete.invariant).
      rewrite <- (flow_zero (concrete.flow chs l) p).
      apply inv...
      apply -> CRnonNeg_le_zero...
    exists r'.
    split...
    unfold raw_cont_trans.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply overestimation_true.
      exists p.
      eauto 10.
    rewrite H0...
  Qed.

  Program Definition cont_trans (s : State): sig
    (fun l: list (abstract.Region ap) => LazyProp (NoDup l /\ abstract.ContRespect ap s l)) :=
    filter (cont_trans_b s) (abstract.regions ap).
  Next Obligation. Proof with auto.
    split.
      apply NoDup_filter, (abstract.NoDup_regions ap).
    repeat intro.
    destruct (respects_cont H1 _ H0).
    destruct H2.
    exists x.
    split...
    unfold raw_cont_trans in H3.
    destruct s...
  Qed.

End contents.
