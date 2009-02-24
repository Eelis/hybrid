Require Import List.
Require Import Bool.
Require Import util.
Require Import list_util.
Require c_abstract.
Require Import reachability.
Require digraph.
Set Implicit Arguments.

Section using_duplication.

  Variable chs: c_concrete.System.
  Variable ahs: c_abstract.System chs.
  
  Inductive TransKind := Cont | Disc.

  Lemma TransKind_eq_dec (k k': TransKind): decision (k = k').
    unfold decision.
    destruct k; destruct k'; firstorder; right; intro; discriminate.
  Defined.

  Definition flip (k: TransKind) :=
    match k with Cont => Disc | Disc => Cont end.

  Let V := prod TransKind (c_abstract.State chs (c_abstract.Region ahs)).

  Definition vertices: list V :=
    map (pair Cont) (c_abstract.states chs (c_abstract.regions ahs)) ++
    map (pair Disc) (c_abstract.states chs (c_abstract.regions ahs)).

  Definition vertices_exhaustive: forall v, In v vertices.
    destruct v.
    apply in_or_app.
    destruct t; [left | right]; apply in_map;
      apply c_abstract.states_exhaustive;
      apply c_abstract.regions_exhaustive.
  Defined.

  Definition eq_dec :=
    pair_eq_dec TransKind_eq_dec (@c_abstract.State_eq_dec chs
     (c_abstract.Region ahs) (c_abstract.Region_eq_dec ahs)).

  Definition tr (k: TransKind) (s:
    c_abstract.State chs (c_abstract.Region ahs)):
     list (c_abstract.State chs (c_abstract.Region ahs)) :=
    match k with
    | Cont => map (pair (fst s))
      (proj1_sig (c_abstract.cont_trans _ (fst s) (snd s)))
    | Disc => proj1_sig (c_abstract.disc_trans _ (fst s) (snd s))
    end.
     
  Definition next (v: V): list V :=
    map (pair (flip (fst v))) (tr (fst v) (snd v)).

  Lemma NoDup_next v: NoDup (next v).
  Proof with auto.
    intros.
    unfold next.
    apply NoDup_map.
      intros. inversion H1...
    destruct v. simpl @fst. simpl @snd.
    unfold tr.
    destruct t.
      apply NoDup_map.
        intros. inversion H1...
      apply c_abstract.NoDup_cont_trans.
    apply c_abstract.NoDup_disc_trans.
  Qed.

  Lemma NoDup_vertices: NoDup vertices.
  Proof with auto.
    unfold vertices.
    apply NoDup_app.
      apply NoDup_map.
        intros. inversion H1...
        apply c_abstract.NoDup_states.
        apply c_abstract.NoDup_regions.
      apply NoDup_map.
      intros. inversion H1...
      apply c_abstract.NoDup_states.
      apply c_abstract.NoDup_regions.
    intros. intro.
    destruct (fst (in_map_iff _ _ x) H).
    destruct (fst (in_map_iff _ _ x) H0).
    destruct H1. destruct H2.
    destruct x.
    inversion H1. inversion H2. subst. discriminate.
  Qed.

  Definition g: digraph.DiGraph :=
    digraph.Build eq_dec vertices vertices_exhaustive next NoDup_next.
(*
  Lemma reachable_cont_disc s s':
    digraph.reachable s ((Cont, s'): digraph.Vertex g) ->
    digraph.reachable s (Disc, s').
  Proof with auto.
    intros.
    apply reachable_next with (Cont, s')...
    simpl. unfold next. simpl.
    apply in_map. apply abstract.cont_trans_refl.
  Qed.
*)
  Lemma respect (s: c_abstract.State chs (c_abstract.Region ahs)):
    c_abstract.reachable _ s ->
    exists k,
    exists v: digraph.Vertex g,
    opt_to_bool (c_abstract.initial _ (fst (snd v)) (snd (snd v))) = false /\
    digraph.reachable v (k, s).
  Proof with auto.
    intros.
    destruct H. destruct H. destruct H0.
    exists (if x0 then Disc else Cont).
    induction H0.
      exists (if b then Disc else Cont, s).
      split...
      destruct b; apply reachable_refl.
    destruct IHend_with... destruct H2.
    exists x0.
    split...
    destruct b; simpl in *.
      apply reachable_next with (Cont, y)...
      simpl. unfold next. simpl. apply in_map. 
      destruct z. destruct H1. simpl in H1. subst.
      apply in_map...
    apply reachable_next with (Disc, y)...
    simpl. unfold next. simpl. apply in_map...
  Defined.

  Lemma respect_inv (s: c_abstract.State chs (c_abstract.Region ahs)):
    (forall v: digraph.Vertex g, opt_to_bool (c_abstract.initial _ (fst (snd v)) (snd (snd v))) = false ->
     ~ digraph.reachable v (Cont, s) /\ ~ digraph.reachable v (Disc, s))
     -> ~ c_abstract.reachable _ s.
  Proof with auto.
    intros. intro.
    destruct (respect H0). destruct H1. destruct H1.
    destruct (H x0 H1). clear H.
    destruct x...
  Defined.

  Lemma semidecide_reachable (s: c_abstract.State chs (c_abstract.Region ahs)):
    option (~ c_abstract.reachable _ s).
  Proof with auto.
    intro s.
    set (start := filter (fun v => negb (opt_to_bool (c_abstract.initial _ (fst (snd v)) (snd (snd v))))) vertices).
    destruct (@digraph.reachables g start).
      apply NoDup_filter.
      apply NoDup_vertices.
    destruct (In_dec (digraph.Vertex_eq_dec g) (Cont, s) x). exact None.
    destruct (In_dec (digraph.Vertex_eq_dec g) (Disc, s) x). exact None.
    apply Some.
    apply respect_inv.
    intros.
    assert (In v start).
      apply (snd (filter_In (fun v => negb (opt_to_bool
        (c_abstract.initial chs (fst (snd v)) (snd (snd v))))) v vertices)).
      split...
        apply vertices_exhaustive.
      unfold c_abstract.State in H.
      rewrite H...
    split; intro.
      apply n.
      apply (snd (i (Cont, s))).
      exists v...
    apply n0.
    apply (snd (i (Disc, s))).
    exists v...
  Defined.

  Lemma semidecide_reachable2 (u: c_abstract.State _ (c_abstract.Region ahs)):
    option (forall s, c_abstract.abs ahs s = u -> ~ c_concrete.reachable s).
  Proof with auto.
    intros.
    refine (option_map _ (semidecide_reachable u)).
    repeat intro.
    apply H.
    subst. apply c_abstract.reachable_concrete_abstract...
  Defined.

End using_duplication.
