Require Import List.
Require Import Bool.
Require Import util.
Require Import list_util.
Require c_abstract.
Require Import reachability.
Require digraph.
Require Import dec_overestimator.
Set Implicit Arguments.

Section using_duplication.

  Variable chs: c_concrete.System.
  Variable ahs: c_abstract.System chs.

  Inductive TransKind := Cont | Disc.

  Lemma TransKind_eq_dec (k k': TransKind) : decision (k = k').
  Proof. dec_eq. Defined.

  Definition flip (k: TransKind) :=
    match k with Cont => Disc | Disc => Cont end.

  Let a_State := c_abstract.State chs (c_abstract.Region ahs).

  Let V := (TransKind * a_State)%type.

  Definition all_abstract_states := c_abstract.states chs (c_abstract.regions ahs).

  Definition states_to_verts (s : list a_State) := map (pair Cont) s ++ map (pair Disc) s.

  Definition vertices : list V := states_to_verts all_abstract_states.

  Definition vertices_exhaustive: forall v, In v vertices.
  Proof.
    destruct v.
    apply in_or_app.
    destruct t; [left | right]; apply in_map;
      apply c_abstract.states_exhaustive;
      apply c_abstract.regions_exhaustive.
  Qed.

  Definition eq_dec :=
    pair_eq_dec TransKind_eq_dec (@c_abstract.State_eq_dec chs
     (c_abstract.Region ahs) (c_abstract.Region_eq_dec ahs)).

  Definition tr (k : TransKind) (s: a_State) : list a_State :=
    match k with
    | Cont => 
        let (l, r) := s in
          map (pair l) (c_abstract.cont_trans _ s)
    | Disc => c_abstract.disc_trans _ s
    end.
     
  Definition next (v: V) : list V :=
    map (pair (flip (fst v))) (tr (fst v) (snd v)).

  Lemma NoDup_next v: NoDup (next v).
  Proof with auto; try congruence.
    intros. apply NoDup_map...
    destruct v. destruct a. destruct t; simpl. 
    apply NoDup_map...
    apply c_abstract.NoDup_cont_trans.
    apply c_abstract.NoDup_disc_trans.
  Qed.

  Lemma NoDup_states_to_verts s : NoDup s -> NoDup (states_to_verts s).
  Proof with auto; try congruence.
    intros s nds. apply NoDup_app; try apply NoDup_map... intros. 
    destruct (proj1 (in_map_iff _ _ _ ) H) as [e [es _]]. subst. intro. 
    destruct (proj1 (in_map_iff _ _ _) H0) as [f [fs _]]. discriminate.
  Qed.

  Definition g : digraph.DiGraph :=
    digraph.Build eq_dec vertices vertices_exhaustive next NoDup_next.

  Lemma respect (s : a_State) : 
    c_abstract.reachable _ s ->
    exists k, exists v : digraph.Vertex g,
    c_abstract.initial_dec chs (snd v) = true /\
    digraph.reachable v (k, s).
  Proof with auto.
    intros s [absS [init [tt reach_alt]]].
    exists (if tt then Disc else Cont).
    induction reach_alt.
    exists (if b then Disc else Cont, s).
    split...
    destruct b; apply reachable_refl.
    destruct IHreach_alt as [v [init_v reach_v]]... 
    exists v. split...
    destruct b; simpl in *.
    apply reachable_next with (Cont, y)...
    simpl. apply in_map.
    destruct z. destruct y. destruct H. subst. simpl. apply in_map...
    apply reachable_next with (Disc, y)...
    destruct y. destruct z. simpl in *. apply in_map...
  Qed.

  Definition graph_unreachable_prop s (v : digraph.Vertex g) : Prop :=
    c_abstract.initial_dec chs (snd v) = true ->
    ~digraph.reachable v (Cont, s) /\ ~digraph.reachable v (Disc, s).

  Lemma respect_inv (s: a_State) :
    (forall v: digraph.Vertex g, graph_unreachable_prop s v) ->
    ~c_abstract.reachable _ s.
  Proof with auto.
    intros s rc abs_reach.
    destruct (respect abs_reach) as [tt [v [init reach]]].
    destruct (rc v init) as [reach_c reach_d].
    destruct tt...
  Qed.

  Definition init_verts : list V :=
    let is_initial v := c_abstract.initial_dec chs v in
    let init_states := filter is_initial all_abstract_states in
      states_to_verts init_states.

  Lemma init_verts_eq_aux (tt : TransKind) ss :
    map (pair tt) (filter (fun v => c_abstract.initial_dec chs (s:=ahs) v) ss) =
    filter (fun s => c_abstract.initial_dec chs (snd s)) (map (pair tt) ss).
  Proof.
    induction ss. ref. simpl. 
    destruct (c_abstract.initial_dec chs a); simpl; rewrite IHss; ref.
  Qed.

  Lemma init_verts_eq  :
    init_verts = 
    filter (fun s => c_abstract.initial_dec chs (snd s)) 
    (states_to_verts all_abstract_states).
  Proof.
    unfold init_verts, states_to_verts.
    do 2 rewrite init_verts_eq_aux. 
    apply filter_app.
  Qed.

  Lemma NoDup_init_verts : NoDup init_verts.
  Proof.
    apply NoDup_states_to_verts.
    apply NoDup_filter.
    apply c_abstract.NoDup_states.
    apply c_abstract.NoDup_regions.
  Qed.

  Definition state_reachable vr s : bool :=
    let edge tt := 
      match In_dec (digraph.Vertex_eq_dec g) (tt, s) vr with
      | left _ => true
      | right _ => false
      end
    in
      edge Cont || edge Disc.

  Definition reachable_verts :=
    let (vr, _) := @digraph.reachables g init_verts NoDup_init_verts in
      vr.

  Lemma over_abstract_reachable : 
    state_reachable reachable_verts >=> c_abstract.reachable ahs.
  Proof with auto.
    intros s sur. apply respect_inv. intros v init_t.
    unfold state_reachable, reachable_verts in sur.
    assert (In v init_verts).
    rewrite init_verts_eq. apply in_filter... apply vertices_exhaustive.
    destruct (@digraph.reachables g init_verts). 
    destruct (In_dec (digraph.Vertex_eq_dec g) (Cont, s) x);
    destruct (In_dec (digraph.Vertex_eq_dec g) (Disc, s) x); 
      try discriminate; split.
    intro. apply n. apply (snd (i (Cont, s))). exists v... 
    intro. apply n0. apply (snd (i (Disc, s))). exists v...
  Qed.

  Definition some_reachable ss : bool :=
    List.existsb (state_reachable reachable_verts) ss.

  Lemma states_unreachable (ss : list a_State) :
    some_reachable ss = false ->
    forall s cs, 
      In s ss -> c_abstract.abs ahs cs = s -> ~c_concrete.reachable cs.
  Proof with auto.
    intros. intro.
    contradict H. apply not_false_true.
    apply (snd (existsb_exists (state_reachable reachable_verts) ss)).
    exists s; split...
    subst. apply over_true with a_State (c_abstract.reachable ahs).
    apply over_abstract_reachable.
    apply c_abstract.reachable_concrete_abstract...
  Qed.

End using_duplication.
