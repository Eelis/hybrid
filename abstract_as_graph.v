Require Import List.
Require Import Bool.
Require Import util.
Require Import list_util.
Require abstract.
Require Import reachability.
Require digraph.
Require Import dec_overestimator.
Set Implicit Arguments.

Section using_duplication.

  Variable chs: concrete.System.
  Variable ahs: abstract.System chs.

  Inductive TransKind := Cont | Disc.

  Instance transKinds: ExhaustiveList TransKind :=
    { exhaustive_list := Cont :: Disc :: [] }.
  Proof. destruct x; firstorder. Defined.

  Instance TransKind_eq_dec: EquivDec.EqDec TransKind eq.
  Proof. repeat intro. cut (decision (x = y)). auto. dec_eq. Defined.

  Definition flip (k: TransKind) :=
    match k with Cont => Disc | Disc => Cont end.

  Let a_State := abstract.State chs (abstract.Region ahs).

  Let V := (TransKind * a_State)%type.

  Definition all_abstract_states := @abstract.states chs _ _ (abstract.regions ahs).

  Definition states_to_verts (s : list a_State) := map (pair Cont) s ++ map (pair Disc) s.

  Instance vertices: ExhaustiveList V := { exhaustive_list := states_to_verts all_abstract_states }.
  Proof. intro v. destruct v. apply in_or_app. destruct t; auto. Defined.

  Definition tr (k : TransKind) (s: a_State) : list a_State :=
    match k with
    | Cont => 
        let (l, r) := s in
          map (pair l) (abstract.cont_trans _ s)
    | Disc => abstract.disc_trans _ s
    end.
     
  Definition next (v: V) : list V :=
    map (pair (flip (fst v))) (tr (fst v) (snd v)).

  Lemma NoDup_next v: NoDup (next v).
  Proof with auto; try congruence.
    intros. apply NoDup_map...
    destruct v. destruct a. destruct t; simpl. 
    apply NoDup_map...
    apply abstract.NoDup_cont_trans.
    apply abstract.NoDup_disc_trans.
  Qed.

  Lemma NoDup_states_to_verts s : NoDup s -> NoDup (states_to_verts s).
  Proof with auto; try congruence.
    intros s nds. apply NoDup_app; try apply NoDup_map... intros. 
    destruct (proj1 (in_map_iff _ _ _ ) H) as [e [es _]]. subst. intro. 
    destruct (proj1 (in_map_iff _ _ _) H0) as [f [fs _]]. discriminate.
  Qed.

  Definition g : digraph.DiGraph :=
    @digraph.Build (TransKind * abstract.State chs (abstract.Region ahs)) _ _ _ NoDup_next.

  Lemma respect (s : a_State) : 
    abstract.reachable _ s ->
    exists k, exists v : digraph.Vertex g,
    abstract.initial_dec chs (snd v) = true /\
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
    abstract.initial_dec chs (snd v) = true ->
    ~digraph.reachable v (Cont, s) /\ ~digraph.reachable v (Disc, s).

  Lemma respect_inv (s: a_State) :
    (forall v: digraph.Vertex g, graph_unreachable_prop s v) ->
    ~abstract.reachable _ s.
  Proof with auto.
    intros s rc abs_reach.
    destruct (respect abs_reach) as [tt [v [init reach]]].
    destruct (rc v init) as [reach_c reach_d].
    destruct tt...
  Qed.

  Definition init_verts : list V :=
    let is_initial v := abstract.initial_dec chs v in
    let init_states := filter is_initial all_abstract_states in
      states_to_verts init_states.

  Lemma init_verts_eq_aux (tt : TransKind) ss :
    map (pair tt) (filter (fun v => abstract.initial_dec chs (s:=ahs) v) ss) =
    filter (fun s => abstract.initial_dec chs (snd s)) (map (pair tt) ss).
  Proof.
    induction ss. ref. simpl. 
    destruct (abstract.initial_dec chs a); simpl; rewrite IHss; ref.
  Qed.

  Lemma init_verts_eq  :
    init_verts = 
    filter (fun s => abstract.initial_dec chs (snd s))
    vertices.
  Proof.
    unfold init_verts, states_to_verts.
    do 2 rewrite init_verts_eq_aux. 
    apply filter_app.
  Qed.

  Lemma NoDup_init_verts : NoDup init_verts.
  Proof.
    apply NoDup_states_to_verts.
    apply NoDup_filter.
    apply abstract.NoDup_states.
    apply abstract.NoDup_regions.
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

Hint Resolve in_filter.

  Lemma over_abstract_reachable : 
    state_reachable reachable_verts >=> abstract.reachable ahs.
  Proof with auto.
    intros s sur. apply respect_inv. intros v init_t.
    unfold state_reachable, reachable_verts in sur.
    assert (In v init_verts). rewrite init_verts_eq...
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
      In s ss -> abstract.abs ahs cs = s -> ~concrete.reachable cs.
  Proof with auto.
    intros. intro.
    contradict H. apply not_false_true.
    apply (snd (existsb_exists (state_reachable reachable_verts) ss)).
    exists s; split...
    subst. apply over_true with a_State (abstract.reachable ahs).
    apply over_abstract_reachable.
    apply abstract.reachable_concrete_abstract...
  Qed.

End using_duplication.
