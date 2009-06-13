Require Import List Bool.
Require Import util bool_util list_util.
Require abstract.
Require Import reachability.
Require digraph.
Set Implicit Arguments.

Section using_duplication.

  Variables
    (chs: concrete.System)
    (ap: abstract.Parameters chs)
    (ahs: abstract.System ap).

  Inductive TransKind := Cont | Disc.

  Instance transKinds: ExhaustiveList TransKind :=
    { exhaustive_list := Cont :: Disc :: [] }.
  Proof. destruct x; clear; firstorder. Defined.

  Instance TransKind_eq_dec: EquivDec.EqDec TransKind eq.
  Proof. repeat intro. cut (decision (x = y)). auto. dec_eq. Defined.

  Definition flip (k: TransKind) :=
    match k with Cont => Disc | Disc => Cont end.

  Let a_State := abstract.State ap.

  Let V := (TransKind * a_State)%type.

  Definition states_to_verts (s : list a_State) := map (pair Cont) s ++ map (pair Disc) s.

  Instance vertices: ExhaustiveList V := { exhaustive_list := states_to_verts (abstract.states ap) }.
  Proof. intro v. destruct v. apply in_or_app. destruct t; auto. Defined.

  Definition tr (k : TransKind) (s: a_State) : list a_State :=
    match k with
    | Cont => 
        let (l, r) := s in
          map (pair l) (proj1_sig (abstract.cont_trans ahs s))
    | Disc => proj1_sig (abstract.disc_trans ahs s)
    end.
     
  Definition next (v: V) : list V :=
    map (pair (flip (fst v))) (tr (fst v) (snd v)).

  Lemma NoDup_next v: NoDup (next v).
  Proof with auto; try congruence.
    intros. apply NoDup_map...
    destruct v. destruct a. destruct t; simpl. 
    apply NoDup_map...
    destruct_call abstract.cont_trans. simpl. destruct l0...
    destruct_call abstract.disc_trans. simpl. destruct l0...
  Qed.

  Lemma NoDup_states_to_verts s : NoDup s -> NoDup (states_to_verts s).
  Proof with auto; try congruence.
    intros s nds. apply NoDup_app; try apply NoDup_map... intros. 
    destruct (proj1 (in_map_iff _ _ _ ) H) as [e [es _]]. subst. intro. 
    destruct (proj1 (in_map_iff _ _ _) H0) as [f [fs _]]. discriminate.
  Qed.

  Definition g : digraph.DiGraph :=
    @digraph.Build (TransKind * abstract.State ap) _ _ _ NoDup_next.

  Lemma respect (s : a_State) : 
    abstract.reachable ahs s ->
    exists k, exists v : digraph.Vertex g,
    (@abstract.initial_dec chs ap ahs (snd v): bool) = true /\
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
    (@abstract.initial_dec _ _ ahs (snd v): bool) = true ->
    ~digraph.reachable v (Cont, s) /\ ~digraph.reachable v (Disc, s).

  Lemma respect_inv (s: a_State) :
    (forall v: digraph.Vertex g, graph_unreachable_prop s v) ->
    ~abstract.reachable ahs s.
  Proof with auto.
    intros s rc abs_reach.
    destruct (respect abs_reach) as [tt [v [init reach]]].
    destruct (rc v init) as [reach_c reach_d].
    destruct tt...
  Qed.

  Definition init_verts : list V :=
    let is_initial v := @abstract.initial_dec chs ap ahs v in
    let init_states := filter is_initial (abstract.states ap) in
      states_to_verts init_states.

  Lemma init_verts_eq_aux (tt : TransKind) ss :
    map (pair tt) (filter (fun v => abstract.initial_dec ahs v) ss) =
    filter (fun s => abstract.initial_dec ahs (snd s)) (map (pair tt) ss).
  Proof.
    induction ss. ref. simpl.
    destruct (abstract.initial_dec ahs a); destruct x; simpl; rewrite IHss; ref.
  Qed.

  Lemma init_verts_eq  :
    init_verts = 
    filter (fun s => abstract.initial_dec ahs (snd s))
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

  Definition reachable_verts: list V :=
    proj1_sig (@digraph.reachables g init_verts NoDup_init_verts).

  Hint Resolve in_filter.
  Obligation Tactic := idtac.

  Definition state_reachable vs s: bool :=
    unsumbool (In_dec (digraph.Vertex_eq_dec g) (Cont, s) vs) ||
    unsumbool (In_dec (digraph.Vertex_eq_dec g) (Disc, s) vs).
      (* We really only ever call state_reachable with vs=reachable_verts, but
       for efficiency reasons we don't hard-code it into state_reachable, because
       for some reason, that appears to cause it to be re-computed over and
       over again. This is also why state_reachable doesn't return an
       overestimation: nothing interesting can be concluded when nothing
       is known about vs. *)

  Lemma state_reachable_correct s:
    state_reachable reachable_verts s = false -> 
    ~ abstract.reachable ahs s.
  Proof with eauto.
    intros.
    apply respect_inv.
    unfold state_reachable in H.
    destruct (In_dec (digraph.Vertex_eq_dec g) (Cont, s) reachable_verts); [discriminate|].
    destruct (In_dec (digraph.Vertex_eq_dec g) (Disc, s) reachable_verts); [discriminate|].
    repeat intro.
    assert (In v init_verts). rewrite init_verts_eq...
    unfold reachable_verts in *.
    destruct (digraph.reachables g NoDup_init_verts).
    set (snd (i (Cont, s))).
    set (snd (i (Disc, s))).
    eauto 20.
  Qed.

  Definition some_reachable ss : bool :=
    List.existsb (state_reachable reachable_verts) ss.

  Lemma states_unreachable (P: concrete.State chs -> Prop) (ss : list a_State):
    (forall s, P s -> forall r, abstract.abs s r -> In r ss) ->
    some_reachable ss = false ->
    forall cs, P cs -> ~ concrete.reachable cs.
  Proof with auto.
    intros.
    apply (@abstract.safe chs ap ahs).
    unfold some_reachable in H0.
    intros.
    intro.
    set (H cs H1 s' H2). clearbody i.
    contradict H0.
    apply not_false_true.
    apply (snd (existsb_exists (state_reachable reachable_verts) ss)).
    exists s'.
    split...
    case_eq (state_reachable reachable_verts s')...
    intro. elimtype False.
    apply state_reachable_correct with s'...
  Qed.

End using_duplication.
