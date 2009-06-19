Require Import List Bool util list_util.
Require abstract digraph.
Require Import reachability.

Set Implicit Arguments.

Local Open Scope type_scope.

(* Given an abstract system, we can compute reachability overestimations. We do this by
 making a graph corresponding to the abstract system, and using a graph reachability
 algorithm on it. *)

Section using_duplication.

  Variables
    (chs: concrete.System)
    (ap: abstract.Parameters chs)
    (ahs: abstract.System ap).

  Let Vertex := bool * abstract.State ap.

  (* The purpose of the bool component is the following. In the graph, some edges will
   correspond to abstract _continuous_ transitions, while others will correspond to abstract
   _discrete_ transitions. We do not want to allow two successive transitions of the same
   kind. The solution we use (for now) is to add two vertices for each abstract state,
   one with fst = true, and one with fst = false. Next, we only add edges corresponding to
   abstract continuous transitions from a vertex with fst = true to a vertex with fst = false, and
   only add edges corresponding to abstract discrete transitions from a vertex with
   fst = false to a vertex with fst = true. This ensures that paths through the graph alternate
   between vertices with fst = true and vertices with fst = false, and that the corresponding
   abstract traces alternate between continuous and discrete transitions. *)

  Definition nexts (v: Vertex): list (abstract.State ap) :=
    let (k, s) := v in (if k
      then map (pair (fst s)) (` (abstract.cont_trans ahs s))
      else ` (abstract.disc_trans ahs s)).

  Definition edges (v: Vertex): list Vertex := map (pair (negb (fst v))) (nexts v).

  Lemma NoDup_edges v: NoDup (edges v).
  Proof with auto; try congruence.
    intros [k [l r]].
    apply NoDup_map...
    unfold nexts.
    destruct abstract.cont_trans. destruct abstract.disc_trans.
    simpl.
    destruct l0... destruct l1... destruct k...
    apply NoDup_map...
  Qed.

  Definition g : digraph.DiGraph :=
    @digraph.Build (bool * abstract.State ap) _ _ edges NoDup_edges.

  (* Next, we show that reachability in the graph is equivalent to reachability in the abstract system. *)

  Lemma edges_match_transitions y b x: In y (nexts (b, x)) <-> abstract.trans ahs b x y.
  Proof with auto.
    intros [l' r'] b [l r]. simpl.
    split; destruct b...
      intro.
      destruct (fst (in_map_iff _ _ _) H) as [x [C D]].
      inversion C. subst...
    intros [A B].
    subst...
  Qed.

  Lemma paths_match_traces x y:
    (exists b, digraph.reachable ((b, x): digraph.Vertex g) y) <->
    end_with (abstract.trans ahs) (negb (fst y)) x (snd y).
  Proof with auto.
    split.
      intros [b r].
      replace x with (snd (b, x))...
      set (b, x) in *.
      clearbody p.
      clear b.
      induction r...
      destruct (fst (in_map_iff _ _ _) H) as [x0 [A B]]. clear H.
      subst. simpl.
      rewrite negb_involutive.
      apply (end_with_next _ IHr).
      apply (edges_match_transitions x0 (fst b) (snd b))...
      destruct b...
    destruct y.
    simpl.
    generalize b. clear b.
    cut (forall b, end_with (abstract.trans ahs) b x s -> exists b0, digraph.reachable ((b0, x): digraph.Vertex g) (negb b, s)).
      intros.
      rewrite <- (negb_involutive b)...
    intros b r.
    induction r.
      unfold digraph.reachable.
      exists (negb b).
      apply reachable_refl.
    unfold digraph.reachable in *.
    destruct IHr.
    rewrite negb_involutive in H0.
    exists x0.
    apply (@reachable_next _ (fun v w : digraph.Vertex g => In w (digraph.edges v)) (x0, x) (b, y) (negb b, z) H0).
    unfold digraph.edges.
    simpl.
    unfold edges.
    simpl negb.
    apply in_map.
    apply <- edges_match_transitions...
  Qed.

  Definition graph_reachable (s: abstract.State ap): Prop :=
    exists i: digraph.Vertex g, overestimation_bool (abstract.initial_dec ahs (snd i)) = true /\
    exists k, digraph.reachable i (k, s).

  Hint Unfold graph_reachable In.

  Theorem respect s: abstract.reachable ahs s <-> graph_reachable s.
  Proof with auto.
    unfold abstract.reachable.
    unfold graph_reachable.
    split.
      intros [x [H [x0 H0]]].
      rewrite <- (negb_involutive x0) in H0.
      destruct (snd (paths_match_traces x (_, _)) H0).
      exists (x1, x). eauto.
    intros [[b s0] [H [k H0]]].
    exists s0. split...
    exists (negb k).
    apply (paths_match_traces s0 (k, s)). eauto.
  Qed.

  (* Since we can decide reachability in the graph, we can now decide reachability in the abstract system. *)

  Definition init_verts: list Vertex :=
    filter (fun v: Vertex => overestimation_bool (abstract.initial_dec ahs (snd v)))
      ExhaustivePairList.

  Hint Unfold init_verts.

  Lemma NoDup_init_verts : NoDup init_verts.
  Proof with auto; try congruence.
    unfold init_verts.
    apply NoDup_filter.
    apply NoDup_ExhaustivePairList.
      apply NoDup_bools.
    apply abstract.NoDup_states.
    apply abstract.NoDup_regions.
  Qed.

  Program Let reachable_verts := digraph.reachables g NoDup_init_verts.

  Program Let state_reachable s: decision (abstract.reachable ahs s) :=
    @equivalent_decision (exists b, In (b, s) (`reachable_verts)) _ _ decide.

  Hint Resolve in_filter.

  Next Obligation. Proof with auto.
    split.
      intros [x H].
      destruct reachable_verts.
      simpl proj1_sig in H.
      apply <- respect.
      unfold graph_reachable.
      destruct (fst (i (_, s)) H) as [x1 [H0 H1]].
      exists x1.
      split...
        destruct (fst (filter_In _ _ _) H0)...
      eauto.
    intro.
    destruct (fst (respect s) H) as [x [H0 [x0 H1]]].
    destruct reachable_verts.
    exists x0.
    apply <- i.
    unfold init_verts.
    eauto.
  Qed.

  (* Using the above, we can overestimate reachability of sets of concrete states. *)

  Variables
    (cstates: concrete.State chs -> Prop)
    (astates: list (abstract.State ap))
    (astates_cover_cstates: forall s, cstates s -> forall r, abstract.abs s r -> In r astates).

  Program Definition some_reachable: overestimation (overlap cstates concrete.reachable) :=
    unsumbool (@decide (exists u, In u astates /\ abstract.reachable ahs u) decide).

  Next Obligation. Proof with eauto.
    intros H [x [Px r]].
    apply (@abstract.safe _ _ ahs x)...
    repeat intro. apply (decision_false _ H)...
  Qed.

End using_duplication.
