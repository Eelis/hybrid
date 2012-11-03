Require Import List Bool util list_util.
Require abstract digraph.

Require Import EquivDec.

Set Implicit Arguments.

Local Open Scope type_scope.

Section using_duplication.

  Variables
    (chs: concrete.System)
    (ap: abstract.Space chs)
    (ahs: abstract.System ap).

  Let Vertex : Type := bool * abstract.State ap.

  Definition nexts (v: Vertex): list (abstract.State ap) :=
    let (k, s) := v in
      if k then ` (abstract.cont_trans_over ahs s)
      else ` (abstract.disc_trans_over ahs s).

  Definition edges (v: Vertex): list Vertex := map (pair (negb (fst v))) (nexts v).

  Lemma NoDup_edges v: NoDup (edges v).
  Proof with auto; try congruence.
    revert v.
    intros [k [l r]].
    apply NoDup_map...
    unfold nexts.
    destruct k.
      destruct abstract.cont_trans_over. simpl. destruct l0...
    destruct abstract.disc_trans_over. simpl. destruct l0...
  Qed.

  Definition g: digraph.DiGraph :=
    @digraph.Build (bool * abstract.State ap) _ _ edges NoDup_edges.

  Lemma edges_match_transitions y b x: In y (nexts (b, x)) <-> abstract.trans ahs b x y.
  Proof with auto.
    destruct y as [l' r'].
    destruct x as [l r]. simpl.
    split; destruct b...
  Qed.

  Lemma paths_match_traces x y:
    (exists b, trans_refl_closure.R (digraph.edge g) (b, x) y) <->
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
    cut (forall b, end_with (abstract.trans ahs) b x s -> exists b0, trans_refl_closure.R (digraph.edge g) ((b0, x): digraph.Vertex g) (negb b, s)).
      intros.
      rewrite <- (negb_involutive b)...
    intros b r.
    induction r.
      unfold digraph.reachable.
      exists (negb b)...
    unfold digraph.reachable in *.
    destruct IHr.
    rewrite negb_involutive in H0.
    exists x0.
    apply (@trans_refl_closure.step _ (fun v w : digraph.Vertex g => In w (digraph.edges v)) (x0, x) (b, y) (negb b, z) H0).
    unfold digraph.edges.
    simpl.
    unfold edges.
    simpl negb.
    apply in_map.
    apply <- edges_match_transitions...
  Qed.

  Hint Unfold In.

  Definition init_verts: list Vertex :=
    filter (fun v: Vertex => overestimation_bool (abstract.initial_dec ahs (snd v)))
      ExhaustivePairList.

  Theorem respect: forall s: abstract.State ap,
    abstract.reachable ahs s <-> exists k, @digraph.reachable g init_verts (k, s).
  Proof with auto.
    unfold abstract.reachable.
    split.
      intros [x [H [x0 H0]]].
      rewrite <- (negb_involutive x0) in H0.
      destruct (snd (paths_match_traces x (_, _)) H0).
      unfold digraph.reachable, init_verts.
      exists (negb x0) (x1, x).
      auto using in_filter.
    intros [k [v [vi R]]].
    exists (snd v).
    unfold init_verts in vi.
    apply filter_In in vi.
    destruct vi.
    split...
    unfold alternate.
    exists (negb k).
    apply (paths_match_traces (snd v) (k, s)).
    destruct v.
    eauto.
  Qed.

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
    (* Having this as a separate definition is critical for efficiency. *)

  Hint Resolve in_filter.

  Definition state_reachable: decider (abstract.reachable ahs).
  Proof with auto.
   intro s.
   simpl.
   apply (@equivalent_decision (exists b, In (b, s) (`reachable_verts))).
    split.
     intros [x H].
     destruct reachable_verts.
     apply <- respect.
     exists x.
     apply -> i...
    intro.
    apply respect in H.
    destruct H.
    destruct H.
    exists x.
    destruct @reachable_verts.
    simpl proj1_sig.
    apply <- i.
    unfold digraph.reachable...
    eauto.
   apply (@decide_exists bool _ _).
   intros.
   apply (@In_decision _ _ _).
   (* todo: this last goal is just instance resolution but it appears to diverge *)
  Defined.

(*  Program Let state_reachable: decider (abstract.reachable ahs) :=
    fun s => @equivalent_decision (exists b, In (b, s) (`reachable_verts)) _ _ decide.
*)

  Definition some_reachable := abstract.some_reachable_2 (decider_to_overestimator _ state_reachable).

End using_duplication.
