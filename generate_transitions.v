Require rotator.
Require abstract_as_graph.
Require Import CRln.

Let conc_sys := rotator.concrete_system.
Let oconc_sys := rotator.oconcrete_system.

Let abs_sys := rotator.abstract_system (1#100).
Let oabs_sys := rotator.oabstract_system (1#100).

Let region: Set := c_abstract.Region abs_sys.
Let oregion: Set := c_abstract.Region oabs_sys.
Require c_abstract.

Let abs_state: Set := @c_abstract.State conc_sys (c_abstract.Region abs_sys).
Let oabs_state: Set := @c_abstract.State oconc_sys (c_abstract.Region oabs_sys).
Definition initstate: abs_state
  := (rotator.Up, (rotator.I01, rotator.I12)).
Definition oinitstate: oabs_state
  := (rotator.Up, (rotator.OI_1, rotator.OI12)).

Definition all_transitions: list (abs_state * abs_state) :=
  flat_map (fun s: abs_state =>
    map (pair s) (map (pair (fst s)) (c_abstract.cont_trans conc_sys s) ++ 
    c_abstract.disc_trans conc_sys s))
   (@c_abstract.states conc_sys _ (c_abstract.regions abs_sys)).

Definition oall_transitions: list (oabs_state * oabs_state) :=
  flat_map (fun s: oabs_state =>
    map (pair s) (map (pair (fst s)) (c_abstract.cont_trans oconc_sys s) ++ 
    c_abstract.disc_trans oconc_sys s))
   (@c_abstract.states oconc_sys _ (c_abstract.regions oabs_sys)).

Let graph := abstract_as_graph.g abs_sys.
Let ograph := abstract_as_graph.g oabs_sys.

Let init := (abstract_as_graph.Cont, initstate).
Let oinit := (abstract_as_graph.Cont, oinitstate).

Lemma NoDup_one X (x: X): NoDup (x :: nil). auto. Qed.

Definition reachables: list (digraph.Vertex graph) :=
  proj1_sig (@digraph.reachables graph (init::nil) (@NoDup_one _ _)).

Definition oreachables: list (digraph.Vertex ograph) :=
  proj1_sig (@digraph.reachables ograph (oinit::nil) (@NoDup_one _ _)).

Definition exported_edges: list (digraph.Vertex graph * digraph.Vertex graph)
  := flat_map (fun v => map (pair v) (digraph.edges v)) reachables.
  (* := digraph.flat_edge_list graph. *)

Definition oexported_edges: list (digraph.Vertex ograph * digraph.Vertex ograph)
  := flat_map (fun v => map (pair v) (digraph.edges v)) oreachables.
  (* := digraph.flat_edge_list graph. *)

Infix ":" := cons (at level 60, right associativity) : list_scope.
Notation "[]" := nil.

Set Printing Depth 10000.
Set Printing Width 1000000.

Require Import abstract_as_graph.
Require Import rotator.
  (* so that names aren't qualified in the output *)

Eval vm_compute in oexported_edges.
