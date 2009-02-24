Require rotator.
Require abstract_as_graph.
Require Import CRln.

Let abs_sys := proj1_sigT _ _ (rotator.abstract_system (1#100)).
Let abs_state := abstract.State abs_sys.

Definition initstate: abstract.State abs_sys
  := (rotator.Up, (rotator.I01, rotator.I12)).

Definition all_transitions: list (abs_state * abs_state) :=
  flat_map (fun s => map (pair s) (abstract.cont_trans s ++ abstract.disc_trans s))
   (abstract.states abs_sys).

Let graph := abstract_as_graph.g abs_sys.

Definition reachables: list (digraph.Vertex graph) :=
  proj1_sig (digraph.reachables graph (abstract_as_graph.Cont, initstate)).

Definition all_edges: list (digraph.Vertex graph * digraph.Vertex graph)
  := flat_map (fun v => map (pair v) (digraph.edges v)) reachables.
  (* := digraph.flat_edge_list g. *)

Infix ":" := cons (at level 60, right associativity) : list_scope.
Notation "[]" := nil.

Set Printing Depth 10000.
Set Printing Width 1000000.

Require Import abstract_as_graph.
Require Import rotator.
  (* so that names aren't qualified in the output *)

Eval vm_compute in all_edges.
