Require Import thermostat.
Require abstract_as_graph.
Require Import CRln.

Let conc_sys := concrete_system.
Let abs_sys := abstract_system (1#100).

Let region: Set := abstract.Region abs_sys.

Require abstract.

Let abs_state: Set := @abstract.State conc_sys (abstract.Region abs_sys).

Definition initstate: abs_state
  := (thermostat.Heat, (thermostat.CI0_D, thermostat.TI6_9)).

Definition all_transitions: list (abs_state * abs_state) :=
  flat_map (fun s: abs_state =>
    map (pair s) (map (pair (fst s)) (abstract.cont_trans conc_sys s) ++
    abstract.disc_trans conc_sys s))
   (@abstract.states conc_sys _ _ (abstract.regions abs_sys)).

Let graph := abstract_as_graph.g abs_sys.

Let init := (abstract_as_graph.Cont, initstate).

Lemma NoDup_one X (x: X): NoDup (x :: nil). auto. Qed.

Definition reachables: list (digraph.Vertex graph) :=
  proj1_sig (@digraph.reachables graph (init::nil) (@NoDup_one _ _)).

Definition exported_edges: list (digraph.Vertex graph * digraph.Vertex graph)
  := flat_map (fun v => map (pair v) (digraph.edges v)) reachables.
  (* := digraph.flat_edge_list graph. *)

Infix ":" := cons (at level 60, right associativity) : list_scope.
Notation "[]" := nil.

Set Printing Depth 10000.
Set Printing Width 1000000.

Require Import abstract_as_graph.
  (* so that names aren't qualified in the output *)

Eval vm_compute in exported_edges.
