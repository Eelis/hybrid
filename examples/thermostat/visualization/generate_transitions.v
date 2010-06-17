Require abstract_as_graph.
Require Import CRln c_util.
Require Import thermostat.abs.
Require Import thermostat.conc.

Let abs_sys := abs.system milli.
Let graph := abstract_as_graph.g abs_sys.
Let init: digraph.Vertex graph := (true, (conc.Heat, (bnat.bO _, bnat.bO _))).

Lemma NoDup_one X (x: X): NoDup (x :: nil). auto. Qed.

Definition reachables: list (digraph.Vertex graph) :=
  proj1_sig (@digraph.reachables graph (init::nil) (@NoDup_one _ _)).

Definition exported_edges: list (digraph.Vertex graph * digraph.Vertex graph)
  := flat_map (fun v => map (pair v) (digraph.edges v)) reachables.

Definition PrintedVertex := (bool * (Location * nat * nat))%type.

Definition printVertex (v: digraph.Vertex graph): PrintedVertex :=
  (fst v, (fst (snd v), (bnat.to_nat (fst (snd (snd v)))), bnat.to_nat (snd (snd (snd v))))).

Definition printed_edges: list (PrintedVertex * PrintedVertex)
  := map (fun e => (printVertex (fst e), printVertex (snd e))) exported_edges.

Infix ":" := cons (at level 60, right associativity) : list_scope.
Notation "[]" := nil.
Notation True := true.
Notation False := false.
  (* so that it's valid Haskell *)

Set Printing Depth 10000.
Set Printing Width 1000000.

Require Import abstract_as_graph.
  (* so that names aren't qualified in the output *)

Eval vm_compute in printed_edges.
