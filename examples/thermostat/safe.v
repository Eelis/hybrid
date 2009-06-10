Require Import c_util.
Require List.
Require decreasing_exponential_flow.
Require abstract.
Require abstract_as_graph.
Require Import Program.

Require hybrid.examples.thermostat.conc hybrid.examples.thermostat.abs.
Module conc := thermostat.conc.
Module abs := thermostat.abs.

Set Implicit Arguments.

Definition abs_sys := abs.system milli.

Program Definition unsafe_reachable: bool :=
  abstract_as_graph.some_reachable abs_sys (abs.unsafe_abstract milli).

Theorem unsafe_correct: unsafe_reachable = false -> conc.UnsafeUnreachable.
Proof with auto.
  unfold unsafe_reachable, conc.UnsafeUnreachable.
  intros srf [l [px py]] su.
  apply (abstract_as_graph.states_unreachable abs_sys conc.unsafe (proj1_sig (abs.unsafe_abstract milli)))...
  destruct_call abs.unsafe_abstract.
  eauto.
Qed.

Theorem unsafe_unreachable: conc.UnsafeUnreachable.
Proof. Time apply unsafe_correct; vm_compute; reflexivity. Qed.

Print Assumptions unsafe_unreachable.
