Require Import c_util util.
Require List.
Require decreasing_exponential_flow.
Require abstract.
Require abstract_as_graph.
Require Import Program.

Require hybrid.examples.thermostat.conc hybrid.examples.thermostat.abs.
Module conc := thermostat.conc.
Module abs := thermostat.abs.

Obligation Tactic := idtac.

Program Definition unsafe_reachable :=
  abstract_as_graph.some_reachable (abs.system milli) conc.unsafe (abs.unsafe_abstract milli) _.

Next Obligation. destruct abs.unsafe_abstract. eauto. Qed.

Theorem unsafe_correct: (unsafe_reachable: bool) = false -> conc.UnsafeUnreachable.
Proof. repeat intro. apply (overestimation_false _ H). unfold overlap. eauto. Qed.

Theorem unsafe_unreachable: conc.UnsafeUnreachable.
Proof. Time apply unsafe_correct; vm_compute; reflexivity. Qed.

(* Hm, integrating the above further as in unbounded_rotator.safe makes the final Qed very slow.. *)

Print Assumptions unsafe_unreachable.
