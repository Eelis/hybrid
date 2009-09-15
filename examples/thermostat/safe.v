Require Import c_util util.
Require List.
Require decreasing_exponential_flow.
Require abstract.
Require abstract_as_graph.
Require Import Program.

Require hybrid.examples.thermostat.conc hybrid.examples.thermostat.abs.
Module conc := thermostat.conc.
Module abs := thermostat.abs.

Program Definition over_unsafe_reachable: overestimation (containers.overlap thermostat.conc.unsafe concrete.reachable) :=
  @abstract_as_graph.some_reachable _ _ (abs.system milli) conc.unsafe (abs.unsafe_abstract milli).

Definition under_unsafe_unreachable: underestimation conc.UnsafeUnreachable.
Proof with eauto.
  destruct over_unsafe_reachable.
  destruct x. exact None.
  apply Some.
  repeat intro.
  unfold containers.overlap, containers.nonempty, containers.In, containers.intersection,
    containers.In, containers.predicate_container in *.
  apply n...
Defined.

Theorem unsafe_unreachable: conc.UnsafeUnreachable.
Proof. apply (underestimation_true under_unsafe_unreachable). Time vm_compute. reflexivity. Qed.

Print Assumptions unsafe_unreachable.
