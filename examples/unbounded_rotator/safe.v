Require Import util c_util.
Require abstract abstract_as_graph.
Require Import Program.

Require hybrid.examples.unbounded_rotator.conc hybrid.examples.unbounded_rotator.abs.
Module conc := unbounded_rotator.conc.
Module abs := unbounded_rotator.abs.

Theorem unsafe_unreachable: conc.UnsafeUnreachable.
Proof with eauto.
  repeat intro.
  cut (~ exists s, unbounded_rotator.conc.unsafe s /\ concrete.reachable s)...
  assert (forall s, unbounded_rotator.conc.unsafe s -> forall r,
   abstract.abs s r -> In r (` (unbounded_rotator.abs.unsafe_abstract centi))).
    destruct abs.unsafe_abstract...
  apply (overestimation_false (@abstract_as_graph.some_reachable _ _ (abs.system centi) conc.unsafe (abs.unsafe_abstract centi))).
  Time vm_compute. reflexivity.
Qed.

Print Assumptions unsafe_unreachable.
