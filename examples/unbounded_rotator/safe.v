Require Import util c_util.
Require abstract abstract_as_graph.
Require Import Program.

Require unbounded_rotator.conc unbounded_rotator.abs.
Module conc := unbounded_rotator.conc.
Module abs := unbounded_rotator.abs.

Definition abs_sys := abs.system centi.

Program Definition unsafe_reachable: bool :=
  abstract_as_graph.some_reachable abs_sys (abs.unsafe_abstract centi).

Theorem unsafe_correct: unsafe_reachable = false -> conc.UnsafeUnreachable.
Proof with auto.
  unfold unsafe_reachable, conc.UnsafeUnreachable.
  intros srf [l [px py]] su.
  apply (abstract_as_graph.states_unreachable abs_sys conc.unsafe (proj1_sig (abs.unsafe_abstract centi)))...
  destruct_call abs.unsafe_abstract.
  eauto.
Qed.

Theorem unsafe_unreachable: conc.UnsafeUnreachable.
Proof. Time apply unsafe_correct; vm_compute; reflexivity. Qed.

Print Assumptions unsafe_unreachable.
