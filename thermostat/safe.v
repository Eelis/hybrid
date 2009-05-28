Require Import c_util.
Require List.
Require decreasing_exponential_flow.
Require abstract.
Require abstract_as_graph.

Require thermostat.conc thermostat.abs.
Module conc := thermostat.conc.
Module abs := thermostat.abs.

Set Implicit Arguments.

Definition abs_sys := abs.system milli.

Definition vs := abstract_as_graph.vertices abs_sys.
Definition g := abstract_as_graph.g abs_sys.
Definition graph := flat_map (@digraph.edges g) vs.

Definition Safe: Prop :=
  forall s: concrete.State conc.system,
    conc.state_unsafe s -> ~ concrete.reachable s.

Definition unsafe_abstract_states :=
  List.flat_map (fun l => map (fun ci => (l, (ci, abs.TI_5))) abs.clock_intervals) conc.locations.

Definition unsafe_abstracts_cover_unsafe_concretes:
  forall s, conc.state_unsafe s ->
  forall r, abstract.abs abs_sys s r -> In r unsafe_abstract_states.
Proof with auto.
  intros [l [c t]] H [l' [ci ti]] [H0 [_ tin]].
  subst.
  apply <- in_flat_map.
  exists l'. split...
  simpl.
  replace ti with abs.TI_5. destruct ci; auto 10.
  destruct tin.
  destruct ti; auto; elimtype False;
    apply (util.flip (@CRlt_le_asym _ _) (CRle_trans H1 H)), CRlt_Qlt;
    vm_compute...
Qed.

Definition unsafe : bool :=
  abstract_as_graph.some_reachable abs_sys unsafe_abstract_states.

Theorem unsafe_correct: unsafe = false -> Safe.
Proof with auto.
  unfold unsafe, Safe.
  intros srf [l [px py]] su.
  apply (abstract_as_graph.states_unreachable (ahs:=abs_sys) conc.state_unsafe unsafe_abstract_states)...
  apply unsafe_abstracts_cover_unsafe_concretes.
Qed.

Theorem safe: Safe.
Proof. Time apply unsafe_correct; vm_compute; reflexivity. Qed.

Print Assumptions safe.
