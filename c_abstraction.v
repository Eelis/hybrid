Require Import List.
Require Import dec_overestimator.
Require Import c_util.
Require Import list_util.
Require Import CSetoids.
Require Import CRreal.
Require Import c_flow.
Require c_concrete.
Require c_abstract.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section contents.

  Variables
    (conc_sys : c_concrete.System)
    (Region : Set) 
    (Region_eq_dec : forall i i': Region, decision (i=i'))
    (in_region : c_concrete.Point conc_sys -> Region -> Prop)
    (regions : list Region)
    (regions_complete : forall i, List.In i regions)
    (NoDup_regions : NoDup regions).

  Let Location := c_concrete.Location conc_sys.
  Let Point := c_concrete.Point conc_sys.
  Let c_State := c_concrete.State conc_sys.
  Let State := (Location * Region)%type.

  Variable select_region : Point -> Region.
    (* does not have to be constructive, because it is only
       used in the correctness proof. *)

  Definition initial_condition (s : State) : Prop :=
    let (l, r) := s in
      exists p, in_region p r /\ c_concrete.initial (l, p).

  Definition cont_trans_cond (w : Location * (Region * Region)) : Prop :=
    let (l, r) := w in
    let (r1, r2) := r in
      exists p, exists q,
        in_region p r1 /\ in_region q r2 /\ c_concrete.cont_trans (l, p) (l, q).

  Definition disc_trans_cond (s : State * State): Prop :=
    let (s1, s2) := s in
    let (l1, r1) := s1 in
    let (l2, r2) := s2 in
      exists p, exists q,
        in_region p r1 /\ in_region q r2 /\ c_concrete.disc_trans (l1, p) (l2, q).

  Variables
    (cont_do : dec_overestimator cont_trans_cond)
    (disc_do : dec_overestimator disc_trans_cond)
    (initial_do : dec_overestimator initial_condition).

  (* Using these, we can define the abstract transitions.. *)

  Let cont_trans_b (s : State) (r_dst : Region) : bool :=
    let (l, r_src) := s in
    (do_pred cont_do) (l, (r_src, r_dst)).

  Let disc_trans_b (s1 s2 : State): bool :=
    (do_pred disc_do) (s1, s2).

  Definition RegionsCoverInvariants : Prop :=
    forall l p, c_concrete.invariant (l, p) ->
      in_region p (select_region p).

  Variable regions_cover_invariants : RegionsCoverInvariants.

  Definition initial_prop (s : State) :=
    let (l, r) := s in
      exists p, select_region p = r /\ c_concrete.initial (l, p).

  Definition initial_dec (s : State) :=
    let (l, r) := s in
      do_pred initial_do (l, r).

  Lemma over_initial : initial_dec >=> initial_prop.
  Proof with auto.
    intros s init ips. destruct s.
    apply (do_correct initial_do (l, r))...
    destruct ips as [p [pr lp]].
    exists p. split...
    subst. apply (regions_cover_invariants l).
    apply c_concrete.invariant_initial. hyp.
  Qed.

  Definition disc_trans (s : State) : list State :=
    filter (disc_trans_b s) (c_abstract.states conc_sys regions).
      (* a more efficient implementation would grow the graph *)

  Lemma NoDup_disc_trans s : NoDup (disc_trans s).
  Proof with auto.
    intro. apply NoDup_filter. apply c_abstract.NoDup_states...
  Qed.

  Lemma respects_disc (s1 s2 : c_State) :
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
    c_concrete.disc_trans s1 s2 ->
    In (l2, select_region p2) (disc_trans (l1, select_region p1)).

  Proof with auto.
    intros [l1 p1] [l2 p2] dt.
    apply in_filter.
    apply c_abstract.states_exhaustive...
    set (s1 := (l1, select_region p1)). set (s2 := (l2, select_region p2)).
    apply do_over_true.
    destruct dt as [guard [reset [inv1 inv2]]].
    exists p1. exists p2. 
    repeat split; solve 
      [ hyp 
      | simpl; eapply regions_cover_invariants; eassumption].
  Qed.

  Add Morphism (c_concrete.inv_curried conc_sys)
    with signature (@eq _) ==> (@cs_eq _) ==> iff
    as inv_mor.
  Proof.
    intros. apply c_concrete.invariant_wd; trivial.
  Qed.

  Definition cont_trans (s : State) : list Region :=
    filter (cont_trans_b s) regions.

  Hint Immediate CRle_refl : real.

  Lemma respects_cont l s1 s2 : 
    c_concrete.cont_trans' _ l s1 s2 ->
    In (select_region s2) (cont_trans (l, select_region s1)).
  Proof with auto with real.
    intros l s1 s2 [t [inv flow]].
    apply in_filter.
    apply regions_complete.
    apply do_over_true.
    exists s1. exists s2.
    repeat split.

    apply regions_cover_invariants with l. rewrite c_concrete.curry_inv.
    rewrite <- (flow_zero (c_concrete.flow conc_sys l) s1).
    apply inv... destruct t. simpl. apply (CRnonNeg_le_zero x). hyp.

    apply regions_cover_invariants with l. rewrite c_concrete.curry_inv.
    rewrite <- flow. apply inv...
    destruct t. simpl. apply (CRnonNeg_le_zero x)...

    exists t...
  Qed.

  Lemma NoDup_cont_trans s : NoDup (cont_trans s).
  Proof. unfold cont_trans. auto. Qed.

  Program Definition abstract_system : c_abstract.System conc_sys :=
    c_abstract.Build_System Region_eq_dec regions_complete
     NoDup_regions select_region over_initial disc_trans
     NoDup_disc_trans respects_disc cont_trans NoDup_cont_trans respects_cont.

End contents.
