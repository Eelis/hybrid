Require Import List.
Require Import util.
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
    (conc_sys: c_concrete.System)
    (Region: Set) (Region_eq_dec: forall i i': Region, decision (i=i'))
    (in_region: c_concrete.Point conc_sys -> Region -> Prop)
    (regions: list Region)
    (regions_complete: forall i, List.In i regions)
    (NoDup_regions: NoDup regions).

  Let Location := c_concrete.Location conc_sys.
  Let Point := c_concrete.Point conc_sys.
  Let State := prod Location Region.

  Variable select_region: Point -> Region.
    (* does not have to be constructive, because it is only
       used in the correctness proof. *)

  Definition initial_condition (l: State): Prop :=
    exists p, in_region p (snd l) /\
    c_concrete.initial (fst l, p).

  Definition cont_trans_cond
    (l: prod Location (prod Region Region)): Prop :=
    exists p, exists q,
      in_region p (fst (snd l)) /\ in_region q (snd (snd l)) /\
      c_concrete.cont_trans (fst l, p) (fst l, q).

  Definition disc_trans_cond (l: prod State State): Prop :=
    exists p, exists q,
      in_region p (snd (fst l)) /\ in_region q (snd (snd l)) /\
      c_concrete.disc_trans (fst (fst l), p) (fst (snd l), q).

  Variables
    (cont_decider: weak_decider cont_trans_cond)
    (disc_decider: weak_decider disc_trans_cond)
    (initial_decider: weak_decider initial_condition).

  (* Using these, we can define the abstract transitions.. *)

  Let cont_trans_b (l: Location) (s s': Region): bool :=
    negb (opt_to_bool (cont_decider (l, (s, s')))).
  Let disc_trans_b (s s': State): bool :=
    negb (opt_to_bool (disc_decider (s, s'))).

  Definition disc_trans (s: State): list State :=
    filter (disc_trans_b s) (c_abstract.states conc_sys regions).
      (* a more efficient implementation would grow the graph *)

  Lemma NoDup_disc_trans s: NoDup (disc_trans s).
  Proof with auto.
    intro. apply NoDup_filter. apply c_abstract.NoDup_states...
  Qed.

  Definition RegionsCoverInvariants': Prop :=
    forall l p, c_concrete.invariant (l, p) ->
    exists r, in_region p r.

  Definition RegionsCoverInvariants: Prop :=
    forall l p, c_concrete.invariant (l, p) ->
      in_region p (select_region p).

  Hypothesis regions_cover_invariants: RegionsCoverInvariants.
  Hypothesis regions_cover_invariants': RegionsCoverInvariants'.

  Definition initial (l: Location) (r: Region):
    option (forall p, select_region p = r -> ~ c_concrete.initial (l, p)).
  Proof with auto.
    intros.
    destruct (initial_decider (l, r)).
      unfold initial_condition in n.
      apply Some.
      intros.
      subst. intro.
      apply n.
      exists p.
      split...
      simpl.
      apply regions_cover_invariants with l...
      apply c_concrete.invariant_initial...
    exact None.
  Defined.

  Lemma respects_disc (s1 s2: c_concrete.State conc_sys):
    c_concrete.disc_trans s1 s2 ->
    In (fst s2, select_region (snd s2)) (disc_trans (fst s1, select_region (snd s1))).
  Proof with auto.
    intros.
    unfold disc_trans.
    apply (snd (filter_In (disc_trans_b (fst s1, select_region (snd s1))) (fst s2, select_region (snd s2)) (c_abstract.states conc_sys regions))).
    split. apply c_abstract.states_exhaustive. apply regions_complete.
    unfold disc_trans_b.
    destruct (disc_decider (@pair State State (fst s1, select_region (snd s1)) (fst s2, select_region (snd s2))))...
    elimtype False.
    apply n.
    unfold disc_trans_cond.
    simpl @fst. simpl @snd.
    destruct H. destruct H0. destruct H1.
    exists (snd s1). exists (snd s2).
    repeat rewrite fst_absFunc.
    simpl c_concrete.Location. simpl c_concrete.Point.
    destruct s1. destruct s2.
    split. apply regions_cover_invariants with l...
    split. apply regions_cover_invariants with l0...
    unfold c_concrete.disc_trans...
  Defined.

  Add Morphism (c_concrete.inv_curried conc_sys)
    with signature (@eq _) ==> (@cs_eq _) ==> iff
    as inv_mor.
  Proof.
    intros.
    apply c_concrete.invariant_wd.
      reflexivity.
    assumption.
  Qed.

  Definition cont_trans (l: Location) (r: Region): list Region :=
    filter (cont_trans_b l r) regions.

  Lemma respects_cont l s1 s2: (c_concrete.cont_trans' _ l s1 s2) ->
    In (select_region s2) (cont_trans l (select_region s1)).
  Proof with auto with real.
    unfold c_concrete.cont_trans. simpl c_abstract.cont_trans.
    intros.
    unfold cont_trans.
    destruct H. destruct H.
    apply (snd (filter_In
      (cont_trans_b l (select_region s1)) (select_region s2) regions)).
    split. apply regions_complete.
    unfold cont_trans_b.
    destruct (cont_decider (@pair Location (prod Region Region) l
      (@pair Region Region (select_region s1) (select_region s2))))...
    elimtype False. apply n. clear n.
    unfold cont_trans_cond.
    simpl @fst. simpl @snd.
    exists s1. exists s2.
    split.
      apply regions_cover_invariants with l.
      rewrite c_concrete.curry_inv.
      rewrite <- (flow_zero (c_concrete.flow conc_sys l) s1).
      apply H.
        apply CRle_refl.
      destruct x... simpl.
      apply (CRnonNeg_le_zero x)...
    split.
      apply regions_cover_invariants with l.
      rewrite c_concrete.curry_inv.
      rewrite <- H0.
      apply H.
        destruct x... simpl. apply (CRnonNeg_le_zero x)...
      apply CRle_refl.
    unfold c_concrete.cont_trans.
    simpl.
    split...
    exists x...
  Defined.

  Definition cont_trans' (l: Location) (r: Region):
    { r': list Region | forall p q, select_region p = r ->
            c_concrete.cont_trans' _ l p q -> In (select_region q) r' }.
  Proof.
    intros. exists (filter (cont_trans_b l r) regions).
    intros. subst. apply (respects_cont H0).
  Defined.

  Definition disc_trans' (l: Location) (r: Region):
    { r': list (Location * Region) | forall p q, select_region p = r ->
       c_concrete.disc_trans (l, p) q -> In (fst q, select_region (snd q)) r' }.
  Proof.
    intros. exists (disc_trans (l, r)). intros. 
    subst. apply (respects_disc H0).
  Defined.

  Lemma NoDup_cont_trans l r: NoDup (cont_trans l r).
  Proof. unfold cont_trans. auto. Qed.

  Lemma NoDup_disc_trans' l r: NoDup (proj1_sig (disc_trans' l r)).
  Proof with auto.
    intros. simpl. apply NoDup_filter. apply c_abstract.NoDup_states...
  Qed.

  (* Et voila: *)

  Definition abstract_system: c_abstract.System conc_sys :=
    c_abstract.Build_System Region_eq_dec regions_complete
     NoDup_regions select_region initial disc_trans'
     NoDup_disc_trans' cont_trans' NoDup_cont_trans.

End contents.
