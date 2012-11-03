Set Automatic Coercions Import.

Require Import List Bool.
Require Import util list_util stability containers.
Require Import CSetoids.
Require Import Morphisms.
Set Implicit Arguments.
Require Import EquivDec.
Require concrete.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import hybrid.vector_setoid.
Require hybrid.nat_util.
Require Import hybrid.hlist_aux.

Module c := concrete.

Section contents.

  Variable chs: concrete.System.

  Record Space: Type :=
    { Region: Type
    ; Region_eq_dec: EquivDec.EqDec Region eq
    ; regions: ExhaustiveList Region
    ; NoDup_regions: NoDup regions
    ; in_region: Container (concrete.Point chs) Region
    ; in_region_mor: Proper (@cs_eq _ ==> eq ==> iff) in_region
    ; regions_cover: forall l p, c.invariant (l, p) -> DN (sig (in_region p))
    }.

  Existing Instance in_region.
  Existing Instance Region_eq_dec.
  Existing Instance regions.
  Existing Instance in_region_mor.

  Section space_derivatives.

    Variable p: Space.

    Definition State := (concrete.Location chs * Region p)%type.

    Definition region: State -> Region p := snd.
    Definition location: State -> c.Location chs := fst.

    Definition states: ExhaustiveList State := @ExhaustivePairList (concrete.Location chs) (Region p) _ _.

    Lemma NoDup_states: NoDup (regions p) -> NoDup states.
    Proof. apply NoDup_ExhaustivePairList, c.NoDup_locations. Qed.

  End space_derivatives.

  (* Given two sets of abstraction parameters, we can combine these to make
   finer-grained abstraction parameters where each region corresponds to the
   intersection of two regions of the respective abstraction parameters.

   For instance, for a hybrid system whose continuous state space is the plane,
   we could first define abstraction parameters with regions corresponding to X
   intervals, then define abstraction parameters with regions corresponding to
   Y intervals, and then finally combine these using param_prod below to
   produce abstraction parameters with regions corresponding to squares. *)

  Section prod_space.

    Variables ap ap': Space.

    Let in_region p r := in_region ap p (fst r) /\ in_region ap' p (snd r).

    Let in_region_mor: Proper (@cs_eq _ ==> eq ==> iff) in_region.
    Proof. unfold in_region. intros x x' e r r' e'. rewrite e, e'. split; auto. Qed.

    Program Definition regions_cover_prod l p : concrete.invariant (l, p) -> DN (sig (in_region p)) :=
      fun H => 
        C1 <- contents.regions_cover ap l p H;
        C2 <- contents.regions_cover ap' l p H;
        return [=(`C1, `C2)=].
    Next Obligation.
      split; crunch.
    Qed.

    Definition prod_space: Space := Build_Space _ _
      (NoDup_ExhaustivePairList (NoDup_regions ap) (NoDup_regions ap'))
      in_region_mor regions_cover_prod.

  End prod_space.

  (* We generalize the product space above from 2 to arbitrary 'n' dimensions,
     hence generalizing abstraction by squares in 2 dimensional space to 
     abstraction by hyper-cubes in n-dimensional space *)

  Section hyper_space.

    Variable n : nat.
    Variable aps : list Space.

    (* [Regions] is formed by an n-product of [Region]s of respective [Space]s,
       epxressed with heterogenous list *)
    Notation Regions aps := (@hlist _ Region aps).

    Fixpoint in_region_aux (aps : list Space) (p : concrete.Point chs) : Regions aps -> Prop :=
      match aps as aps return Regions aps -> Prop with
      | [] => fun _ => True
      | s::ss => fun rs =>
          in_region s p (hhd rs) /\ @in_region_aux ss p (htl rs)
      end.

    Obligation Tactic := crunch.

    Program Fixpoint regions_cover_aux (aps : list Space) l p : 
      concrete.invariant (l, p) -> DN (sig (@in_region_aux aps p)) :=
      match aps with
      | [] => fun H => return [= HNil (H:=_) =]
      | s::ss => fun H =>
          C1 <- contents.regions_cover s l p H;
          C2 <- @regions_cover_aux ss l p H;
          return [= `C1:::`C2 =]
      end.

    Lemma in_region_aux_morph : Proper (@st_eq _ ==> eq ==> iff) (@in_region_aux aps).
    Proof with auto.
      repeat intro.
      subst.
      induction aps. firstorder.
      split; intros [H0 H1]; split.
            apply (in_region_mor a x y H (refl_equal _))...
          apply IHl...
        apply (in_region_mor a x y H (refl_equal _))...
      apply IHl...
    Qed.

    Obligation Tactic := program_simpl; auto with typeclass_instances.

    Hint Resolve NoDup_regions.

    Program Definition hyper_space : Space := @Build_Space (Regions aps) _ _ _ 
      (@in_region_aux aps) in_region_aux_morph (@regions_cover_aux aps).
    Next Obligation.
      set (w := NoDup_ExhaustiveHList); simpl in w; apply w; auto.
    Qed.

  End hyper_space.

  Variable ap: Space.

  Instance abs: Container (c.State chs) (State ap) := fun s s' =>
    c.location s = location s' /\ c.point s ∈ region s'.

  Hint Unfold abs.

  Section CoverRelandsuch.

    Context `{Container (c.State chs) C} `{Container (State ap) D} (cs: C) (ss: D).

    Definition CompleteCover: Prop := forall s: c.State chs, s ∈ cs -> forall r: State ap, s ∈ r -> r ∈ ss.
    Definition SharedCover: Prop := forall s: c.State chs, s ∈ cs -> DN (exists r: State ap, s ∈ r /\ r ∈ ss).

  End CoverRelandsuch.

  Definition CompleteCoverList (cs: c.State chs -> Prop): Type :=
    sig (LazyProp ∘ (CompleteCover cs: list (State ap) -> Prop)).

  Section safe.

    (* We're looking for a set of abstract states... *)

    Variables (reachable: State ap -> Prop)

    (* ... that together cover concretely reachable states in a shared manner: *)

      (reachable_respect: SharedCover concrete.reachable reachable).

    (* Because then, abstract unreachability implies concrete unreachability *)

    Lemma safe (s: concrete.State chs): (forall s', s ∈ s' -> ~ reachable s') -> ~ concrete.reachable s.
    Proof with eauto.
      unfold not.
      intros.
      apply DN_free, (DN_bind (reachable_respect H0))...
      intros [s' [H1 H2]]...
    Qed.

    (* And consequently, if abstract reachability is overestimatable, reachability of an
     overestimatable concrete set is overestimatable: *)

    Hint Unfold intersection overlap nonempty.

    Context
      `(forall s, overestimation (reachable s))
      (cstates: concrete.State chs -> Prop)
      (astates: CompleteCoverList cstates).

    Program Definition some_reachable_1: overestimation (overlap cstates concrete.reachable) :=
      @overestimate (exists u, In u (proj1_sig astates) /\ reachable u) overestimate.

    Next Obligation. Proof with eauto.
      intros [x [Px r]].
      apply (@safe x)...
      repeat intro.
      apply (@overestimation_false (exists u, In u (proj1_sig astates) /\ reachable u) _ H0)...
        (* todo: ugly *)
      destruct astates.
      pose proof (c ())...
    Qed.

  End safe.

  Definition cont_trans (l: c.Location chs): relation (Region ap)
    := fun r r' => exists p q, p ∈ r /\ q ∈ r' /\ c.can_flow chs l p q.

  Definition sharing_transition_overestimator (R: relation (concrete.State chs)): Type :=
    forall s: State ap, sig (fun l: list (State ap) => LazyProp (NoDup l /\
      SharedCover (concrete.invariant ∩ (overlap s ∘ util.flip R)) l)).
        (* the invariant part is important because it means the overestimators can use
         regions_cover in their correctness proofs (which we do actually need) *)

  (* We define abstract versions of initiality, invariance, and guards, suitable
   as overestimation predicates. *)

  Definition Initial: State ap -> Prop := overlap (@concrete.initial chs).
  Definition invariant: State ap -> Prop := overlap (@concrete.invariant chs).

  Definition guard (l: concrete.Location chs) (r: Region ap) (l': concrete.Location chs): Prop
    := exists p, p ∈ r /\ concrete.guard _ (l, p) l'.

  Record System: Type :=
    { initial_dec: overestimator (overlap (@concrete.initial chs))
    ; disc_trans_over: sharing_transition_overestimator (@concrete.disc_trans _)
    ; cont_trans_over: sharing_transition_overestimator (@concrete.cont_trans _)
    }.

  Variable ahs: System.

  Definition trans (b: bool): relation (State ap) :=
    fun s1 s2 => s2 ∈ if b then proj1_sig (cont_trans_over ahs s1) else proj1_sig (disc_trans_over ahs s1).

  Definition reachable (s: State ap): Prop :=
    exists is: State ap,
      overestimation_bool (initial_dec ahs is) = true /\ alternate trans is s.

  Hint Unfold Initial predicate_container containers.intersection In.

  Lemma reachable_alternating_concrete_abstract (i s: c.State chs):
    concrete.initial i -> forall b, end_with (@concrete.trans_kind chs) b i s ->
      DN (exists is, overestimation_bool (initial_dec ahs is) = true /\
        exists s', s ∈ s' /\ end_with trans (negb b) is s').
  Proof with eauto; auto 20.
    intros H b H0.
    induction H0 as [| b i (l, p) H0 IH [l' p']].
      destruct s as [l cp].
      apply (DN_fmap (regions_cover ap l cp (concrete.invariant_initial chs _ H))).
      intros [x i].
      exists (l, x).
      split.
        apply overestimation_true.
        exists (l, cp).
        auto 20.
      exists (l, x)...
    apply (DN_bind (IH H)).
    intros [ir [H2 [[al r] [[H3 H5] H4]]]]. clear IH.
    apply (DN_exists (x := ir)).
    apply (DN_liftM2 (@conj _ _))...
    simpl in H3. subst.
    cut (DN (exists r0, In p' r0 /\ trans (negb b) (al, r) (l', r0))).
      intros.
      apply (DN_fmap H3).
      intros [x [H6 H7]].
      exists (l', x).
      eauto 30.
    destruct b; simpl in H0 |- *.
      unfold trans.
      destruct (disc_trans_over ahs (al, r)).
      simpl.
      destruct l...
      unfold SharedCover in H6.
      unfold In at 1 in H6.
      unfold predicate_container in H6.
      simpl in H1.
      cut (DN (exists r: State ap, In (l', p') r /\ In r x)).
        intro.
        apply (DN_fmap H7).
        intro.
        destruct H8.
        destruct H8.
        exists (region x0).
        destruct H8.
        split...
        destruct x0.
        simpl in H8. subst...
      apply H6.
      split...
        destruct H1. intuition.
      exists (al, p)...
    unfold trans.
    destruct cont_trans_over.
    simpl.
    destruct l...
    unfold SharedCover, In, predicate_container in H6.
    simpl in H1.
    cut (DN (exists r : State ap, (l', p') ∈ r /\ r ∈ x)).
      intro.
      apply (DN_fmap H7). clear H7.
      intros [x0 [[H7 H9] H8]].
      exists (region x0).
      split...
      simpl in H7. subst.
      destruct x0...
    apply H6.
    split.
      apply concrete.reachable_invariant.
      apply -> concrete.alternating_reachable.
      hnf.
      exists i.
      split...
      unfold alternate.
      exists false.
      eauto.
    exists (al, p)...
  Qed.

  Hint Unfold alternate.

  Lemma reachable_respect: SharedCover concrete.reachable reachable.
  Proof.
    unfold SharedCover.
    intros.
    apply concrete.alternating_reachable in H.
    destruct H as [s' [H0 [x0 H1]]].
    apply (DN_fmap (@reachable_alternating_concrete_abstract s' s H0 x0 H1)).
    intros [x [y [A [B C]]]].
    unfold reachable.
    eauto 10.
  Qed.

  Definition some_reachable_2 := @some_reachable_1 reachable reachable_respect.

End contents.

Existing Instance in_region.
Existing Instance Region_eq_dec.
Existing Instance regions.
Existing Instance in_region_mor.
