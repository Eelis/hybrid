Require Import List.
Require Import dec_overestimator.
Require Import c_util.
Require Import list_util.
Require Import CSetoids.
Require Import CRreal.
Require Import flow.
Require concrete.
Require abstract.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section contents.

  Context
    {Region: Set}
    {Region_eq_dec: EquivDec.EqDec Region eq}
    {regions: ExhaustiveList Region}.

  Variables
    (conc_sys : concrete.System)
    (in_region : concrete.Point conc_sys -> Region -> Prop)
    (in_region_wd: forall x x', x [=] x' -> forall r, in_region x r -> in_region x' r)
    (NoDup_regions : NoDup (@exhaustive_list _ regions)).

  Let Location := concrete.Location conc_sys.
  Let Point := concrete.Point conc_sys.
  Let c_State := concrete.State conc_sys.
  Let State := (Location * Region)%type.

  Variables
    (select_region: Point -> Region)
    (select_region_wd: forall x x', x [=] x' -> select_region x = select_region x')
    (select_region_correct: forall x, concrete.invariant x -> in_region (snd x) (select_region (snd x))).
      (* select_region does not have to be constructive, because it is only
       used in the correctness proof. *)

  Hint Resolve select_region_correct.

  Definition initial_condition (s : State) : Prop :=
    let (l, r) := s in
      exists p, in_region p r /\ concrete.initial (l, p).

  Definition cont_trans_cond (w : Location * (Region * Region)) : Prop :=
    let (l, r) := w in
    let (r1, r2) := r in
      exists p, exists q,
        in_region p r1 /\ in_region q r2 /\ concrete.cont_trans (l, p) (l, q).

  Definition disc_trans_cond (s : State * State): Prop :=
    let (s1, s2) := s in
    let (l1, r1) := s1 in
    let (l2, r2) := s2 in
      exists p, exists q,
        in_region p r1 /\ in_region q r2 /\ concrete.disc_trans (l1, p) (l2, q).

  (* this condition is no good, because it forces transitions to adjacent
   regions in reset=id cases *)

  Variables
    (cont_do : dec_overestimator cont_trans_cond)
    (disc_do : dec_overestimator disc_trans_cond)
    (initial_do : dec_overestimator initial_condition).

  Definition Hint (l: Location) (r r': Region): Set :=
    forall p, in_region p r ->
      forall t, '0 <= t -> in_region (concrete.flow conc_sys l p t) r' ->
        in_region (concrete.flow conc_sys l p t) r.

  Definition AltHint (l: Location) (r r': Region): Set :=
    (forall p: Point,
      in_region p r ->
      forall t: Time,
      in_region (concrete.flow conc_sys l p t) r' -> t <= '0).

  Lemma dealt_hint l r r': AltHint l r r' -> Hint l r r'.
  Proof with auto.
    repeat intro.
    set (H p H0 _ H2). clearbody c. clear H.
    set (snd (CRle_def t ('0)) (conj c H1)). clearbody s.
    apply in_region_wd with p...
    simpl bsm.
    transitivity (concrete.flow conc_sys l p ('0)).
      symmetry.
      apply flow_zero.
    destruct (concrete.flow conc_sys l).
    simpl.
    apply bsm_wd...
    symmetry...
  Qed.

  Variable hints: forall (l: Location) (r r': Region), r <> r' -> option (Hint l r r').

  Definition dealt_hints (H: forall l r r', r <> r' -> option (AltHint l r r')) l r r' (E: r <> r'): option (Hint l r r') :=
    option_map (@dealt_hint l r r') (H l r r' E).

  Definition hints' (l: Location) (r r': Region):
    option (forall p, in_region p r ->
     forall t, '0 <= t -> in_region (concrete.flow conc_sys l p t) r' ->
       in_region (concrete.flow conc_sys l p t) r) :=
    match Region_eq_dec r r' with
    | left _ => None
    | right E => hints l E
    end.

  (* Using these, we can define the abstract transitions.. *)

  Let cont_trans_b (s : State) (r_dst : Region) : bool :=
    let (l, r_src) := s in
    (do_pred cont_do) (l, (r_src, r_dst)) &&
    negb (hints' l r_src r_dst).

  Let disc_trans_b (s1 s2 : State): bool :=
    (do_pred disc_do) (s1, s2).

  Definition RegionsCoverInvariants : Prop :=
    forall l p, concrete.invariant (l, p) ->
      in_region p (select_region p).

  Variable regions_cover_invariants : RegionsCoverInvariants.

  Definition initial_prop (s : State) :=
    let (l, r) := s in
      exists p, in_region p r /\ concrete.initial (l, p).

  Definition initial_dec (s : State) :=
    let (l, r) := s in
      do_pred initial_do (l, r).

  Lemma over_initial : initial_dec >=> initial_prop.
  Proof with auto.
    intros s init ips. destruct s.
    apply (do_correct initial_do (l, r))...
  Qed.

  Definition disc_trans (s : State) : list State :=
    filter (disc_trans_b s) (abstract.states conc_sys).
      (* a more efficient implementation would grow the graph *)

  Lemma NoDup_disc_trans s : NoDup (disc_trans s).
  Proof with auto.
    intro. apply NoDup_filter. apply abstract.NoDup_states...
  Qed.

  Lemma respects_disc (s1 s2 : c_State) :
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
    concrete.disc_trans s1 s2 ->
    forall r1, in_region p1 r1 ->
    exists r2, in_region p2 r2 /\
    In (l2, r2) (disc_trans (l1, r1)).
  Proof with auto.
    intros [l1 p1] [l2 p2] dt r1 inr1.
    exists (select_region p2).
    split.
      destruct dt.
      apply (select_region_correct (l2, p2)).
      intuition.
    apply in_filter...
    set (s1 := (l1, select_region p1)). set (s2 := (l2, select_region p2)).
    apply do_over_true.
    destruct dt as [guard [reset [inv1 inv2]]].
    exists p1. exists p2. 
    repeat split; solve 
      [ hyp 
      | simpl; eapply regions_cover_invariants; eassumption].
  Qed.

  Add Morphism (concrete.inv_curried conc_sys)
    with signature (@eq _) ==> (@cs_eq _) ==> iff
    as inv_mor.
  Proof.
    intros. apply concrete.invariant_wd; trivial.
  Qed.

  Definition cont_trans (s : State) : list Region :=
    filter (cont_trans_b s) regions.

  Lemma cont_refl l r p: in_region p r -> concrete.invariant (l, p) -> In r (cont_trans (l, r)).
  Proof with auto.
    intros.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply do_over_true.
      simpl.
      exists p. exists p.
      repeat split...
      unfold concrete.cont_trans'.
      exists NonNegCR_zero.
      split.
        intros.
        simpl.
        rewrite concrete.curry_inv.
        assert (concrete.flow conc_sys l p t [=] p).
          transitivity (concrete.flow conc_sys l p ('0))...
            set (concrete.flow conc_sys l).
            clearbody f .
            destruct f.
            simpl.
            destruct flow_morphism.
            simpl.
            apply bsm_wd...
            symmetry.
            apply (snd (CRle_def ('0) t)).
            split...
          apply flow_zero.
        rewrite H3...
      simpl.
      rewrite flow_zero...
    simpl.
    unfold hints'.
    destruct (Region_eq_dec r r)...
    elimtype False.
    intuition.
  Qed.

  Lemma respects_cont l s1 s2 :
    concrete.cont_trans' _ l s1 s2 ->
    forall r1, in_region s1 r1 ->
    exists r2, in_region s2 r2 /\ In r2 (cont_trans (l, r1)).
  Proof with auto with real.
    intros l s1 s2 [t [inv flow]] r1 inr1.
    set (r2 := select_region s2).
    case_eq (hints' l r1 r2); intros.
      clear H.
      exists r1.
      split.
        apply in_region_wd with (concrete.flow conc_sys l s1 (`t))...
        apply i...
          apply -> CRnonNeg_le_zero...
        subst r2.
        apply in_region_wd with s2.
          symmetry...
        apply (select_region_correct (l, s2)).
        rewrite concrete.curry_inv.
        rewrite <- flow.
        apply inv...
        apply -> CRnonNeg_le_zero...
      apply cont_refl with s1...
      rewrite concrete.curry_inv.
      rewrite <- (flow_zero (concrete.flow conc_sys l) s1).
      apply inv...
      apply -> CRnonNeg_le_zero...
    exists r2.
    split.
      apply (select_region_correct (l, s2)).
      rewrite concrete.curry_inv.
      rewrite <- flow.
      apply inv...
      apply -> CRnonNeg_le_zero...
    unfold cont_trans.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply do_over_true.
      exists s1. exists s2.
      split...
      split.
        apply regions_cover_invariants with l.
        rewrite concrete.curry_inv.
        rewrite <- flow.
        apply inv...
        apply -> CRnonNeg_le_zero...
      eauto 10.
    rewrite H...
  Qed.

  Lemma NoDup_cont_trans s : NoDup (cont_trans s).
  Proof. unfold cont_trans. auto. Qed.

  Lemma regions_cover_invariant l p: concrete.invariant (l, p) -> exists r, in_region p r.
  Proof with auto.
    intros.
    exists (select_region p).
    apply (select_region_correct (l, p))...
  Qed.

  Program Definition abstract_system : abstract.System conc_sys :=
    abstract.Build_System Region_eq_dec regions
     NoDup_regions in_region regions_cover_invariant over_initial disc_trans
     NoDup_disc_trans respects_disc cont_trans NoDup_cont_trans respects_cont.

  Variable disc_trans': @abstract.State conc_sys Region -> list (@abstract.State conc_sys Region).
  Variable NoDup_disc_trans': forall s : @abstract.State conc_sys Region, NoDup (disc_trans' s).
  Variable respects_disc': forall s1 s2 : concrete.State conc_sys,
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
      concrete.disc_trans s1 s2 ->
      forall r1, in_region p1 r1 ->
      exists r2, in_region p2 r2 /\
      In (l2, r2) (disc_trans' (l1, r1)).

  Program Definition abstract_system': abstract.System conc_sys :=
    abstract.Build_System Region_eq_dec regions
     NoDup_regions in_region regions_cover_invariant over_initial disc_trans' NoDup_disc_trans'
     respects_disc' cont_trans NoDup_cont_trans respects_cont.

End contents.
