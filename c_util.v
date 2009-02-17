Require Import util.
Require Export CRsign.
Require Export CRln.

Set Implicit Arguments.
Open Local Scope CR_scope.

Inductive weak_decision P := 
  | definitely: P -> weak_decision P
  | definitely_not: Not P -> weak_decision P
  | indeterminate: weak_decision P.

Definition weak_and_dec (A B: Prop):
  weak_decision A -> weak_decision B -> weak_decision (A /\ B).
Proof.
  intros.
  destruct H.
      destruct H0.
          apply definitely.
          split; assumption.
        apply definitely_not.
        intro. apply n. destruct H. assumption.
      apply indeterminate.
    apply definitely_not.
    intro. apply n. destruct H. assumption.
  destruct H0.
      apply indeterminate.
    apply definitely_not.
    intro. apply n. destruct H. assumption.
  apply indeterminate.
Defined.

Definition weak_decision_to_opt_neg (A: Prop) (d: weak_decision A): option (~ A) :=
  match d with
  | definitely_not p => Some p
  | _ => None
  end.

Lemma CRadd_0_r x: x + '0 == x.
  intros.
  rewrite (Radd_comm CR_ring_theory).
  apply (Radd_0_l CR_ring_theory).
Defined. (* todo: generalize to arbitrary ring. *)

Lemma add_both_sides x y: x == y -> forall z, x+z == y+z.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma diff_zero_eq x y: x - y == '0 -> x == y.
Proof.
  intros.
  set (add_both_sides H y).
  rewrite (Radd_0_l CR_ring_theory) in m.
  rewrite <- (Radd_assoc CR_ring_theory) in m.
  rewrite (Radd_comm CR_ring_theory (-y)) in m.
  rewrite (Ropp_def CR_ring_theory) in m.
  rewrite (Radd_comm CR_ring_theory) in m.
  rewrite (Radd_0_l CR_ring_theory) in m.
  assumption.
Qed.

Lemma CRminus_zero x: x - '0 == x.
Proof with auto.
  intros.
  rewrite CRopp_Qopp.
  replace ((-0)%Q) with 0...
  rewrite (Radd_comm CR_ring_theory).
  apply (Radd_0_l CR_ring_theory).
Qed.

Lemma inject_Q_le x y: (x <= y)%Q -> 'x <= 'y.
Proof. intros. apply (CRle_Qle x y). assumption. Qed.

Lemma CRnonNeg_nonPos x: CRnonNeg x -> CRnonPos (-x).
  unfold CRnonNeg.
  unfold CRnonPos.
  intros.
  simpl.
  rewrite <- (Qopp_opp e).
  apply Qopp_le_compat.
  apply H.
Qed.

Lemma CRnonNeg_le_zero x: CRnonNeg x <-> '0 <= x.
Proof with auto.
  unfold CRle.
  split; intro; apply (CRnonNeg_wd (CRminus_zero x))...
Qed. 

Lemma CRnonNeg_zero: CRnonNeg ('0).
Proof. apply (CRnonNeg_le_zero ('0)). apply CRle_refl. Qed.
  (* a much more direct proof should be possible, but we don't care,
   because this is in Prop, anyway. *)

Lemma t3: Setoid_Theory CR (@ms_eq _).
  unfold Setoid_Theory.
  apply (CSetoid_eq_Setoid (csg_crr CRasCField)).
Defined.

Lemma diff_opp x y: x - y == -(y - x).
  set (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
  intros.
  rewrite m.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite m0.
  apply (Radd_comm CR_ring_theory).
Qed.

Lemma QposAsQ_Qpos_plus x y: QposAsQ (Qpos_plus x y) = (QposAsQ x + QposAsQ y)%Q.
  reflexivity.
Qed.

Lemma CRle_le_eq x y: x <= y -> y <= x -> x == y.
Proof with auto.
  unfold CRle.
  intros.
  set (CRnonNeg_nonPos H0).
  clearbody c.
  assert (CRnonPos (y - x)).
    rewrite diff_opp.
    assumption.
  clear c. clear H0.
  symmetry.
  apply diff_zero_eq.
  unfold ms_eq.
  simpl.
  apply regFunEq_e.
  unfold CRnonNeg in H. unfold CRnonPos in H1.
  intros.
  simpl approximate at 2.
  unfold ball.
  unfold Qmetric.Q_as_MetricSpace at 1.
  unfold Qmetric.Qball.
  unfold Qminus.
  replace ((-0)%Q) with 0...
  rewrite (Radd_comm Qsrt).
  rewrite (Radd_0_l Qsrt).
  set (H e). set (H1 e). clearbody q q0. clear H H1.
  unfold AbsSmall.
  set (@approximate Qmetric.Q_as_MetricSpace (y - x)%CR e) in *.
  clearbody m.
  simpl.
  assert ((e <= (e + e)%Qpos)%Q).
    rewrite QposAsQ_Qpos_plus.
    apply Qle_trans with ((e + 0)%Q).
      rewrite (Radd_comm Qsrt).
      rewrite (Radd_0_l Qsrt).
      apply Qle_refl.
    apply Qplus_le_compat.
      apply Qle_refl.
    apply Qpos_nonneg.
  split.
    apply Qle_trans with ((-e)%Q)...
    apply Qopp_le_compat.
    assumption.
  apply Qle_trans with e...
Qed.

Lemma CRlt_le x y: x < y -> x <= y.
Proof.
  intros.
  destruct (def_leEq _ _ _ _ _ CRisCOrdField x y).
  apply H1.
  intro.
  destruct (ax_less_strorder _ _  _ _ _ CRisCOrdField).
  apply (so_asym x y); assumption.
Qed.

Lemma t1 (x y z: CR): x < y -> x+z < y+z.
Proof.
  set (ax_plus_resp_less _ _ _ _ _ CRisCOrdField).
  simpl in c.
  intros.
  apply c.
  assumption.
Defined.

Lemma t1_rev (x y z: CR): x < y -> z+x < z+y.
Proof.
  intros.
  apply (CRlt_wd (Radd_comm CR_ring_theory x z) (Radd_comm CR_ring_theory y z)).
    (* todo: why won't setoid rewrites work here? *)
  apply t1.
  assumption.
Qed.

Lemma t4 (q: Qpos): '0 <= 'q.
Proof.
  intros.
  destruct (CRle_Qle 0 q).
  apply H0.
  apply Qpos_nonneg.
Defined.

Lemma Qadd_both_sides x y: (x == y -> forall z, x+z == y+z)%Q.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Qbla (x y: Q): (-(x * y) == -x * y)%Q.
  intros.
  symmetry.
  rewrite <- (Qplus_0_l (-(x * y))).
  rewrite <- (Qplus_0_l (-x * y)).
  rewrite <- (Qplus_opp_r (x * y)) at 1.
  rewrite <- Qplus_assoc.
  rewrite (Qplus_comm (-(x*y))).
  rewrite Qplus_assoc.
  apply Qadd_both_sides.
  rewrite <- Qmult_plus_distr_l.
  rewrite Qplus_opp_r.
  apply Qmult_0_l.
Qed.

Lemma Qpositive_ne_0 (x: positive): ~(x == 0)%Q.
Admitted.

Lemma Qbla4 (x: positive): (x # x == 1)%Q.
  intros.
  unfold pos2Z.
  rewrite Qmake_Qdiv.
  apply Qmult_inv_r.
  apply Qpositive_ne_0.
Qed.

Lemma Qhalves_add_to_1: ((1#2) + (1#2) == 1)%Q.
Proof. compute. reflexivity. Qed.

Lemma t10 (x y: CR): CRnonNeg x -> CRnonNeg y -> CRnonNeg (x + y).
Proof with auto.
  unfold CRnonNeg.
  intros.
  simpl.
  unfold Cap_raw.
  simpl.
  apply Qle_trans with ((-((1#2)*e)%Qpos + -((1#2)*e)%Qpos)%Q).
    rewrite Q_Qpos_mult.
    rewrite Qbla.
    rewrite <- Qmult_plus_distr_l.
    rewrite <- Qopp_plus.
    rewrite Qhalves_add_to_1.
    rewrite <- Qbla.
    rewrite Qmult_1_l.
    apply Qle_refl.
  apply Qplus_le_compat...
Qed.

Lemma t11 x y: y == x + (y - x).
  intros.
  rewrite (Radd_comm CR_ring_theory y).
  rewrite (Radd_assoc CR_ring_theory).
  rewrite (Ropp_def CR_ring_theory).
  symmetry.
  apply (Radd_0_l CR_ring_theory).
Qed.

Lemma t9 (x y x' y': CR): x <= x' -> y <= y' -> x+y <= x'+y'.
Proof with auto.
  unfold CRle.
  intros.
  rewrite <- (Radd_assoc CR_ring_theory x').
  rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3
    CR_ring_eq_ext CR_ring_theory ).
  rewrite (Radd_assoc CR_ring_theory y').
  rewrite (Radd_comm CR_ring_theory y').
  rewrite <- (Radd_assoc CR_ring_theory (-x)).
  rewrite (Radd_assoc CR_ring_theory x').
  apply t10...
Qed.

Lemma t2 (x y z: CR): x <= y -> x+z <= y+z.
Proof.
  unfold CRle.
  intros.
  set (@Ropp_add CR ('0) ('1) (ucFun2 CRplus)
    CRmult (fun x y : CR => x - y) CRopp (@ms_eq CR) t3
    CR_ring_eq_ext CR_ring_theory ).
  rewrite <- (Radd_assoc CR_ring_theory y).
  rewrite (Radd_comm CR_ring_theory x).
  rewrite m.
  rewrite (Radd_assoc CR_ring_theory z).
  rewrite (Ropp_def CR_ring_theory).
  rewrite (Radd_0_l CR_ring_theory).
  assumption.
Qed.

Lemma t8 x y: x <= y -> -y <= -x.
Proof.
  unfold CRle.
  intros.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite m.
  rewrite (Radd_comm CR_ring_theory).
  assumption.
Defined.

Lemma CRlt_opp_compat x y: x < y -> -y < -x.
  unfold CRlt.
  unfold CRpos.
  intros.
  destruct H.
  exists x0.
  rewrite (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite (Radd_comm CR_ring_theory).
  assumption.
Defined.

Lemma t12 x y: -x <= y -> -y <= x.
Proof.
  intros.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory x).
  rewrite <- m.
  apply t8.
  assumption.
Qed.

Lemma t6 x y: CRneg (x - y) -> CRpos (y - x).
Proof.
  unfold CRpos, CRneg, CRle.
  intros.
  destruct H.
  exists x0.
  rewrite CRopp_Qopp.
  rewrite (Radd_comm CR_ring_theory).
  set (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite m in c.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite m0 in c.
  rewrite (Radd_comm CR_ring_theory y).
  assumption.
Defined.

Definition weak_CRlt_decision (f: (CR -> CR -> Set) -> Set): Set :=
  option (sum (f CRlt) (f (fun x y => y < x))).

Definition weak_CRle_decision (f: (CR -> CR -> Prop) -> Prop): Set :=
  option ({f CRle}+{f (fun x y => y <= x)}).

Definition NonNegCR: Type := sigT CRnonNeg.

Definition NonNegCR_plus (n n': NonNegCR): NonNegCR :=
  let (r, p) := n in let (r', p') := n' in existT _ (r + r') (t10 p p').

Definition NonNegCR_zero: NonNegCR := existT _ _ CRnonNeg_zero.

Axiom CR_lt_eq_dec: forall (x y: CR), sum (x==y) (sum (x<y) (y<x)).
(* hm, if we make this a {x<=y}+{y<=x} axiom, we can be sure it won't be used in
 computation, because that's in prop, no? it may not be enough for
 our proofs though.. *)

Lemma CR_le_le_dec x y: {x<=y}+{y<=x}.
  intros.
  destruct (CR_lt_eq_dec x y).
    left. rewrite m. apply CRle_refl.
  destruct s; [left | right]; apply CRlt_le; assumption.
Defined.

Section function_properties.

  Variable f: CR -> CR.
  Variable f_wd: forall x x', x == x' -> f x == f x'.

  Definition strongly_increasing: CProp :=
    forall x x', x < x' -> f x < f x'.
  Definition strongly_decreasing: CProp :=
    forall x x', x < x' -> f x' < f x.

  Definition increasing: CProp :=
    forall x x', x <= x' -> f x <= f x'.
  Definition decreasing: CProp :=
    forall x x', x <= x' -> f x' <= f x.

  Lemma strongly_increasing_inv:
    strongly_increasing -> forall x x', f x < f x' -> x < x'.
  Proof with auto.
    unfold strongly_increasing.
    intros.
    destruct (CR_lt_eq_dec x x').
      elimtype False.
      destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x') (f x)).
      apply H0...
      rewrite (f_wd m).
      apply CRle_refl.
    destruct s...
    destruct (ax_less_strorder _ _  _ _ _ CRisCOrdField).
    elimtype False.
    apply (so_asym (f x) (f x') H).
    apply X...
  Qed.

  Lemma strongly_increasing_inv_mild:
    strongly_increasing -> forall x x', f x <= f x' -> x <= x'.
  Proof with auto.
    unfold strongly_increasing.
    intros.
    destruct (CR_lt_eq_dec x x').
      rewrite m.
      apply CRle_refl.
    destruct s.
      apply CRlt_le...
    elimtype False.
    destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x) (f x')).
    apply H0...
    apply X...
  Qed.

  Lemma strongly_decreasing_inv:
    strongly_decreasing -> forall x x', f x < f x' -> x' < x.
  Proof with auto.
    unfold strongly_decreasing.
    intros.
    destruct (CR_lt_eq_dec x x').
      elimtype False.
      destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x') (f x)).
      apply H0...
      rewrite (f_wd m).
      apply CRle_refl.
    destruct s...
    destruct (ax_less_strorder _ _  _ _ _ CRisCOrdField).
    elimtype False.
    apply (so_asym (f x) (f x') H).
    apply X...
  Qed.

  Lemma strongly_decreasing_inv_mild:
    strongly_decreasing -> forall x x', f x <= f x' -> x' <= x.
  Proof with auto.
    unfold strongly_increasing.
    intros.
    destruct (CR_lt_eq_dec x x').
      rewrite m.
      apply CRle_refl.
    destruct s.
      elimtype False.
      destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x) (f x')).
      apply H0...
      apply X...
    apply CRlt_le...
  Qed.

  Lemma mildly_increasing:
    strongly_increasing -> forall x x', x <= x' -> f x <= f x'.
  Proof with auto.
    intros.
    destruct (CR_lt_eq_dec x x').
      rewrite (f_wd m).
      apply CRle_refl.
    destruct s.
      apply CRlt_le...
    elimtype False.
    destruct (def_leEq _ _ _ _ _ CRisCOrdField x x').
    apply H0...
  Qed. (* todo: i'm not convinced CR_lt_eq_dec is needed for this *)

  Lemma mildly_decreasing:
    strongly_decreasing -> forall x x', x <= x' -> f x' <= f x.
  Proof with auto.
    intros.
    destruct (CR_lt_eq_dec x x').
      rewrite (f_wd m).
      apply CRle_refl.
    destruct s.
      apply CRlt_le...
    elimtype False.
    destruct (def_leEq _ _ _ _ _ CRisCOrdField x x').
    apply H0...
  Qed.

  Definition monotonic: Type := sum strongly_increasing strongly_decreasing.

  Add Morphism f with signature (@cs_eq _) ==> (@cs_eq _) as f_mor.
  Proof. exact f_wd. Qed.

  Lemma mono_eq: monotonic -> forall x x', f x == f x' <-> x == x'.
  Proof with auto.
    intros.
    split.
      intros.
      destruct (CR_lt_eq_dec x x')...
      elimtype False.
      destruct s; destruct X.
            set (s _ _ c).
            destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x') (f x)).
            apply H0... rewrite H. apply CRle_refl.
          set (s _ _ c).
          destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x) (f x')).
          apply H0... rewrite H. apply CRle_refl.
        set (s _ _ c).
        destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x) (f x')).
        apply H0... rewrite H. apply CRle_refl.
      set (s _ _ c).
      destruct (def_leEq _ _ _ _ _ CRisCOrdField (f x') (f x)).
      apply H0... rewrite H. apply CRle_refl.
    intros.
    apply f_wd...
  Qed.

End function_properties.

Record unary_setoid_morphism (A B: CSetoid): Type :=
  { usm: A -> B
  ; usm_wd: forall a a', a [=] a' -> usm a [=] usm a'
  }.

Section BSM.

  Variables A B C: CSetoid.

  Record binary_setoid_morphism: Type :=
    { bsm:> A -> B -> C
    ; bsm_wd: forall a a', a [=] a' ->
        forall b b', b [=] b' -> bsm a b [=] bsm a' b'
    }.

  Add Morphism bsm
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as bsm_mor.
  Proof.
    destruct y.
    exact bsm_wd0.
  Qed.
    (* Todo: For some reason this morphism doesn't actually seem to be
     available in other modules, where I frequently had to redefine it.. *)

End BSM.
