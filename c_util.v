Require Import util.
Require Export CRsign.
Require Export CRln.
Require Import CRexp.

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
Qed. (* todo: generalize to arbitrary ring. *)

Lemma add_both_sides x y: x == y -> forall z, x+z == y+z.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma diff_zero_eq x y: x - y == '0 -> x == y.
Proof.
  intros.
  set (add_both_sides H y).
  rewrite (Radd_0_l CR_ring_theory) in s.
  rewrite <- (Radd_assoc CR_ring_theory) in s.
  rewrite (Radd_comm CR_ring_theory (-y)) in s.
  rewrite (Ropp_def CR_ring_theory) in s.
  rewrite (Radd_comm CR_ring_theory) in s.
  rewrite (Radd_0_l CR_ring_theory) in s.
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

Lemma CRlt_trans x y z: x < y -> y < z -> x < z.
  exact (so_trans (ax_less_strorder _ _  _ _ _ (cof_proof CRasCOrdField))).
Qed.

Lemma positive_CRpos (q: positive): CRpos ('q).
Proof.
  unfold CRpos. intro. 
  exists (QposMake q 1). 
  apply CRle_refl.
Qed.

Lemma Qpos_CRpos (q: Qpos): CRpos ('q).
  unfold CRpos.
  intro. exists q. apply CRle_refl.
Qed.

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

Lemma t3: Setoid_Theory CR (@st_eq _).
  unfold Setoid_Theory.
  apply (CSetoid_eq_Setoid (csg_crr CRasCField)).
Qed.

Lemma diff_opp x y: x - y == -(y - x).
  set (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
  intros.
  rewrite s.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite s0.
  apply (Radd_comm CR_ring_theory).
Qed.

Lemma Qmult_inv (x: Q) (y: positive): (x == y -> x * (1 # y) == 1)%Q.
Proof with auto.
  intros. rewrite H.
  unfold Qeq. simpl. repeat rewrite Pmult_1_r. ref.
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
  unfold st_eq.
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
  clearbody s.
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
Qed.

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
Qed.

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

Lemma CRmult_0_l x: '0 * x == '0.
Proof @Rmul_0_l _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory.

Lemma CRmult_comm x y: x * y == y * x.
Proof Rmul_comm CR_ring_theory.

Lemma CRmult_0_r x: x * '0 == '0.
Proof. intros. rewrite CRmult_comm. apply CRmult_0_l. Qed.

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
    CRmult (fun x y : CR => x - y) CRopp (@st_eq CR) t3
    CR_ring_eq_ext CR_ring_theory ).
  rewrite <- (Radd_assoc CR_ring_theory y).
  rewrite (Radd_comm CR_ring_theory x).
  rewrite s.
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
  rewrite s.
  rewrite (Radd_comm CR_ring_theory).
  assumption.
Qed.

Lemma CRlt_opp_compat x y: x < y -> -y < -x.
  unfold CRlt.
  unfold CRpos.
  intros.
  destruct H.
  exists x0.
  rewrite (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  rewrite (Radd_comm CR_ring_theory).
  assumption.
Qed.

Lemma CRopp_mult_l x y: -(x * y) == -x * y.
Proof Ropp_mul_l t3 CR_ring_eq_ext CR_ring_theory.

Lemma CRmult_lt_0 x y: '0 < x -> '0 < y -> '0 < x * y.
Proof ax_mult_resp_pos _ _ _ _ _ (cof_proof CRasCOrdField).

Lemma CRopp_0: -'0 == '0.
  rewrite CRopp_Qopp.
  reflexivity.
Qed.

Lemma CRpos_lt_0 x: '0 < x -> CRpos x.
  unfold CRlt.
  intros.
  apply CRpos_wd with (x - '0).
    rewrite CRopp_0.
    apply CRadd_0_r.
  assumption.
Qed.

Lemma CRpos_lt_0_rev x: CRpos x -> '0 < x.
Proof with auto.
  unfold CRlt.
  intros.
  apply CRpos_wd with x.
    rewrite CRopp_0.
    symmetry. apply CRadd_0_r.
  assumption.
Defined.

Lemma CRpos_mult x y: CRpos x -> CRpos y -> CRpos (x * y).
Proof.
  intros.
  apply CRpos_lt_0.
  apply CRmult_lt_0; apply CRpos_lt_0_rev; assumption.
Qed.

Lemma CRmult_lt_pos_r x y: x < y -> forall z, CRpos z -> z * x < z * y.
Proof.
  intros.
  unfold CRlt in *.
  apply CRpos_wd with (z * y + z * -x).
    rewrite (Rmul_comm CR_ring_theory z (-x)).
    rewrite <- (CRopp_mult_l x z).
    rewrite (Rmul_comm CR_ring_theory x z).
    reflexivity.
  apply CRpos_wd with (z * (y + - x)).
    rewrite (Rmul_comm CR_ring_theory z).
    rewrite (Rdistr_l CR_ring_theory).
    rewrite (Rmul_comm CR_ring_theory y).
    rewrite (Rmul_comm CR_ring_theory (-x)).
    reflexivity.
  apply CRpos_mult; assumption.
Qed.

Lemma t12 x y: -x <= y -> -y <= x.
Proof.
  intros.
  set (@Ropp_opp _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory x).
  rewrite <- s.
  apply t8.
  assumption.
Qed.

Lemma CRpos_opp x: CRneg x -> CRpos (-x).
Proof with auto.
  unfold CRpos, CRneg, CRle.
  intros.
  destruct H.
  exists x0.
  rewrite CRopp_Qopp.
  rewrite (Radd_comm CR_ring_theory)...
Qed.

Lemma CRpos_opp' x: CRneg (-x) -> CRpos x.
Proof with auto.
   intros.
   apply (@CRpos_wd (--x)).
   apply (Ropp_opp t3 CR_ring_eq_ext CR_ring_theory).
   apply CRpos_opp...
Qed.

Lemma t6 x y: CRneg (x - y) -> CRpos (y - x).
Proof with auto.
  intros.
  apply CRpos_opp'.
  apply CRneg_wd with (x - y)...
  apply diff_opp.
Qed.

Import PowerSeries.
Import Exponential.

Lemma exp_sum a b: exp (a + b) == exp a * exp b.
  intros.
  rewrite <- (CRasIRasCR_id a).
  rewrite <- (CRasIRasCR_id b).
  rewrite <- IR_plus_as_CR.
  do 3 rewrite <- exp_correct.
  rewrite <- IR_mult_as_CR.
  apply IRasCR_wd.
  apply Exp_plus.
Qed.

Lemma blo x y: x < y -> x < IRasCR (CRasIR y).
  intros.
  apply CRlt_wd with x y.
      reflexivity.
    symmetry.
    apply CRasIRasCR_id.
  assumption.
Qed.

Lemma CRln_expand a p: CRln a p == CRln (IRasCR (CRasIR a)) (blo p).
Proof. intros. apply CRln_wd. symmetry. apply CRasIRasCR_id. Qed.

Lemma CR_mult_as_IR (x y: CR): CRasIR (x * y) [=] CRasIR x [*] CRasIR y.
Proof with auto.
  intros.
  transitivity (CRasIR (IRasCR (CRasIR x) * IRasCR (CRasIR y))).
    apply CRasIR_wd.
    repeat rewrite CRasIRasCR_id.
    reflexivity.
  transitivity (CRasIR (IRasCR (CRasIR x [*] CRasIR y))).
    apply CRasIR_wd.
    rewrite <- IR_mult_as_CR.
    reflexivity.
  apply IRasCRasIR_id.
Qed. (* this is an extra-awful proof *)

Lemma CRln_mult a b p q r: CRln (a * b) r == CRln a p + CRln b q.
Proof with auto.
  intros.
  assert (Zero [<] CRasIR a).
    apply CR_less_as_IR.
    apply CRlt_wd with ('0) a...
      symmetry. apply IR_Zero_as_CR.
    symmetry. apply CRasIRasCR_id.
  assert (Zero [<] CRasIR b).
    apply CR_less_as_IR.
    apply CRlt_wd with ('0) b...
      symmetry. apply IR_Zero_as_CR.
    symmetry. apply CRasIRasCR_id.
  assert (Zero [<] CRasIR (a * b)).
    apply CR_less_as_IR.
    apply CRlt_wd with ('0) (a * b)...
      symmetry. apply IR_Zero_as_CR.
    symmetry. apply CRasIRasCR_id.
  rewrite (CRln_expand p).
  rewrite (CRln_expand q).
  rewrite CRln_expand at 1.
  rewrite <- (CRln_correct (CRasIR (a * b)) X1).
  rewrite <- (CRln_correct (CRasIR a) X).
  rewrite <- (CRln_correct (CRasIR b) X0).
  rewrite <- IR_plus_as_CR.
  apply IRasCR_wd.
  assert (Zero [<] CRasIR a [*] CRasIR b).
    apply CR_less_as_IR.
    apply CRlt_wd with ('0) (a * b)...
      symmetry. apply IR_Zero_as_CR.
    transitivity (IRasCR (CRasIR (a * b))).
      symmetry. apply CRasIRasCR_id.
    apply IRasCR_wd.
    apply CR_mult_as_IR.
  rewrite <- (Log_mult (CRasIR a) (CRasIR b) X X0 X2).
  apply Log_wd.
  apply CR_mult_as_IR.
Qed.

Lemma exp_0: exp ('0) == '1.
  rewrite <- IR_One_as_CR.
  rewrite <- IR_Zero_as_CR.
  rewrite <- exp_correct.
  apply IRasCR_wd.
  apply Exp_zero.
Qed.

Lemma exp_le_inv x y: exp x <= exp y -> x <= y.
  intros x y.
  rewrite <- (CRasIRasCR_id x).
  rewrite <- (CRasIRasCR_id y).
  do 2 rewrite <- exp_correct.
  intros.
  apply (IR_leEq_as_CR (CRasIR x) (CRasIR y)).
  apply Exp_cancel_leEq.
  apply <- IR_leEq_as_CR.
  assumption.
Qed.

Lemma CRln_exp x p: CRln (exp x) p == x.
Proof with auto.
  intros.
  assert ('0 < exp (IRasCR (CRasIR x))).
    apply CRlt_wd with ('0) (exp x)...
      reflexivity.
    rewrite (CRasIRasCR_id x).
    reflexivity.
  assert (exp x == IRasCR (Exp (CRasIR x))).
    rewrite exp_correct.
    apply exp_wd.
    symmetry.
    apply CRasIRasCR_id.
  assert ('0 < IRasCR (Exp (CRasIR x))).
    apply CRlt_wd with ('0) (exp x)...
    reflexivity.
  rewrite (CRln_wd p H).
    rewrite (CRln_wd H H1).
      assert (Zero [<] Exp (CRasIR x)).
        apply CR_less_as_IR.
        apply CRlt_wd with ('0) (exp x)...
        rewrite IR_Zero_as_CR. reflexivity.
      rewrite <- (CRln_correct (Exp (CRasIR x)) X).
      rewrite <- (CRasIRasCR_id x) at 2.
      apply IRasCR_wd.
      apply Log_Exp.
    rewrite <- exp_correct.
    reflexivity.
  apply exp_wd.
  symmetry.
  apply CRasIRasCR_id.
Qed.

Lemma exp_ln x p: exp (CRln x p) == x.
Proof with auto.
  intros.
  assert ('0 < IRasCR (CRasIR x)).
    apply CRlt_wd with ('0) x...
      reflexivity.
    symmetry. apply CRasIRasCR_id.
  assert (CRln x p == CRln _ H).
    apply CRln_wd. symmetry. apply CRasIRasCR_id.
  rewrite (exp_wd H0).
  assert (Zero [<] CRasIR x).
    apply CR_less_as_IR.
    apply CRlt_wd with ('0) x...
      rewrite IR_Zero_as_CR. reflexivity.
    symmetry. apply CRasIRasCR_id.
  rewrite <- (CRln_correct (CRasIR x) X).
  rewrite <- exp_correct.
  rewrite <- (CRasIRasCR_id x) at 2.
  apply IRasCR_wd.
  apply Exp_Log.
Qed.

Lemma CRpos_plus x y: CRpos x -> CRnonNeg y -> CRpos (x + y).
Proof with auto.
  intros.
  unfold CRpos.
  destruct H.
  exists x0.
  unfold CRle in *.
  rewrite (Radd_comm CR_ring_theory x).
  rewrite <- (Radd_assoc CR_ring_theory).
  apply t10...
Qed.

Lemma CRlt_le_trans: forall x y, x < y -> forall z, y <= z -> x < z.
Proof with auto.
  intros.
  unfold CRlt in *.
  unfold CRle in *.
  apply CRpos_wd with (y - x + (z - y)).
    rewrite <- (Radd_assoc CR_ring_theory).
    rewrite (Radd_assoc CR_ring_theory (-x)).
    rewrite <- t11.
    apply (Radd_comm CR_ring_theory).
  apply CRpos_plus...
Qed.

Definition Qpos_div (a b: Qpos): Qpos :=
  match a, b with
  | QposMake aNum aDen, QposMake bNum bDen =>
    QposMake (aNum * bDen) (aDen * bNum)
  end.

  (* todo: *)
Axiom bah: forall x y, '0 < x * y -> '0 < x -> '0 < y.
Axiom exp_pos: forall x, '0 < exp x.
Axiom CRinv_pos: forall x, '0 < x -> forall p: x >< '0, '0 < CRinv x p.
Axiom CRinv_mult: forall x (p: x >< '0), x * CRinv x p == '1.
Axiom exp_inc: forall x y, x < y -> exp x < exp y.
Axiom exp_inc': forall x y, exp x < exp y -> x < y.
Axiom exp_opp_ln: forall x xp, x * exp (- CRln x xp) == '1.
Axiom CRln_le: forall x y (p: '0 < x) (q: '0 < y), x <= y -> CRln x p <= CRln y q.
Axiom CRlt_irrefl: forall a,  a < a -> False.
Axiom CRle_mult: forall x, '0 <= x -> forall a b, a <= b -> x * a <= x * b.
Axiom CRmult_le_compat_r: forall x y, x <= y -> forall z, CRnonNeg z -> z * x <= z * y.
Axiom CRmult_le_inv: forall x, CRnonNeg x -> forall a b, x * a <= x * b -> a <= b.
Axiom CRle_opp_inv: forall x y, -x <= -y -> y <= x.


Definition weak_CRlt_decision (f: (CR -> CR -> Set) -> Set): Set :=
  option (sum (f CRlt) (f (fun x y => y < x))).

Definition weak_CRle_decision (f: (CR -> CR -> Prop) -> Prop): Set :=
  option ({f CRle}+{f (fun x y => y <= x)}).

Definition NonNegCR: Type := sig CRnonNeg.

Program Definition NonNegCR_plus (n n': NonNegCR): NonNegCR := n + n'.

Next Obligation.
  destruct n. destruct n'.
  simpl. apply t10; assumption.
Qed.

Definition NonNegCR_zero: NonNegCR := exist _ _ CRnonNeg_zero.

Axiom CR_lt_eq_dec: forall (x y: CR), sum (x==y) (sum (x<y) (y<x)).
(* hm, if we make this a {x<=y}+{y<=x} axiom, we can be sure it won't be used in
 computation, because that's in prop, no? it may not be enough for
 our proofs though.. *)

Lemma CR_le_le_dec x y: {x<=y}+{y<=x}.
  intros.
  destruct (CR_lt_eq_dec x y).
    left. rewrite s. apply CRle_refl.
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
      rewrite (f_wd s).
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
      rewrite s.
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
      rewrite (f_wd s).
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
      rewrite s.
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
      rewrite (f_wd s).
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
      rewrite (f_wd s).
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

Ltac CRle_constants := apply inject_Q_le; compute; discriminate.
