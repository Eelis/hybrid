Require Export CoRN.reals.fast.CRsign.
Require Export util.
Require Export bool_util.

Open Local Scope CR_scope.
Set Implicit Arguments.

(*
  We replace weak_decider with an dec_overestimator (below), which has a
more descriptive type and also provides a separation between the 
computational and logical part of the (semi-)decision procedure.

Definition weak_decider T (P: T -> Prop) :=
  forall x, option (~ P x).
*)

Definition overestimates A bool_dec pred :=
  forall a : A, bool_dec a = false -> ~pred a.

Notation "A >=> B" := (overestimates A B) (at level 40).

Lemma over_true A (x : A) Ideal P : P >=> Ideal -> Ideal x -> P x = true.
Proof.
  intros.
  destruct (bool_case (P x)). hyp.
  elimtype False. apply (H x); hyp. 
Qed.

Record dec_overestimator (A : Type) (Ideal : A -> Prop) := mk_DO
  { do_pred: A -> bool
  ; do_correct: do_pred >=> Ideal
  }.
  
Lemma do_over_false A (x : A) Ideal (do : dec_overestimator Ideal) :
  do_pred do x = false -> ~Ideal x.
Proof with auto.
  intros. destruct do. intro.
  apply (eq_true_false_abs (do_pred (mk_DO do_correct0) x))...
  apply over_true with A Ideal...
Qed.

Lemma do_over_true A (x : A) Ideal (do : dec_overestimator Ideal) :
  Ideal x -> do_pred do x  = true.
Proof.
  intros. destruct do. apply over_true with A Ideal; hyp.
Qed.

Definition CRnonNeg_dec eps r : bool :=
  match CR_epsilon_sign_dec eps r with
  | Lt => false
  | _ => true
  end.

Lemma over_CRnonNeg eps :
  overestimates (CRnonNeg_dec eps) (CRnonNeg).
Proof.
  intros eps x px p.
  set (w := p eps). unfold CRnonNeg_dec, CR_epsilon_sign_dec in px.
  set (ax := approximate x eps) in *.
  destruct (QMinMax.Qle_total ax (2 * eps)); try discriminate.
  destruct (QMinMax.Qle_total (- (2) * eps) ax); try discriminate.
  apply (Qlt_not_le (-(2)*eps) (-eps)).
  change (-eps)%Q with (- (1)%positive * eps)%Q.
  apply Qmult_lt_compat_r; compute; trivial.
  apply Qle_trans with ax; trivial.
Qed.

Definition CRle_pair (pq : CR * CR) := fst pq <= snd pq.

Hint Unfold CRle_pair.

Definition CRle_dec eps (pq : CR * CR) : bool :=
  let (p, q) := pq in
    CRnonNeg_dec eps (q - p).

Lemma over_CRle eps : CRle_dec eps >=> CRle_pair.
Proof with auto with real.
  intros eps x le_x_dec le_x_pred.
  unfold CRle_pair in le_x_pred.
  destruct x. simpl in *.
  apply (over_CRnonNeg eps le_x_dec)...
Qed.

Ltac estim pred := eapply (over_true _ pred); auto.
