Require Import c_util.
Require Import geometry.
Require Import CRreal.
Require Import CRexp.
Require Import CRln.
Require Import flow.
Set Implicit Arguments.
Open Local Scope CR_scope.

Definition CRln' (x: CR) (H: CRpos x): CR :=
  CRln x (CRpos_lt_0_rev H).

Implicit Arguments CRln' [].

Hint Resolve t8 CRpos_lt_0_rev exp_pos CRmult_lt_0 CRln_le.

Lemma CRln_mult': forall a b (p: CRpos a) (q: CRpos b) (r: CRpos (a * b)),
  CRln' (a * b) r == CRln' a p + CRln' b q.
Proof. intros. apply CRln_mult. Qed.

Lemma CRln'_opp_mult x y (P: CRpos (- (x * y))) (Q: CRpos (-x)) (R: CRpos y):
  CRpos (- x * y) -> CRln' _ P == CRln' _ Q + CRln' _ R.
Proof with auto.
  intros.
  apply CRln_opp_mult.
  apply CRpos_lt_0_rev...
Qed.

Definition noneOr (X: Type) (P: X -> Set) (o: option X): Set :=
  match o with
  | None => True
  | Some x => P x
  end.

Definition someAnd (X: Type) (P: X -> Set) (o: option X): Set :=
  match o with
  | None => False
  | Some x => P x
  end.

Definition optPos: optCR -> Set := noneOr CRpos.
Definition optNeg: optCR -> Set := noneOr CRneg.

Definition optPos_le_trans (x: CR) (H: CRpos x) (y: optCR): OCRle (Some x, y) -> optPos y :=
  match y with
  | None => fun _ => I
  | Some v => @CRpos_le_trans x H v
  end.

Definition optNeg_le_trans (x: CR) (H: CRneg x) (y: optCR): OCRle (y, Some x) -> optNeg y :=
  match y with
  | None => fun _ => I
  | Some v => @CRneg_le_trans x H v
  end.

Lemma OCRle_None_right x: OCRle (x, None).
Proof. destruct x; exact I. Qed.

Definition raw (x: CR) (t: Time): CR := x * exp (-t).

Hint Resolve exp_pos'.

Lemma raw_pos x t: CRpos x -> CRpos (raw x t).
Proof with auto. intros. apply CRpos_mult... Defined.

Lemma raw_neg x t: CRneg x -> CRneg (raw x t).
Proof with auto.
  intros.
  unfold raw.
  apply CRneg_opp.
  apply CRpos_wd with (-x * exp (-t)).
    symmetry. apply CRopp_mult_l.
  apply CRpos_mult...
  apply CRpos_opp...
Defined.

Lemma raw_pos_inv x t: CRpos (raw x t) -> CRpos x.
Proof with auto.
  intros.
  unfold raw in H.
  apply CRpos_mult_inv with (exp (-t))...
Defined.

Lemma raw_neg_inv x t: CRneg (raw x t) -> CRneg x.
Proof with auto.
  intros.
  apply CRneg_opp.
  apply CRpos_mult_inv with (exp (-t))...
  apply CRpos_wd with (-(x * exp (-t))).
    apply CRopp_mult_l.
  apply CRpos_opp...
Defined.

Lemma raw_lt_compat_l: forall x a b, CRpos x -> a < b -> raw a x < raw b x.
Proof with auto.
  intros.
  unfold raw.
  apply CRlt_wd with (exp (-x) * a) (exp (-x) * b).
      apply (Rmul_comm CR_ring_theory).
    apply (Rmul_comm CR_ring_theory).
  apply CRmult_lt_pos_r...
Defined.

Lemma raw_le_compat_l: forall x a b, a <= b -> raw a x <= raw b x.
Proof with auto.
  intros.
  unfold raw.
  rewrite (Rmul_comm CR_ring_theory a).
  rewrite (Rmul_comm CR_ring_theory b).
  apply CRmult_le_compat_r...
  apply CRpos_nonNeg...
Qed.

Lemma raw_le_inv_r: forall x a b, CRnonNeg x -> raw x b <= raw x a -> a <= b.
Proof with auto.
  unfold raw.
  intros.
  apply CRle_opp_inv.
  apply (exp_le_inv).
  apply CRmult_le_inv with x...
Qed.

Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
Proof.
  apply (Build_binary_setoid_morphism _ _ _ raw).
  intros. unfold raw.
  rewrite H. rewrite H0. reflexivity.
Defined.

Lemma A x: x * exp (-'0) == x.
  intros.
  rewrite CRopp_0.
  rewrite exp_0.
  rewrite (Rmul_comm CR_ring_theory).
  apply (Rmul_1_l CR_ring_theory).
Qed.

Lemma B x t t': x * exp (- (t + t'))[=]x * exp (- t) * exp (- t').
  intros.
  rewrite <- (Rmul_assoc CR_ring_theory).
  rewrite <- exp_sum.
  rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
  reflexivity.
Qed.

Definition f: Flow CRasCSetoid := Build_Flow morphism A B.

Definition part_inv (x x': CR) (xp: CRpos x) (x'p: CRpos x'): Time := CRln' _ xp - CRln' _ x'p.

Lemma part_inv_correct (x: CR) (xp: CRpos x) (x': CR) (x'p: CRpos x'):
  raw x (part_inv xp x'p) == x'.
Proof with auto.
  unfold raw, part_inv.
  intros.
  rewrite <- diff_opp.
  rewrite exp_sum.
  unfold CRln'.
  rewrite exp_ln.
  rewrite (Rmul_comm CR_ring_theory x').
  rewrite (Rmul_assoc CR_ring_theory).
  rewrite exp_opp_ln.
  apply (Rmul_1_l CR_ring_theory).
Qed.

Definition upper_shortest (src dst: OpenRange):
  optPos (fst (`src)) -> optPos (snd (`dst)) -> optCR :=
  match src, dst return optPos (fst (`src)) -> optPos (snd (`dst)) -> optCR with
  | exist p _, exist q _ =>
    match p, q return optPos (fst p) -> optPos (snd q) -> optCR with
    | (x, _), (_, u) =>
      match u, x return optPos x -> optPos u -> optCR with
      | Some v, Some w =>
        fun B E => Some (part_inv B E)
      | _, _ => fun _ _ => None
  end end end.

Definition upper_longest (src dst: OpenRange):
  optPos (snd (`src)) -> optPos (fst (`dst)) -> optCR :=
  match src, dst return optPos (snd (`src)) -> optPos (fst (`dst)) -> optCR with
  | exist p _, exist q _ =>
    match p, q return optPos (snd p) -> optPos (fst q) -> optCR with
    | (_, x), (u, _) =>
      match u, x return optPos x -> optPos u -> optCR with
      | Some v, Some w =>
        fun B E => Some (part_inv B E)
      | _, _ => fun _ _ => None
  end end end.

Definition lower_shortest (src dst: OpenRange):
  optNeg (snd (`src)) -> optNeg (fst (`dst)) -> optCR :=
  match src, dst return optNeg (snd (`src)) -> optNeg (fst (`dst)) -> optCR with
  | exist p _, exist q _ =>
    match p, q return optNeg (snd p) -> optNeg (fst q) -> optCR with
    | (_, x), (u, _) =>
      match u, x return optNeg x -> optNeg u -> optCR with
      | Some v, Some w =>
        fun B E => Some (part_inv (CRpos_opp B) (CRpos_opp E))
      | _, _ => fun _ _ => None
  end end end.

Definition lower_longest (src dst: OpenRange):
  optNeg (fst (`src)) -> optNeg (snd (`dst)) -> optCR :=
  match src, dst return optNeg (fst (`src)) -> optNeg (snd (`dst)) -> optCR with
  | exist p _, exist q _ =>
    match p, q return optNeg (fst p) -> optNeg (snd q) -> optCR with
    | (x, _), (_, u) =>
      match u, x return optNeg x -> optNeg u -> optCR with
      | Some v, Some w =>
        fun B E => Some (part_inv (CRpos_opp B) (CRpos_opp E))
      | _, _ => fun _ _ => None
  end end end.

      (* i have some faith that some of these return clauses can be omitted in a future Coq version *)

Section upper_def.

  Variable (src dst: OpenRange)
    (src_fst_nonNeg: optPos (fst (`src)))
    (src_snd_nonNeg: optPos (snd (`src)))
    (dst_fst_nonNeg: optPos (fst (`dst)))
    (dst_snd_nonNeg: optPos (snd (`dst))).

  Program Definition upper: OpenRange :=
    (upper_shortest src dst src_fst_nonNeg dst_snd_nonNeg
    , upper_longest src dst src_snd_nonNeg dst_fst_nonNeg).
  Next Obligation. Proof with auto.
    destruct src. destruct dst.
    simpl.
    destruct x. destruct x0.
    destruct s2...
    destruct s...
    destruct s1...
    destruct s0...
    unfold part_inv.
    unfold CRln'.
    apply t9...
  Defined.

  Variables
    (x: CR) (xnn: CRnonNeg x)
    (xisrc: in_orange src x)
    (t: Time) (xidst: in_orange dst (raw x t)).

  Lemma part_inv_alt (H3: CRpos x) (H4 : CRpos (raw x t)): t[=]part_inv H3 H4.
  Proof with auto.
    intros. unfold part_inv, raw.
    assert (CRpos (exp (-t)))...
    rewrite (CRln_mult' H3 H H4).
    unfold CRln'.
    rewrite CRln_exp.
    rewrite <- diff_opp.
    rewrite <- t11.
    reflexivity.
  Qed.

  Lemma upper_correct: in_orange upper t.
  Proof with auto.
    unfold upper, in_orange, orange_left, orange_right.
    simpl. destruct src. destruct dst. destruct x0. destruct x1.
    simpl. split.
      destruct s2... destruct s... destruct xisrc. destruct xidst.
      simpl in H, H2, src_fst_nonNeg, src_snd_nonNeg, dst_fst_nonNeg, dst_snd_nonNeg.
      assert (CRpos x). apply CRpos_le_trans with s...
      rewrite (part_inv_alt H3 (raw_pos t H3)).
      unfold part_inv.
      apply t9; unfold CRln'...
    destruct s1... destruct s0... destruct xisrc. destruct xidst.
    simpl in H0, H1, src_fst_nonNeg, src_snd_nonNeg, dst_fst_nonNeg, dst_snd_nonNeg.
    assert (CRpos (raw x t)). apply CRpos_le_trans with s1...
    rewrite (part_inv_alt (raw_pos_inv H3) H3).
    apply t9; unfold CRln'...
  Qed.

End upper_def.

Section lower_def.

  Variables (src dst: OpenRange)
    (src_fst_nonPos: optNeg (fst (`src)))
    (src_snd_nonPos: optNeg (snd (`src)))
    (dst_fst_nonPos: optNeg (fst (`dst)))
    (dst_snd_nonPos: optNeg (snd (`dst))).

  Program Definition lower: OpenRange :=
    (lower_shortest src dst src_snd_nonPos dst_fst_nonPos
    , lower_longest src dst src_fst_nonPos dst_snd_nonPos).
  Next Obligation. Proof with auto.
    destruct src. destruct dst.
    destruct x. destruct x0.
    simpl.
    destruct s1...
    destruct s0...
    destruct s2...
    destruct s...
    unfold part_inv.
    apply t9; unfold CRln'...
  Defined.

  Variables
    (x: CR) (xnn: CRnonNeg x)
    (xisrc: in_orange src x)
    (t: Time) (xidst: in_orange dst (raw x t)).

  Lemma lower_part_inv_alt (H3: CRneg x) (H4: CRneg (raw x t)): t[=]part_inv (CRpos_opp H3) (CRpos_opp H4).
  Proof with auto.
    intros. unfold part_inv, raw.
    rewrite (CRln'_opp_mult (CRpos_opp H4) (CRpos_opp H3) (exp_pos' (-t))).
      unfold CRln'.
      rewrite CRln_exp.
      rewrite <- diff_opp.
      rewrite <- t11...
    apply CRpos_wd with (- (x * exp (-t))).
      apply CRopp_mult_l.
    apply CRpos_opp...
  Qed.

  Lemma lower_correct: in_orange lower t.
  Proof with auto.
    unfold lower, in_orange, orange_left, orange_right.
    simpl. destruct src. destruct dst. destruct x0. destruct x1.
    simpl. split.
      destruct s1... destruct s0... destruct xisrc. destruct xidst.
      simpl in H0, H1, src_fst_nonPos, src_snd_nonPos, dst_fst_nonPos, dst_snd_nonPos.
      assert (CRneg x). apply CRneg_le_trans with s0...
      assert (CRneg (raw x t)). apply raw_neg...
      rewrite (lower_part_inv_alt H3 H4).
      apply t9; unfold CRln'...
    destruct s2... destruct s... destruct xisrc. destruct xidst.
    simpl in H, H2, src_fst_nonPos, src_snd_nonPos, dst_fst_nonPos, dst_snd_nonPos.
    assert (CRneg (raw x t)). apply CRneg_le_trans with s2...
    assert (CRneg x). apply raw_neg_inv with t...
    rewrite (lower_part_inv_alt H4 H3).
    unfold part_inv.
    apply t9; unfold CRln'...
  Qed.

End lower_def.

Definition someAnd_noneOr (X: Type) (P: X -> Set) (r: option X): someAnd P r -> noneOr P r :=
  match r return someAnd P r -> noneOr P r with
  | None => fun _ => I
  | Some v => fun H => H
  end.

Definition upper_pos_from_lower (r: OpenRange):
  someAnd CRpos (fst (`r)) -> optPos (snd (`r)).
Proof.
  intros [[[x|] y] le]; intros.
    apply optPos_le_trans with x; assumption.
  elimtype False. assumption.
Defined.

Definition lower_neg_from_upper (r: OpenRange):
  someAnd CRneg (snd (`r)) -> optNeg (fst (`r)).
Proof.
  intros [[x [y|]] le]; intros.
    apply optNeg_le_trans with y; assumption.
  elimtype False. assumption.
Defined.

Section contents.

  Variable (eps: Qpos).

  Definition range_cases (r: OpenRange): option (
    someAnd CRpos (fst (`r)) +
    someAnd CRneg (snd (`r)) +
    (optNeg (fst (`r)) * optPos (snd (`r)))) :=
    match r return option (someAnd CRpos (fst (`r)) + someAnd CRneg (snd (`r)) + (optNeg (fst (`r)) * optPos (snd (`r)))) with
    | exist p _ => match p return option (someAnd CRpos (fst p) + someAnd CRneg (snd p) + (optNeg (fst p) * optPos (snd p))) with
      | (s, s0) => match s return option (someAnd CRpos s + someAnd CRneg s0 + (optNeg s * optPos s0)) with
        | Some v => match CR_sign_dec eps v with
          | None => None
          | Some (inl U) => Some (inl (inl U))
          | Some (inr U) => match s0 with
            | None => Some (inr (pair U I))
            | Some w => match CR_sign_dec eps w with
              | Some (inl V) => Some (inr (pair U V))
              | Some (inr V) => Some (inl (inr V))
              | None => None
          end end end
        | None => match s0 with
          | Some v => match CR_sign_dec eps v with
            | Some (inl U) => Some (inr (pair I U))
            | Some (inr U) => Some (inl (inr U))
            | None => None
            end
          | None_ => Some (inr (pair I I))
    end end end end.

  Program Definition no_trans_result: OpenRange := (-'1, -'1): Range.

  Definition inv (src dst: OpenRange): OpenRange.
  Proof with auto.
    intros.
    refine (match range_cases src, range_cases dst with
    | Some (inr _), Some (inr _) => unbounded_range
    | Some (inr (pair U W)), Some (inl (inr V)) => _
    | Some (inr (pair U W)), Some (inl (inl V)) => _
    | Some (inl (inr U)), Some (inr (pair V W)) => _
    | Some (inl (inr y)), Some (inl (inr y0)) => lower src dst (lower_neg_from_upper _ y) (someAnd_noneOr _ _ y) (lower_neg_from_upper _ y0) (someAnd_noneOr _ _ y0)
    | Some (inl (inr _)), Some (inl (inl _)) => no_trans_result
    | Some (inl (inl U)), Some (inr (pair V W)) => _
    | Some (inl (inl _)), Some (inl (inr _)) => no_trans_result
    | Some (inl (inl y)), Some (inl (inl y0)) => upper src dst (someAnd_noneOr _ _ y) (upper_pos_from_lower _ y) (someAnd_noneOr _ _ y0) (upper_pos_from_lower _ y0)
    | None, _ => unbounded_range
    | _, None => unbounded_range
    end); try clear s; try clear s0; try clear s1; try clear s2; try destruct p;
      destruct src; destruct dst; destruct x; destruct x0.
          try (destruct s; [idtac | elimtype False; assumption]).
          apply (upper (exist OCRle (Some s, s0) o1) (exist OCRle (None, s2) I) y)...
            apply optPos_le_trans with s...
          simpl...
        (* src neg, dst has 0 *)
        try (destruct s0; [idtac | elimtype False; assumption]).
        apply (lower (exist OCRle (s, Some s0) o1) (exist OCRle (s1, None) (OCRle_None_right _))); simpl...
        apply optNeg_le_trans with s0...
      (* src has 0, dst pos *)
      try (destruct s1; [idtac | elimtype False; assumption]).
      apply (@upper (exist OCRle (None, s0) I) (exist OCRle (Some s1, s2) o2)); simpl...
      apply optPos_le_trans with s1...
    (* src has 0, dst neg *)
    try (destruct s2; [idtac | elimtype False; assumption]).
    apply (lower (exist OCRle (s, None) (OCRle_None_right s)) (exist OCRle (s1, Some s2) o2)); simpl...
    apply optNeg_le_trans with s2...
  Defined.

  Lemma inv_correct: range_flow_inv_spec f inv.
  Proof with auto.
    unfold range_flow_inv_spec.
    intros src x H dst t H0.
    unfold inv.
    destruct (range_cases src) as [[[P | Q] | R] | S];
    destruct (range_cases dst) as [[[V | W] | X] | Y];
      destruct src; destruct dst; destruct x0; destruct x1;
      try (destruct s; [idtac | elimtype False; assumption]);
      try (destruct s0; [idtac | elimtype False; assumption]);
      try (destruct s1; [idtac | elimtype False; assumption]);
      try (destruct s2; [idtac | elimtype False; assumption]); simpl...
                      apply upper_correct with x...
                    elimtype False.
                    destruct H. destruct H0.
                    simpl in H1, W, H, H2.
                    apply CRneg_pos_excl with (raw x t).
                      apply raw_pos...
                      apply CRpos_lt_0.
                      apply CRlt_le_trans with s...
                    apply CRneg_le_trans with s2...
                  destruct X.
                  apply upper_correct with x...
                  split; simpl...
                  destruct H0...
                elimtype False.
                destruct H. destruct H0.
                simpl in V, Q, H, H1, H0.
                apply CRneg_pos_excl with (raw x t).
                  apply CRpos_le_trans with s1...
                apply raw_neg.
                apply CRneg_le_trans with s0...
              apply lower_correct with x...
            destruct X.
            apply lower_correct with x...
            split; simpl...
            destruct H0...
          destruct R.
          apply upper_correct with x...
          split; simpl...
          destruct H...
        destruct R.
        apply lower_correct with x...
        split; simpl...
        destruct H...
      destruct R...
    destruct R...
  Qed.

End contents.
