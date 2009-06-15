Require Import geometry.
Require Export Program.
Require Import EquivDec.

Open Local Scope CR_scope.

Hint Unfold in_orange orange_left orange_right : hybsys.

Hint Rewrite CRplus_Qplus CRminus_Qminus CRopp_Qopp 
  CRmult_Qmult CRinv_Qinv : CR_Q.

Ltac CR_Q_pre := autorewrite with CR_Q.

Ltac CRcmp_to_O :=
  let go x :=
    exists x%Qpos; ring_simplify; vm_compute; intros; discriminate
  in
  match goal with
  | |- '0 < '?x =>
      match type of x with
      | Q => 
          match eval compute in (Qnum x) with
          | Zpos ?v => go (v # Qden x)%Qpos
          end
      | positive => go x
      | nat => go (P_of_succ_nat (x - 1))
      end
  end.

Ltac wd_helper :=
  match goal with
  | H: regFunEq ?x ?y |- 
    `match CR_le_le_dec ?x ?v with
    | left _ => _ | right _ => _
     end
    =
    `match CR_le_le_dec ?y ?v' with
    | left _ => _ | right _ => _
     end =>
    let e := fresh "e" in
    set (e := @CR_le_le_dec_wd _ _ v v H (genericSetoid_Reflexive _ _)); clearbody e;
    destruct (CR_le_le_dec x v) in *; 
    destruct (CR_le_le_dec y v) in *; 
    auto; try discriminate; clear e
  end.

Ltac qrange := unfold uncurry; vm_compute; intuition; discriminate.

Ltac decomp_hyp H := 
  match type of H with
  | _ /\ _ => decompose [Logic.and] H; clear H
  | _ \/ _ => decompose [Logic.or] H; clear H
  | ex _ => decompose [ex] H; clear H
  | sig _ => decompose record H; clear H
  end.

Ltac decomp :=
  repeat
    match goal with
    | H: _ |- _ => decomp_hyp H
    end.

Ltac destruct_hs_data :=
  repeat
    match goal with
    | H: ?x * ?y |- _ => destruct H; clear H
    | p : Point |- _ => destruct p; clear p
    end.

Ltac simplify_hyps :=
  intros;
  repeat progress 
    (destruct_hs_data; 
     decomp;
     try subst; 
     simpl in *).

Ltac full_split :=
  repeat 
    match goal with
    | |- ?x /\ ?y => split
    | |- ?x <-> ?y => split; simplify_hyps; intros
    end.

Ltac single_rewrite :=
  match goal with
  | H: _ |- _ => rewrite H; clear H
  | H: _ |- _ => rewrite <- H; clear H
  end.

Ltac esubst :=
  repeat single_rewrite; try subst.

Ltac simplify_proj :=
  repeat
    match goal with
    | |- context [`?x] => destruct x; simpl
    end.

Ltac hs_unfolds := 
  repeat progress (
    unfold 
      Basics.compose,
      in_orange, in_osquare, orange_left, orange_right;
    simpl).

Ltac CRle_solve :=
  match goal with
  | H: ?x <= ?y |- _ <= ?y =>
      solve [apply CRle_trans with x; auto || CRle_constants]
  | H: ?x <= ?y |- ?x <= _ =>
      solve [apply CRle_trans with y; auto || CRle_constants]
  | _ => solve [CRle_constants]
  end.

Ltac grind tac := 
  match goal with
  | |- '0 < '_ => CRcmp_to_O
  | |- forall x, In x _ => 
      prove_exhaustive_list
  | |- _ =>
    hs_unfolds; intros; simpl;
    try solve [intros; CRle_constants | program_simplify | auto with hybsys];
      match goal with
      | |- uncurry Qle _ =>
          qrange
      | |- OQle _ =>
          qrange
      | H: regFunEq ?x ?y |- `_ = `_ =>
          repeat wd_helper
      | |- NoDup _ =>
          prove_NoDup
      | |- EquivDec.EqDec _ _ =>
          equiv_dec
      | |- _ <= _ =>
          CRle_solve
      | |- _ =>
          progress (
            hs_unfolds; intros; simplify_hyps; 
              full_split; esubst; eauto with hybsys; try tac
          );
          grind tac
      end
  end.

Ltac hs_solver := grind idtac.

Obligation Tactic := solve [hs_solver].
