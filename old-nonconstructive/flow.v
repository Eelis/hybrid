
Require Import Reals.
Set Implicit Arguments.
Open Local Scope R_scope.

(* We require CR because we use it for Time.
 Todo: Take an arbitrary (C)Ring/(C)Field for Time, so that
 the classical development does not need a separate concrete module. *)

Let Time := R.
Let Duration := { r: R | r >= 0 }.

Program Definition immediately: Duration := 0.
Next Obligation. right. reflexivity. Defined.

Program Definition duration_plus (d d': Duration): Duration := d + d'.
Next Obligation.
  destruct d. destruct d'. simpl.
  replace 0 with (0+0).
    apply Rplus_ge_compat; auto.
  field.
Qed.

Record Flow (X: Set): Type :=
  { flow_fun:> X -> Time -> X
  ; flow_zero: forall x, flow_fun x 0 = x
  ; flow_additive: forall x t t',
      flow_fun x (t + t') = flow_fun (flow_fun x t) t'
  }.

Section product_flow.

  Variables (X Y: Set) (fx: Flow X) (fy: Flow Y).

  Let f (xy: X * Y) (t: Time): X * Y :=
    (fx (fst xy) t, fy (snd xy) t).

  Definition product_flow: Flow (X * Y).
  Proof with auto.
    apply (Build_Flow f); destruct x; unfold f; simpl; intros.
      do 2 rewrite flow_zero...
    do 2 rewrite flow_additive...
  Defined.

End product_flow.

