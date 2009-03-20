Require Import c_util.
Require Import CRreal.
Set Implicit Arguments.
Open Local Scope CR_scope.

(* We require CR because we use it for Time.
 Todo: Take an arbitrary (C)Ring/(C)Field for Time, so that
 the classical development does not need a separate concrete module. *)

Let Time := CRasCSetoid.
Let Duration := NonNegCR.

Record Flow (X: CSetoid): Type :=
  { flow_morphism:> binary_setoid_morphism X Time X
  ; flow_zero: forall x, flow_morphism x ('0) [=] x
  ; flow_additive: forall x t t',
      flow_morphism x (t + t') [=] flow_morphism (flow_morphism x t) t'
  }.

Section product_flow.

  Variables (X Y: CSetoid) (fx: Flow X) (fy: Flow Y).

  Let f (xy: ProdCSetoid X Y) (t: Time): ProdCSetoid X Y :=
    (fx (fst xy) t, fy (snd xy) t).

  Let fm: binary_setoid_morphism (ProdCSetoid X Y) CRasCSetoid (ProdCSetoid X Y).
  Proof with auto.
    apply (Build_binary_setoid_morphism _ _ _ f).
    intros.
    destruct a. destruct a'. simpl in *.
    destruct H.
    split; apply bsm_mor...
  Defined.

  Definition product_flow: Flow (ProdCSetoid X Y).
  Proof with auto.
    apply (Build_Flow fm); destruct x; simpl.
    destruct fm. simpl.
      split; apply flow_zero.
    split; apply flow_additive.
  Defined.

End product_flow.
