
Require Import Morphisms.
Require Export hybrid.geometry.
Require Export hybrid.vector_setoid.

Set Implicit Arguments.
Open Local Scope CR_scope.

Definition HCube n : Type := vector Range n.
Definition OpenQHCube n : Set := vector OpenQRange n.
Definition OpenHCube n : Type := vector OpenRange n.

Definition HyperPoint n : CSetoid := vecCSetoid CRasCSetoid n.
