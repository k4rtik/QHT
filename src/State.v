Require Import QHTT.Axioms.
Require Import Arith.

Definition loc := nat.
Definition val := dynamic%type.

Definition state := loc -> option val.


Definition empty : state := fun _ => None.

Definition singleton (l : loc) (v : val) : state :=
  fun l' => if eq_nat_dec l l' then Some v else None.
