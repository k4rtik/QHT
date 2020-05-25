Require Import Eqdep.

Set Implicit Arguments.

(** * Extensional equality of functions
 perhaps not needed as provided by
 Coq.Logic.FunctionalExtensionality *)

Axiom ext_eq : forall T1 T2 (f1 f2 : T1 -> T2),
    (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Set) (f1 f2 : T1 -> T2),
    (forall x, f1 x = f2 x) -> f1 = f2.
  intros T1 T2 f1 f2 H.
  rewrite (ext_eq f1 f2).
  - reflexivity.
  - intros x. rewrite H. reflexivity.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.

(** * Dynamic Packages *)

Inductive dynamic : Type :=
  | Dyn : forall T, T -> dynamic.

Theorem Dyn_injT : forall T (x y : T),
    Dyn x = Dyn y -> x = y.
  intros T x y H.
  injection H.
  apply inj_pair2.
Qed.

Theorem Dyn_inj : forall (T : Set) (x y : T),
    Dyn x = Dyn y -> x = y.
  intros T x y H.
  apply Dyn_injT.
  exact H.
Qed.

Theorem Dyn_inj_Some' : forall (d1 d2 : dynamic),
    Some d1 = Some d2 -> d1 = d2.
  intros d1 d2 H.
  congruence.
Qed.

Theorem Dyn_inj_Some : forall (T : Set) (x y : T),
    Some (Dyn x) = Some (Dyn y) -> x = y.
  intros T x y H.
  apply Dyn_inj.
  apply Dyn_inj_Some'.
  exact H.
Qed.
