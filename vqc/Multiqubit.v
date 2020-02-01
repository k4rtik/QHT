(** * Multiqubit: Entanglement and Measurement *)

From VQC Require Import Qubit.
Require Import Bool.
Require Import List.
Import ListNotations.

(** * Multiple qubits and entanglement *)

(** FULL: Quantum computing wouldn't be very interesting if we only
    had lone qubits. In order to get the power of quantum computing we
    need _Quantum States_ with many qubits. We express these using a
    vector of size 2^n, where n is the number of qubits.  *)

Notation QState n := (Vector (2^n)).

(** First, let's look at expressing the basis states: *)
Definition qubit (x : nat) : Qubit := if x =? 0 then ∣0⟩ else ∣1⟩.
Arguments qubit x _ _ /.

Notation "'∣' x '⟩'" := (qubit x).
Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).

Check (∣0,0,1,0⟩).

Lemma test_qubits : ∣0,1⟩ = ∣0⟩ ⊗ ∣1⟩. Proof. reflexivity. Qed.

Lemma qubit_decomposition2 : forall (ϕ : QState 2), exists (α β γ δ: C),
  ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩.
Proof.
  (* WORKINCLASS *)
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat, (ϕ 2 0)%nat, (ϕ 3 0)%nat.
  lma.
Qed.
  (* /WORKINCLASS *)

(** Certain unitary matrices act on multiple qubits *)

(**
[[
    CNOT:  1000
           0100
           0001
           0010
]]
*)

Definition CNOT : Unitary 4 := l2M [[1;0;0;0];
                                    [0;1;0;0];
                                    [0;0;0;1];
                                    [0;0;1;0]].

Lemma CNOT00 : CNOT × ∣0,0⟩ == ∣0,0⟩. Proof. lma. Qed.
Lemma CNOT01 : CNOT × ∣0,1⟩ == ∣0,1⟩. Proof. lma. Qed.
Lemma CNOT10 : CNOT × ∣1,0⟩ == ∣1,1⟩. Proof. lma. Qed.
Lemma CNOT11 : CNOT × ∣1,1⟩ == ∣1,0⟩. Proof. lma. Qed.

Lemma CNOTp1 : CNOT × (∣+⟩ ⊗ ∣0⟩) == /√2 * ∣0,0⟩ + /√2 * ∣1,1⟩.
Proof. lma. Qed.

(** This particular qubit pair has a name: We call it a Bell state.
    (Also known as an EPR pair.) *)

Definition bell : QState 2 := /√2 * ∣0,0⟩ + /√2 * ∣1,1⟩.

(** We can also apply single qubit gates to different qubits in a
    single system, again by using the Kronecker product: *)

Lemma XH01 : (X ⊗ H) × ∣0,1⟩ == ∣1⟩⊗∣-⟩.
Proof. lma. Qed.

Lemma HH01 : (H ⊗ H) × ∣0,1⟩ == ∣+⟩⊗∣-⟩.
Proof. lma. Qed.

(** Let's generate a Bell pair from basis qubits and prove its
    correctness *)

Definition bell' : QState 2 := CNOT × (H ⊗ I 2) × ∣0,0⟩.

Lemma bell_bell' : bell == bell'.
Proof.
  (* WORKINCLASS *)
  lma.
Qed.
  (* /WORKINCLASS *)

(* Some other useful two qubit gates *)

Definition NOTC : Unitary 4 := l2M [[1; 0; 0; 0];
                                    [0; 0; 0; 1];
                                    [0; 0; 1; 0];
                                    [0; 1; 0; 0]].

Definition CZ : Unitary 4:= l2M [[1;0;0;0];
                                 [0;1;0;0];
                                 [0;0;1;0];
                                 [0;0;0;-(1)]].

Definition SWAP : Unitary 4 := l2M [[1;0;0;0];
                                    [0;0;1;0];
                                    [0;1;0;0];
                                    [0;0;0;1]].

Lemma SWAPxy : forall x y, SWAP × ∣ x,y ⟩ == ∣ y,x ⟩.
Proof. intros. destruct x,y; lma. Qed.


(** * Total and partial measurement *)

(** Let's start by recapping measurement on one qubit in a slightly
    different form. *)

Inductive measure' : QState 1 -> (R * QState 1) -> Prop :=
|  measure0' : forall ϕ α β,
               ϕ == α * ∣0⟩ + β * ∣1⟩ ->
               measure' ϕ (Cnorm2 α, ∣0⟩)
|  measure1' : forall ϕ α β,
               ϕ == α * ∣0⟩ + β * ∣1⟩ ->
               measure' ϕ (Cnorm2 β, ∣1⟩).

(** ** Total measurement *)

(** We can define total measurement on two qubits similarly: *)

Inductive measure_total : QState 2 -> (R * QState 2) -> Prop :=
| measure00 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 α, ∣0,0⟩)
| measure01 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 β, ∣0,1⟩)
| measure10 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 γ, ∣1,0⟩)
| measure11 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 δ, ∣1,1⟩).

(* HIDE:

There are two ways to extend our previous notion of measurement to
    multiple qubit systems. Let's start off with the easier one.

Inductive measure_total : QState 2 -> (C * QState 2) -> Prop :=
| measure00 : forall (ϕ : Qubit) (p : C),
              p <> 0 ->
              measure_total ϕ (p, ∣0,0⟩)
| measure01 : forall (ϕ : Qubit) (p : C),
              p = norm2 (ϕ 1%nat 0%nat) ->
              p <> 0 ->
              measure_total ϕ (p, ∣0,1⟩)
| measure10 : forall (ϕ : Qubit) (p : C),
              p = norm2 (ϕ 2%nat 0%nat) ->
              p <> 0 ->
              measure_total ϕ (p, ∣1,0⟩)
| measure11 : forall (ϕ : Qubit) (p : C),
              p = norm2 (ϕ 3%nat 0%nat) ->
              p <> 0 ->
              measure_total ϕ (p, ∣1,1⟩).
*)


Lemma measure_plus_minus : measure_total (∣+⟩⊗∣-⟩) ((/4)%R,  ∣0,1⟩).
Proof.
  (* WORKINCLASS *)
  replace (/4)%R with (Cnorm2 (-/2)) by (simpl; lra).
  apply measure01 with (α := /2) (γ := /2) (δ := -/2).
  by_cell; autounfold with U_db; simpl; C_field.
Qed.
  (* /WORKINCLASS *)

Lemma measure_bell : measure_total bell ((/2)%R,  ∣1,1⟩).
Proof.
  (* WORKINCLASS *)
  replace (/2)%R with (Cnorm2 (/√2)) by (simpl; R_field; nonzero).
  apply measure11 with (α := /√2) (γ := 0) (β := 0).
  unfold bell; simpl.
  by_cell; autounfold with U_db; simpl; C_field.
Qed.
  (* /WORKINCLASS *)

(** ** Partial measurement *)

Inductive measure_partial : nat -> QState 2 -> (R * QState 2) -> Prop :=
| measure_p_1_0 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
                  p = (⎸α⎸² + ⎸β⎸²)%R ->
                  ϕ' == /√p * (α * ∣0,0⟩ + β * ∣0,1⟩) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_1_1 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
                  p = (⎸γ⎸² + ⎸δ⎸²)%R ->
                  ϕ' == /√p * (γ * ∣1,0⟩ + δ * ∣1,1⟩) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_2_0 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
                  p = (⎸α⎸² + ⎸γ⎸²)%R ->
                  ϕ' == /√p * (α * ∣0,0⟩ + γ * ∣1,0⟩) ->
                  measure_partial 2 ϕ (p, ϕ')
| measure_p_2_1 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α * ∣0,0⟩ + β * ∣0,1⟩ + γ * ∣1,0⟩ + δ * ∣1,1⟩ ->
                  p = (⎸β⎸² + ⎸δ⎸²)%R ->
                  ϕ' == /√p * (β * ∣0,1⟩ + δ * ∣1,1⟩) ->
                  measure_partial 2 ϕ (p, ϕ').

(** HIDE: Before we can define measurement, we will want to define two
    _projection operators_.

Definition proj1 (x : nat) (ϕ : QState 2) := (outer_product ∣x⟩ ∣x⟩ ⊗ I 2) × ϕ.
Definition proj2 (x : nat) (ϕ : QState 2) := (I 2 ⊗ outer_product ∣x⟩ ∣x⟩) × ϕ.

Lemma proj1_0 : forall (ϕ ψ : Qubit), proj1 0 (ϕ ⊗ ψ) == (ϕ 0 0)%nat * (∣0⟩ ⊗ ψ).
Proof. intros ϕ ψ. lma. Qed.

Lemma proj1_1 : forall (ϕ ψ : Qubit), proj1 1 (ϕ ⊗ ψ) == (ϕ 1 0)%nat * (∣1⟩ ⊗ ψ).
Proof. intros ϕ ψ. lma. Qed.

Lemma proj2_0 : forall (ϕ ψ : Qubit), proj2 0 (ϕ ⊗ ψ) == (ψ 0 0)%nat * (ϕ ⊗ ∣0⟩).
Proof. intros ϕ ψ. lma. Qed.

Lemma proj2_1 : forall (ϕ ψ : Qubit), proj2 1 (ϕ ⊗ ψ) == (ψ 1 0)%nat * (ϕ ⊗ ∣1⟩).
Proof. intros ϕ ψ. lma. Qed.

Inductive measure_partial : nat -> QState 2 -> (C * QState 2) -> Prop :=
| measure_p_1_0 : forall (ϕ ϕ' : QState 2) (p : C),
                  p = norm2 (ϕ 0 0)%nat + norm2 (ϕ 1 0)%nat  ->
                  p <> 0 ->
                  ϕ' == /√(fst p) * (proj1 0 ϕ) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_1_1 : forall (ϕ ϕ' : QState 2) (p : C),
                  p = norm2 (ϕ 2 0)%nat + norm2 (ϕ 3 0)%nat  ->
                  p <> 0 ->
                  ϕ' == /√(fst p) * (proj1 1 ϕ) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_2_0 : forall (ϕ ϕ' : QState 2) (p : C),
                  p = norm2 (ϕ 0 0)%nat + norm2 (ϕ 2 0)%nat  ->
                  p <> 0 ->
                  ϕ' == /√(fst p) * (proj2 0 ϕ) ->
                  measure_partial 2 ϕ (p, ϕ')
| measure_p_2_1 : forall (ϕ ϕ' : QState 2) (p : C),
                  p = norm2 (ϕ 1 0)%nat + norm2 (ϕ 3 0)%nat  ->
                  p <> 0 ->
                  ϕ' == /√(fst p) * (proj2 1 ϕ) ->
                  measure_partial 2 ϕ (p, ϕ').

*)


Lemma partial_measure_plus_minus : measure_partial 1 (∣+⟩⊗∣-⟩) ((/2)%R,  ∣0⟩⊗∣-⟩).
Proof.
  eapply measure_p_1_0 with (α := /2) (β := -/2) (γ := /2) (δ := -/2).
  - by_cell; autounfold with U_db; simpl; C_field.
  - simpl; R_field.
  - by_cell; autounfold with U_db; simpl; C_field.
Qed.

Lemma partial_measure_bell : measure_partial 1 bell ((/2)%R,  ∣1,1⟩).
Proof.
  (* WORKINCLASS *)
  eapply measure_p_1_1  with (α := /√2) (β := 0) (γ := 0) (δ := /√2).
  - Msimpl. reflexivity.
  - simpl; R_field.
  - by_cell; autounfold with U_db; simpl; C_field.
Qed.
  (* /WORKINCLASS *)


Lemma NOTC00 : NOTC × ∣ 0, 0 ⟩ == ∣ 0, 0 ⟩. Proof. lma. Qed.
Lemma NOTC01 : NOTC × ∣ 0, 1 ⟩ == ∣ 1, 1 ⟩. Proof. lma. Qed.
Lemma NOTC10 : NOTC × ∣ 1, 0 ⟩ == ∣ 1, 0 ⟩. Proof. lma. Qed.
Lemma NOTC11 : NOTC × ∣ 1, 1 ⟩ == ∣ 0, 1 ⟩. Proof. lma. Qed.

(** ** Automation *)
Hint Unfold qubit CNOT NOTC CZ SWAP : U_db.

Hint Rewrite @Mmult_plus_dist_l @Mmult_plus_dist_r @kron_plus_dist_l @kron_plus_dist_r @Mscale_plus_dist_r : ket_db.
Hint Rewrite @Mscale_mult_dist_l @Mscale_mult_dist_r @Mscale_kron_dist_l @Mscale_kron_dist_r : ket_db.
Hint Rewrite @Mscale_assoc @Mmult_assoc : ket_db.
(* HIDE: Hint Rewrite <- Mplus_assoc kron_assoc : ket_db. *)
Hint Rewrite @Mmult_1_l @Mmult_1_r @kron_1_l @kron_1_r @Mscale_0_l @Mscale_1_l @Mplus_0_l @Mplus_0_r : ket_db.
Hint Rewrite @kron_mixed_product : ket_db.

(* Quantum-specific identities *)
Hint Rewrite X0 X1 Y0 Y1 Z0 Z1 H0 H1 Hplus Hminus : ket_db.
Hint Rewrite CNOT00 CNOT01 CNOT10 CNOT11 CNOTp1 NOTC00 NOTC01 NOTC10 NOTC11 SWAPxy : ket_db.

(* Examples using ket_db *)
Lemma XYZ0 : -i * X × Y × Z × ∣ 0 ⟩ == ∣ 0 ⟩.
(* WORKINCLASS *)
Proof.
  autorewrite with ket_db.
  replace (-i * i)%C with 1 by lca.
  rewrite Mscale_1_l.
  easy.
Qed.
(* /WORKINCLASS *)

(* EX1! (XYZ1) *)
Lemma XYZ1 : -i * X × Y × Z × ∣ 1 ⟩ == ∣ 1 ⟩.
Proof.
(* ADMITTED *)
  autorewrite with ket_db.
  replace (-i * -(1) * -i)%C with 1 by lca.
  rewrite Mscale_1_l; reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(*
Ltac qubit_simplify :=
  intros;
  autorewrite with ket_db;
  repeat match goal with
  | [|- context[(?A ⊗ ?B) × (?C ⊗ ?D) ]] =>
    match type of C with
    | Vector _ => match type of D with
                 | Vector _ => rewrite (kron_mixed_product A B C D);
                              autorewrite with ket_db
                 end
    end
  end;
  try match goal with
  | [ |- ?a * ∣ 0 ⟩ + ?b * ∣ 1 ⟩ == ?a' * ∣ 0 ⟩ + ?b' * ∣ 1 ⟩ ] =>
    replace a with a' by lca; replace b with b' by lca
  end.
*)

Ltac qubit_simplify :=
  intros;
  autorewrite with ket_db;
  repeat match goal with
  | [ |- context[(?A ⊗ ?B) × (?C ⊗ ?D) ]] =>
    match type of C with
    | Vector _ => match type of D with
                 | Vector _ => rewrite (kron_mixed_product A B C D);
                              autorewrite with ket_db
                 end
    end
  end;
  try match goal with
  | [ |- ?a * ∣ 0 ⟩ + ?b * ∣ 1 ⟩ == ?a' * ∣ 0 ⟩ + ?b' * ∣ 1 ⟩ ] =>
    replace a with a' by lca; replace b with b' by lca
  end.


Lemma XYZ : forall α β,
  -i * X × Y × Z × (α * ∣ 0 ⟩ + β * ∣ 1 ⟩) == α * ∣ 0 ⟩ + β * ∣ 1 ⟩.
Proof.
  qubit_simplify; reflexivity.
Qed.


(* *)
