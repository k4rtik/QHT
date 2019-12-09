(** * Multiqubit: Entanglement and Measurement *)

From VQC Require Import Qubit.
Require Import Bool.

Opaque C.

(* ################################################################# *)
(** * Multiple qubits and entanglement *)

(** Quantum computing wouldn't be very interesting if we only
    had lone qubits. In order to get the power of quantum computing we
    need _Quantum States_ with many qubits. We express these using a
    vector of size 2^n, where n is the number of qubits.  *)

Notation QState n := (Vector (2^n)).

(** First, let's look at expressing the basis states: *)
Definition qubit (x : nat) : Qubit := if x =? 0 then ∣0⟩ else ∣1⟩.
Notation "'∣' x '⟩'" := (qubit x).
Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).

Check (∣0,0,1,0⟩).

Lemma test_qubits : ∣0,1⟩ = ∣0⟩ ⊗ ∣1⟩. Proof. reflexivity. Qed.

(** Certain unitary matrices act on multiple qubits *)

(**

    CNOT:  1000
           0100
           0001
           0010
*)

Definition CNOT : Unitary 4 :=
  fun i j => if ((i =? j) && (i <? 2)) || (i + j =? 5) then 1 else 0.

Lemma CNOT00 : CNOT × ∣0,0⟩ == ∣0,0⟩. Proof. lma. Qed.
Lemma CNOT01 : CNOT × ∣0,1⟩ == ∣0,1⟩. Proof. lma. Qed.
Lemma CNOT10 : CNOT × ∣1,0⟩ == ∣1,1⟩. Proof. lma. Qed.
Lemma CNOT11 : CNOT × ∣1,1⟩ == ∣1,0⟩. Proof. lma. Qed.

Lemma CNOTp1 : CNOT × (∣+⟩ ⊗ ∣0⟩) == /√2 .* ∣0,0⟩ .+ /√2 .* ∣1,1⟩.
Proof. lma. Qed.

(** This particular qubit pair has a name: We call it a Bell state.
    (Also known as an EPR pair.) *)

Definition bell : QState 2 := /√2 .* ∣0,0⟩ .+ /√2 .* ∣1,1⟩.

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
  (* WORKED IN CLASS *)
  lma.
Qed.

(* ################################################################# *)
(** * Total and partial measurement *)

(** Let's start by recapping measurement on one qubit in a slightly
    different form. *)

Inductive measure' : QState 1 -> (R * QState 1) -> Prop :=
|  measure0' : forall ϕ α β,
               ϕ == α .* ∣0⟩ .+ β .* ∣1⟩ ->
               measure' ϕ (Cnorm2 α, ∣0⟩)
|  measure1' : forall ϕ α β,
               ϕ == α .* ∣0⟩ .+ β .* ∣1⟩ ->
               measure' ϕ (Cnorm2 β, ∣1⟩).

(* ================================================================= *)
(** ** Total measurement *)

(** We can define total measurement on two qubits similarly: *)

Inductive measure_total : QState 2 -> (R * QState 2) -> Prop :=
| measure00 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 α, ∣0,0⟩)
| measure01 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 β, ∣0,1⟩)
| measure10 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 γ, ∣1,0⟩)
| measure11 : forall (ϕ : QState 2) (α β γ δ : C),
              ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
              measure_total ϕ (Cnorm2 δ, ∣1,1⟩).

Lemma measure_plus_minus : measure_total (∣+⟩⊗∣-⟩) ((/4)%R,  ∣0,1⟩).
Proof.
  (* WORKED IN CLASS *)
  replace (/4)%R with (Cnorm2 (-/2)) by (simpl; lra).
  apply measure01 with (α := /2) (γ := /2) (δ := -/2).
  unfold Cnorm2, q_plus, q_minus, kron, qubit, qubit0, qubit1, Mscale, Mplus; simpl.
  by_cell; C_field.
Qed.

Lemma measure_bell : measure_total bell ((/2)%R,  ∣1,1⟩).
Proof.
  (* WORKED IN CLASS *)
  replace (/2)%R with (Cnorm2 (/√2)) by (simpl; R_field; nonzero).
  apply measure11 with (α := /√2) (γ := 0) (β := 0).
  unfold bell; simpl.
  unfold qubit, qubit0, qubit1, Mplus, Mscale, kron; simpl.
  by_cell; C_field.
Qed.

(* ================================================================= *)
(** ** Partial measurement *)

Inductive measure_partial : nat -> QState 2 -> (R * QState 2) -> Prop :=
| measure_p_1_0 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
                  p = (Cnorm2 α + Cnorm2 β)%R ->
                  ϕ' == /√p .* (α .* ∣0,0⟩ .+ β .* ∣0,1⟩) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_1_1 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
                  p = (Cnorm2 γ + Cnorm2 δ)%R ->
                  ϕ' == /√p .* (γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩) ->
                  measure_partial 1 ϕ (p, ϕ')
| measure_p_2_0 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
                  p = (Cnorm2 α + Cnorm2 γ)%R ->
                  ϕ' == /√p .* (α .* ∣0,0⟩ .+ γ .* ∣1,0⟩) ->
                  measure_partial 2 ϕ (p, ϕ')
| measure_p_2_1 : forall (ϕ ϕ' : QState 2) (α β γ δ : C) (p : R),
                  ϕ == α .* ∣0,0⟩ .+ β .* ∣0,1⟩ .+ γ .* ∣1,0⟩ .+ δ .* ∣1,1⟩ ->
                  p = (Cnorm2 β + Cnorm2 δ)%R ->
                  ϕ' == /√p .* (β .* ∣0,1⟩ .+ δ .* ∣1,1⟩) ->
                  measure_partial 2 ϕ (p, ϕ').

Lemma partial_measure_plus_minus : measure_partial 1 (∣+⟩⊗∣-⟩) ((/2)%R,  ∣0⟩⊗∣-⟩).
Proof.
  eapply measure_p_1_0 with (α := /2) (β := -/2) (γ := /2) (δ := -/2).
  - unfold Cnorm2, q_plus, q_minus, Mplus, Mscale, kron; simpl.
    unfold qubit, qubit0, qubit1; simpl.
    by_cell; C_field.
  - simpl; R_field.
  - unfold Cnorm2, q_plus, q_minus, Mplus, Mscale, kron; simpl.
    unfold qubit, qubit0, qubit1; simpl.
    by_cell; C_field.
Qed.

Lemma partial_measure_bell : measure_partial 1 bell ((/2)%R,  ∣1,1⟩).
Proof.
  (* WORKED IN CLASS *)
  eapply measure_p_1_1  with (α := /√2) (β := 0) (γ := 0) (δ := /√2).
  - unfold Cnorm2, bell; simpl.
    unfold qubit, qubit0, qubit1, Mplus, Mscale, kron; simpl.
    by_cell; C_field.
  - simpl; R_field.
  - unfold qubit, qubit0, qubit1, Mplus, Mscale, kron; simpl.
    by_cell; C_field.
Qed.

(* *)

(* Wed Dec 4 22:25:44 EST 2019 *)
