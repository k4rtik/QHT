(** * Qubit: The Building Blocks of Quantum Computing *)

From VQC Require Export Matrix.
Require Import FunctionalExtensionality.
Require Import Bool.

(* ################################################################# *)
(** * Qubits *)

(** Let's start with the basic building block of quantum computing :
    The qubit *)

Notation Qubit := (Vector 2).

Definition WF_Qubit (ϕ : Qubit) : Prop := ϕ† × ϕ == I 1.

(** Note that this is equivalent to saying that [⟨ϕ,ϕ⟩ = 1],
    which partially explains the notation for qubits below. *)

(** **** Exercise: 2 stars, standard, recommended (WF_Qubit_alt)

    Prove this statement. *)
Theorem WF_Qubit_alt : forall ϕ : Qubit, WF_Qubit ϕ <-> ⟨ϕ, ϕ⟩ = 1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Definition qubit0 : Qubit := fun i j => if (i =? 0)%nat then 1 else 0.
Definition qubit1 : Qubit := fun i j => if (i =? 1)%nat then 1 else 0.

Notation "∣ 0 ⟩" := qubit0.
Notation "∣ 1 ⟩" := qubit1.

(** A brief aside : Emacs and other text editors, as well as a famous
    xkcd comic and any well-developed aethestics, don't like seeing
    left angle braces without corresponding right angle braces. (Blame
    here goes to Paul Dirac.) Since emacs' auto-indentation will
    probably go out of whack at this point in the file, I recommend
    disabling it via M-x electric-indent-mode. *)

(** With that done, let's show that our two "basis" qubits are indeed
    proper qubits *)

Lemma WF_qubit0 : WF_Qubit ∣0⟩. Proof. lma. Qed.
Lemma WF_qubit1 : WF_Qubit ∣1⟩. Proof. lma. Qed.

Lemma qubit_decomposition : forall (ϕ : Qubit), exists (α β : C), ϕ == α .* ∣0⟩ .+ β .* ∣1⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat.
  lma.
Qed.

(* ################################################################# *)
(** * Unitaries *)

(** The standard way of operating on a vector is multiplying it by a
    matrix. If A is an n × n matrix and v is a n-dimensional vector,
    then A v is another n-dimensional vector.

    In the quantum case, we want to restrict A so that for any qubit
    ϕ, A ϕ is also a valid qubit. Let's try to figure out what this
    restriction will look like in practice.

 *)

Lemma valid_qubit_function : exists (P : Matrix 2 2 -> Prop),
  forall (A : Matrix 2 2) (ϕ : Qubit),
  P A -> WF_Qubit ϕ -> WF_Qubit (A × ϕ).
Proof.
  (* WORKED IN CLASS *)
  eexists.
  intros A ϕ p Q.
  unfold WF_Qubit in *.
  rewrite Mmult_adjoint.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc (A†)).
  assert (P: A† × A = I 2). apply p.
  rewrite P.
  rewrite Mmult_1_l.
  apply Q.
Qed.

(** We will call these matrices _unitary_ for preserving the unit
    inner product *)

Notation Unitary n := (Matrix n n).

Definition WF_Unitary {n} (U : Unitary n) := U † × U == I n.

(** We'll start with three useful unitaries: The identity (I), the
    Pauli X matrix (X) and the Hadamard matrix (H): *)

(**

      X = 01
          10
*)

Definition X : Unitary 2 :=
  fun i j => if i + j =? 1 then 1 else 0.

Lemma WF_X : WF_Unitary X. Proof. lma. Qed.

Lemma X0 : X × ∣0⟩ == ∣1⟩. Proof. lma. Qed.
Lemma X1 : X × ∣1⟩ == ∣0⟩. Proof. lma. Qed.

(**

      Z = 1 0
          0 -1
*)

Definition Z : Unitary 2 :=
  fun i j => if i + j =? 0 then 1 else if i + j =? 2 then -1 else 0.

Lemma WF_Z : WF_Unitary Z. Proof. lma. Qed.

Lemma Z0 : Z × ∣0⟩ == ∣0⟩. Proof. lma. Qed.
Lemma Z1 : Z × ∣1⟩ == -1 .* ∣1⟩. Proof. lma. Qed.

(**

      H = 1/√2 * 1  1
                 1 -1

**)

Definition H : Unitary 2 :=
  fun i j => if i + j =? 2 then -/√2 else /√2.

Lemma WF_H : WF_Unitary H.
Proof.
  unfold WF_Unitary, Mmult, adjoint, H, I; simpl.
  by_cell; try lca.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
Qed.

Definition q_plus : Qubit := (fun _ _ => /√2).
Definition q_minus : Qubit := (fun i j => if i =? 0 then /√2 else -/√2).

Notation "∣ + ⟩" := q_plus.
Notation "∣ - ⟩" := q_minus.

(** It's worth noticing that if we apply a Hadamard twice, we get our
    initial state back: *)

Lemma Hplus : H × ∣+⟩ == ∣0⟩.
Proof.
  unfold H, Mmult, q_plus.
  by_cell; try lca.
  C_field_simplify.
  lca.
Qed.

(** **** Exercise: 2 stars, standard, recommended (Htwice)

    Prove the general form of double Hadamard application *)
Theorem Htwice : forall ϕ : Qubit, H × (H × ϕ) == ϕ.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** * Measurement **)

(** Measurement is a _probabilistic_ operation on a qubit. Since
    there are (generally) multiple possible outcomes of a measurement,
    we will represent measurement as a relation.

    Note that some measurements, those with 0 probability, will never occur.
*)

Inductive measure : Qubit -> (R * Qubit) -> Prop :=
| measure0 : forall (ϕ : Qubit), measure ϕ (Cnorm2 (ϕ 0%nat 0%nat), ∣0⟩)
| measure1 : forall (ϕ : Qubit), measure ϕ (Cnorm2 (ϕ 1%nat 0%nat), ∣1⟩).

(** **** Exercise: 3 stars, standard, optional (measure_sum)

    State and prove that the sum of the measure outcomes for a valid qubit will always be 1.
    Hint: Compare the definitions of norm2 and inner_product. *)
(* FILL IN HERE *)

(** [] *)

Lemma measure0_idem : forall ϕ p, measure ∣0⟩ (p, ϕ) -> p <> 0 -> ϕ = ∣0⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  inversion H0; subst.
  - reflexivity.
  - contradict H1. lra.
Qed.

(** **** Exercise: 1 star, standard, recommended (measure1_idem)  *)
Lemma measure1_idem : forall ϕ p, measure ∣1⟩ (p, ϕ) -> p <> 0 -> ϕ = ∣1⟩.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma measure_plus : forall ϕ p, measure ∣+⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros.
  inversion H0; subst.
  - R_field.
  - R_field.
Qed.

(** **** Exercise: 2 stars, standard, recommended (measure_minus)  *)
Lemma measure_minus : forall ϕ p, measure ∣-⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* *)

(* Wed Dec 4 22:25:44 EST 2019 *)
