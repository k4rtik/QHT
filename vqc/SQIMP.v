(** * SQIMP: Quantum Programming in Coq **)

Require Import Bool.
Require Import Setoid.
Require Import Reals.
Require Import Psatz.
From VQC Require Import Matrix.
From VQC Require Import Qubit.
From VQC Require Import Multiqubit.

(** * A Small Quantum Imperative Language **)

Open Scope C_scope.
Open Scope matrix_scope.

(* ================================================================= *)
(** ** Unitaries as gates *)

Inductive Gate : nat -> Set :=
| G_I     : nat -> Gate 1
| G_H     : nat -> Gate 1
| G_X     : nat -> Gate 1
| G_Z     : nat -> Gate 1
| G_CNOT  : nat -> nat -> Gate 2.

(** All of our programs will assume a fixed set of qubit registers.
    [app U q1 q2] will apply U to the registers q1 and q2. *)

Inductive com : Set :=
| skip : com
| seq  : com -> com -> com
| app  : forall {n}, Gate n -> com.

Definition SKIP := skip.
Definition I' q := app (G_H q).
Definition H' q := app (G_H q).
Definition X' q := app (G_X q).
Definition Z' q := app (G_Z q).
Definition CNOT' q1 q2 := app (G_CNOT q1 q2).

Declare Scope com_scope.
Notation "p1 ; p2" := (seq p1 p2) (at level 50) : com_scope.

Arguments H' q%nat.
Arguments X' q%nat.
Arguments Z' q%nat.
Arguments CNOT' q1%nat q2%nat.

Open Scope com_scope.

(** A simple program to construct a bell state *)
Definition bell_com := H' 0; CNOT' 0 1.

(** ** Denotation of Commands **)

(** Pad the given unitary with identities *)
Definition pad (n to dim : nat) (U : Unitary (2^n)) : Unitary (2^dim) :=
  if (to + n <=? dim)%nat
  then I (2^to) ⊗ U ⊗ I (2^(dim - n - to))
  else Zero (2^dim) (2^dim).

Definition NOTC : Unitary 4 := fun i j => if (i + j =? 0) || (i + j =? 4) then 1 else 0.

Definition eval_cnot (dim m n: nat) : Unitary (2^dim) :=
  if (m + 1 =? n) then
    pad 2 m dim CNOT
  else if (n + 1 =? m) then
    pad 2 n dim NOTC
  else
    Zero _ _.

Definition geval {n} (dim : nat) (g : Gate n) : Unitary (2^dim) :=
  match g with
  | G_I i => pad n i dim (I 2)
  | G_H i => pad n i dim H
  | G_X i => pad n i dim X
  | G_Z i => pad n i dim Z
  | G_CNOT i j => eval_cnot dim i j
  end.

Fixpoint eval (dim : nat) (c : com) : Unitary (2^dim) :=
  match c with
  | skip    => I (2^dim)
  | app g   => geval dim g
  | c1 ; c2 => eval dim c2 × eval dim c1
  end.

Arguments eval_cnot /.
Arguments geval /.
Arguments pad /.

Lemma eval_bell : (eval 2 bell_com) × ∣0,0⟩ == bell.
Proof.
  (* WORKED IN CLASS *)
  lma.
Qed.

(* ================================================================= *)
(** ** Relating Quantum Programs *)

Definition com_equiv (c1 c2 : com) := forall dim, eval dim c1 == eval dim c2.

Infix "≡" := com_equiv (at level 80): com_scope.

Lemma com_equiv_refl : forall c1, c1 ≡ c1.
Proof. easy. Qed.

Lemma com_equiv_sym : forall c1 c2, c1 ≡ c2 -> c2 ≡ c1.
Proof. easy. Qed.

Lemma com_equiv_trans : forall c1 c2 c3, c1 ≡ c2 -> c2 ≡ c3 -> c1 ≡ c3.
Proof.
  intros c1 c2 c3 H12 H23 dim.
  unfold com_equiv in H12.
  rewrite H12. easy.
Qed.

Lemma seq_assoc : forall c1 c2 c3, ((c1 ; c2) ; c3) ≡ (c1 ; (c2 ; c3)).
Proof.
  intros c1 c2 c3 dim. simpl.
  rewrite Mmult_assoc. easy.
Qed.

Lemma seq_congruence : forall c1 c1' c2 c2',
    c1 ≡ c1' ->
    c2 ≡ c2' ->
    c1 ; c2 ≡ c1' ; c2'.
Proof.
  intros c1 c1' c2 c2' Ec1 Ec2 dim.
  simpl.
  unfold com_equiv in *.
  rewrite Ec1, Ec2.
  reflexivity.
Qed.

Add Relation com com_equiv
  reflexivity proved by com_equiv_refl
  symmetry proved by com_equiv_sym
  transitivity proved by com_equiv_trans
  as com_equiv_rel.

Add Morphism seq
  with signature (@com_equiv) ==> (@com_equiv) ==> (@com_equiv) as seq_mor.
Proof. intros x y H x0 y0 H0. apply seq_congruence; easy. Qed.

(** ** Superdense coding **)

Definition encode (b1 b2 : bool): com :=
  (if b2 then X' 0 else SKIP);
  (if b1 then Z' 0 else SKIP).

Definition decode : com :=
  CNOT' 0 1;
  H' 0.

Definition superdense (b1 b2 : bool) := bell_com; encode b1 b2; decode.

Definition BtoN (b : bool) : nat := if b then 1 else 0.
Coercion BtoN : bool >-> nat.

Lemma superdense_correct : forall b1 b2, (eval 2 (superdense b1 b2)) × ∣ 0,0 ⟩ == ∣ b1,b2 ⟩.
Proof.
(* WORKED IN CLASS *)
  intros.
  simpl.
  rewrite (kron_1_l H).
  rewrite (kron_1_l CNOT), (kron_1_r CNOT).
  repeat rewrite Mmult_assoc.
  assert (P : CNOT × (H ⊗ I 2 × ∣ 0, 0 ⟩) == bell) by lma.
  rewrite P.
  destruct b1, b2.
  - simpl.
    rewrite (kron_1_l X).
    rewrite (kron_1_l Z).
    assert (P1 : X ⊗ I 2 × bell == / √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩) by lma.
    rewrite P1.
    assert (P2 : Z ⊗ I 2 × (/ √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩)
       == - / √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩) by lma.
    rewrite P2.
    assert (P3 : CNOT × (- / √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩)
       == - / √ (2) .* ∣ 1, 1 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩) by lma.
    rewrite P3.
    by_cell; unfold kron, Mscale, Mmult, Mplus, qubit, H, I; simpl; C_field_simplify; lca.
  - simpl.
    rewrite (kron_1_l Z).
    rewrite Mmult_1_l.
    assert (P1 : Z ⊗ I 2 × bell == / √ (2) .* ∣ 0, 0 ⟩ .+ (-/√ (2)) .* ∣ 1, 1 ⟩) by lma.
    rewrite P1.
    assert (P2 : CNOT × (/ √ (2) .* ∣ 0, 0 ⟩ .+ (-/√ (2)) .* ∣ 1, 1 ⟩)
       == / √ (2) .* ∣ 0, 0 ⟩ .+ (-/√ (2)) .* ∣ 1, 0 ⟩) by lma.
    rewrite P2.
    by_cell; unfold kron, Mscale, Mmult, Mplus, qubit, H, I; simpl; C_field_simplify; lca.
  - simpl.
    rewrite (kron_1_l X).
    rewrite Mmult_1_l.
    assert (P1 : X ⊗ I 2 × bell == / √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩) by lma.
    rewrite P1.
    assert (P2 : CNOT × (/ √ (2) .* ∣ 1, 0 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩)
       == / √ (2) .* ∣ 1, 1 ⟩ .+ / √ (2) .* ∣ 0, 1 ⟩) by lma.
    rewrite P2.
    by_cell; unfold kron, Mscale, Mmult, Mplus, qubit, H, I; simpl; C_field_simplify; lca.
  - simpl.
    rewrite 2 Mmult_1_l.
    assert (P1 : CNOT × bell == ∣+⟩⊗∣0⟩) by lma.
    rewrite P1.
    by_cell; unfold kron, Mmult, q_plus, qubit, H, I; simpl; C_field_simplify; lca.
Qed.





(* Wed Dec 4 22:25:44 EST 2019 *)
