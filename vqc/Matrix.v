(** * Matrix: Lightweight Complex Matrices *)

Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
From VQC Require Export Complex.


(** * Matrix Definitions and Equivalence **)

Open Scope nat_scope.

(** We define a _matrix_ as a simple function from to nats
    (corresponding to a row and a column) to a complex number. In many
    contexts it would make sense to parameterize matrices over numeric
    types, but our use case is fairly narrow, so matrices of complex
    numbers will suffice. *)

Definition Matrix (m n : nat) := nat -> nat -> C.

Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

(** Note that the dimensions of the matrix aren't being used here. In
    practice, a matrix is simply a function on any two nats. However,
    we will used these dimensions to define equality, as well as the
    multiplication and kronecker product operations to follow. *)

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 80).

(** Let's prove some important notions about matrix equality. *)

Lemma mat_equiv_refl : forall {m n} (A : Matrix m n), A == A.
Proof. intros m n A i j Hi Hj. reflexivity. Qed.

Lemma mat_equiv_sym : forall {m n} (A B : Matrix m n), A == B -> B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : forall {m n} (A B C : Matrix m n),
    A == B -> B == C -> A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

(** Now we can use matrix equivalence to rewrite! *)

Lemma mat_equiv_trans2 : forall {m n} (A B C : Matrix m n),
    A == B -> A == C -> B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

(* ################################################################# *)
(** * Basic Matrices and Operations *)

Close Scope nat_scope.
Open Scope C_scope.

Declare Scope matrix_scope.
(** Because we will use these so often, it is good to have them in matrix scope. *)
Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.

Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0.

Definition Mscale {m n : nat} (c : C) (A : Matrix m n) : Matrix m n :=
  fun i j => c * A i j.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := Mscale (at level 40, left associativity) : matrix_scope.

Lemma Mplus_assoc : forall {m n} (A B C : Matrix m n), (A .+ B) .+ C == A .+ (B .+ C).
Proof.
  intros m n A B C i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_comm : forall {m n} (A B : Matrix m n), A .+ B == B .+ A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B i j Hi Hj.
  unfold Mplus.
  lca.
Qed.

Lemma Mplus_0_l : forall {m n} (A : Matrix m n), Zero m n .+ A == A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j Hi Hj.
  unfold Zero, Mplus.
  lca.
Qed.

(* Let's try one without unfolding definitions. *)
Lemma Mplus_0_r : forall {m n} (A : Matrix m n), A .+ Zero m n == A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A.
  rewrite Mplus_comm.
  apply Mplus_0_l.
Qed.

Lemma Mplus3_first_try : forall {m n} (A B C : Matrix m n), (B .+ A) .+ C == A .+ (B .+ C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  Fail rewrite (Mplus_comm B A).
Abort.

(** What went wrong? While we can rewrite using [==], we don't
    know that [.+] _respects_ [==]. That is, we don't know that if
    [A == A'] and [B == B'] then [A .+ B == A' .+ B'] -- or at least, we
    haven't told Coq that.

   Let's take a look at an example of a unary function that doesn't
   respect [==] *)

Definition shift_right {m n} (A : Matrix m n) (k : nat) : Matrix m n :=
  fun i j => A i (j + k)%nat.

Lemma shift_unequal : exists m n (A A' : Matrix m n) (k : nat),
    A == A' /\ ~ (shift_right A k == shift_right A' k).
Proof.
  set (A := (fun i j => if (j <? 2)%nat then 1 else 0) : Matrix 2 2).
  set (A' := (fun i j => if (j <? 3)%nat then 1 else 0) : Matrix 2 2).
  exists _, _, A, A', 1%nat.
  split.
  - intros i j Hi Hj.
    unfold A, A'.
    destruct j as [|[|]]; destruct i as [|[|]]; trivial; lia.
  - intros F.
    assert (1 < 2)%nat by lia.
    specialize (F _ _ H H).
    unfold A, A', shift_right in F.
    simpl in F.
    inversion F; lra.
Qed.

(** Let's show that [.+] does respect [==] *)

Lemma Mplus_compat : forall {m n} (A B A' B' : Matrix m n),
    A == A' -> B == B' -> A .+ B == A' .+ B'.
Proof.
  (* WORKED IN CLASS *)
  intros m n A B A' B' HA HB.
  intros i j Hi Hj.
  unfold Mplus.
  rewrite HA by lia.
  rewrite HB by lia.
  reflexivity.
Qed.

Add Parametric Morphism m n : (@Mplus m n)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mplus_mor.
Proof.
  intros A A' HA B B' HB.
  apply Mplus_compat; easy.
Qed.

(** Now let's return to that lemma... *)

Lemma Mplus3 : forall {m n} (A B C : Matrix m n), (B .+ A) .+ C == A .+ (B .+ C).
Proof.
  (* WORKED IN CLASS *)
  intros m n A B C.
  rewrite (Mplus_comm B A).
  apply Mplus_assoc.
Qed.

(** Mscale is similarly compatible with [==], but requires a slightly
    different lemma: *)

Lemma Mscale_compat : forall {m n} (c c' : C) (A A' : Matrix m n),
    c = c' -> A == A' -> c .* A == c' .* A'.
Proof.
  intros m n c c' A A' Hc HA.
  intros i j Hi Hj.
  unfold Mscale.
  rewrite Hc, HA; easy.
Qed.

Add Parametric Morphism m n : (@Mscale m n)
  with signature eq ==> mat_equiv ==> mat_equiv as Mscale_mor.
Proof.
  intros; apply Mscale_compat; easy.
Qed.

(** Let's move on to the more interesting matrix functions: *)

Definition trace {n : nat} (A : Square n) : C :=
  Csum (fun x => A x x) n.

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
  fun x z => Csum (fun y => A x y * B y z) n.

Open Scope nat_scope.

Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) :
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => (A y x)^*.

(** We can derive the dot product and its complex analogue, the
    _inner product_, from matrix multiplication. *)

Definition dot {n : nat} (A B : Vector n) : C :=
  Mmult (transpose A) B 0 0.

Definition inner_product {n} (u v : Vector n) : C :=
  Mmult (adjoint u) (v) 0 0.

(** The _outer product_ produces a square matrix from two vectors. *)

Definition outer_product {n} (u v : Vector n) : Square n :=
  Mmult u (adjoint v).

Close Scope nat_scope.

Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope.
Notation "A †" := (adjoint A) (at level 0) : matrix_scope.
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.

(* ================================================================= *)
(** ** Compatibility lemmas *)

Lemma trace_compat : forall {n} (A A' : Square n),
    A == A' -> trace A = trace A'.
Proof.
  intros n A A' H.
  apply Csum_eq.
  intros x Hx.
  rewrite H; easy.
Qed.

Add Parametric Morphism n : (@trace n)
  with signature mat_equiv ==> eq as trace_mor.
Proof. intros; apply trace_compat; easy. Qed.

Lemma Mmult_compat : forall {m n o} (A A' : Matrix m n) (B B' : Matrix n o),
    A == A' -> B == B' -> A × B == A' × B'.
Proof.
  intros m n o A A' B B' HA HB i j Hi Hj.
  unfold Mmult.
  apply Csum_eq; intros x Hx.
  rewrite HA, HB; easy.
Qed.

Add Parametric Morphism m n o : (@Mmult m n o)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as Mmult_mor.
Proof. intros. apply Mmult_compat; easy. Qed.

Lemma kron_compat : forall {m n o p} (A A' : Matrix m n) (B B' : Matrix o p),
    A == A' -> B == B' -> A ⊗ B == A' ⊗ B'.
Proof.
  intros m n o p A A' B B' HA HB.
  intros i j Hi Hj.
  unfold kron.
  assert (Ho : o <> O). intros F. rewrite F in *. lia.
  assert (Hp : p <> O). intros F. rewrite F in *. lia.
  rewrite HA, HB. easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.mod_upper_bound; easy.
  - apply Nat.div_lt_upper_bound; lia.
  - apply Nat.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism m n o p : (@kron m n o p)
  with signature mat_equiv ==> mat_equiv ==> mat_equiv as kron_mor.
Proof. intros. apply kron_compat; easy. Qed.

Lemma transpose_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A⊤ == A'⊤.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold transpose.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@transpose m n)
  with signature mat_equiv ==> mat_equiv as transpose_mor.
Proof. intros. apply transpose_compat; easy. Qed.

Lemma adjoint_compat : forall {m n} (A A' : Matrix m n),
    A == A' -> A† == A'†.
Proof.
  intros m n A A' H.
  intros i j Hi Hj.
  unfold adjoint.
  rewrite H; easy.
Qed.

Add Parametric Morphism m n : (@adjoint m n)
  with signature mat_equiv ==> mat_equiv as adjoint_mor.
Proof. intros. apply adjoint_compat; easy. Qed.

(* ################################################################# *)
(** * Matrix Properties *)

Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o)
  (C: Matrix o p), A × B × C == A × (B × C).
Proof.
  intros m n o p A B C i j Hi Hj.
  unfold Mmult.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lca.
  + simpl.
    rewrite <- IHn.
    simpl.
    rewrite Csum_mult_l.
    rewrite <- Csum_plus.
    apply Csum_eq; intros.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† == B† × A†.
Proof.
  intros m n o A B i j Hi Hj.
  unfold Mmult, adjoint.
  rewrite Csum_conj_distr.
  apply Csum_eq; intros.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma adjoint_involutive : forall {m n} (A : Matrix m n), A†† == A.
Proof.
  (* WORKED IN CLASS *)
  intros m n A i j _ _.
  lca.
Qed.

Lemma kron_adjoint : forall {m n o p} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† == A† ⊗ B†.
Proof.
  (* WORKED IN CLASS *)
  intros m n o p A B.
  intros i j Hi Hj.
  unfold adjoint, kron.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.


(* ################################################################# *)
(** * Matrix Automation *)

(** A useful tactic for solving A == B for concrete A, B *)

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

Ltac by_cell :=
  intros i j Hi Hj;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma := by_cell; lca.

(** Let's test it! *)
Lemma scale0_concrete : 0 .* I 10 == Zero _ _.
Proof. lma. Qed.

(* ################################################################# *)
(** * Matrix Library *)

(** These equalities will prove useful in the future. *)

Lemma Mscale_0_l : forall {m n : nat} (A : Matrix m n), 0 .* A == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_0_r : forall {m n : nat} (c : C), c .* Zero m n == Zero m n.
Proof. intros. lma. Qed.

Lemma Mscale_1_l : forall {m n : nat} (A : Matrix m n), 1 .* A == A.
Proof. intros. lma. Qed.

Lemma Mscale_1_r : forall {n : nat} (c : C),
    c .* I n == fun x y => if (x =? y) then c else C0.
Proof.
  intros n c i j _ _.
  unfold I, Mscale; simpl.
  destruct (i =? j); lca.
Qed.

Lemma Mmult_0_l : forall {m n o : nat} (A : Matrix n o), Zero m n × A == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.

Lemma Mmult_0_r : forall {m n o : nat} (A : Matrix m n), A × Zero n o == Zero m o.
Proof.
  intros m n o A i j Hi Hj.
  unfold Mmult, Zero.
  rewrite Csum_0. easy.
  intros. lca.
Qed.

Lemma Mmult_1_l: forall {m n : nat} (A : Matrix m n),
  I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hi.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Hx.
  lca.
Qed.

Lemma Mmult_1_r: forall {m n : nat} (A : Matrix m n),
  A × I n == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hj.
  unfold I. rewrite Nat.eqb_refl. lca.
  intros x Hx.
  unfold I.
  apply Nat.eqb_neq in Hx. rewrite Nat.eqb_sym. rewrite Hx.
  lca.
Qed.

Lemma kron_0_l : forall {m n o p : nat} (A : Matrix o p),
  Zero m n ⊗ A == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_0_r : forall {m n o p : nat} (A : Matrix m n),
   A ⊗ Zero o p == Zero _ _.
Proof. intros. lma. Qed.

Lemma kron_1_l : forall {m n : nat} (A : Matrix m n), I 1 ⊗ A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.mod_small by lia.
  rewrite 2 Nat.div_small by lia.
  simpl; lca.
Qed.

Lemma kron_1_r : forall {m n : nat} (A : Matrix m n), A ⊗ I 1 == A.
Proof.
  intros m n A i j Hi Hj.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl; lca.
Qed.








(* Wed Dec 4 22:25:44 EST 2019 *)
