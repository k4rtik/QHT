Require Import QHTT.Axioms.
Require Import Arith.
Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedTypeEx.
Require Import VQC.Complex.

(* Following QIO, we define quantum state as a sum over all base states and their
   corresponding complex amplitudes *)

(* location or label to refer to a qubit *)
Definition loc := nat.

(* bases are stored as a map from qubits to booleans *)
Module Import LocMap := FMapList.Make(Nat_as_OT).

(* primitive operations on bases *)
Definition initial := LocMap.empty.
Definition update m (q : loc) (b : bool) := LocMap.add q b m.
Definition lookup m (q : loc) : option bool := LocMap.find q m.

(* quantum state is a list of pairs where each pair stores a basis state
   and the amplitude associated with that basis state *)
Class State (A : Type) (B : Type) :=
  { sempty : A -> C -> B ;
    scombine : (A -> C -> B) -> (A -> C -> B) -> A -> C -> B ;
    sscale : C -> (A -> C -> B) -> A -> C -> B ;
    slookup : B -> (A -> C -> B) -> A
  }.

(* BROKEN CODE FOLLOWS *)
Instance qstate (B : Type) : State (list (C, B)) :=
  { sempty := nil;
  }.
Parameter state (A : Type) : list pair C A.

Definition val := dynamic%type.

(* state is a partial function from locations to dynamic
  (that stores both type and value, ie, abstracted type) *)
Definition state := loc -> option val.

Definition singleton (l : loc) (v : val) : state :=
  fun l' => if eq_nat_dec l l' then Some v else None.

(* qubit initialization (assuming value is a qubit)
   TODO support converting from a bool here? *)
Definition init (s : state) (l : loc) (v : val) : state :=
  fun l' => if eq_nat_dec l l' then Some v else s l'.

(* measurement, currently returns whatever representation is stored *)
Definition meas (s : state) (l : loc) : option val :=
  s l.

(* no equivalent of free needed here? *)

Infix "|-->" := singleton (at level 35, no associativity).

Definition join (s1 s2 : state) : state :=
  fun l => match s1 l with
        | None => s2 l
        | v => v
        end.

Infix "*" := join (at level 40, left associativity).

(** * Some theorems *)

Theorem join_id1 : forall s, empty * s = s.
  intros s.
  unfold join. simpl.
  ext_eq. reflexivity.
Qed.


Theorem join_id2 : forall s, s * empty = s.
  intros s.
  unfold join.
  ext_eq.
  destruct (s x).
  - reflexivity.
  - unfold empty. reflexivity.
Qed.

Hint Resolve join_id2 join_id1 : QHTT.
Hint Rewrite join_id2 join_id1 : QHTT.

Theorem meas_empty : forall l,
    (meas empty l) = None.
  intros l.
  unfold meas. unfold empty.
  reflexivity.
Qed.


