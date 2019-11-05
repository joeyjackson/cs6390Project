(** Featherweight X10 Implementation *)

From LF Require Export Array.
From LF Require Export Syntax.

Inductive tree : Type :=
| done : tree
| statements (s : statement) : tree
| arrow (T1 : tree) (T2 : tree) : tree
| pipes (T1 : tree) (T2 : tree) : tree
.

Notation "x || y" := (pipes x y).
Notation "x :> y" := (arrow x y) (at level 62).

Inductive State := | state (p : program) (A : array) (T : tree).

Inductive stepsto : State -> State -> Prop :=
| stepsto_1 (p : program) (A : array) (T : tree):
    stepsto
      (state p A (done :> T))
      (state p A T)
| stepsto_2 (p : program) (A : array) (T : tree) (A' : array) (T' : tree) (T2 : tree):
    stepsto
      (state p A T)
      (state p A' T')
    ->
    stepsto
      (state p A (T :> T2))
      (state p A' (T' :> T2))
| stepsto_3 (p : program) (A : array) (T : tree):
    stepsto
      (state p A (done || T))
      (state p A T)
| stepsto_4 (p : program) (A : array) (T : tree):
    stepsto
      (state p A (T || done))
      (state p A T)
| stepsto_5 (p : program) (A : array) (T : tree) (A' : array) (T' : tree) (T2 : tree):
    stepsto
      (state p A T)
      (state p A' T')
    ->
    stepsto
      (state p A (T || T2))
      (state p A' (T' || T2))
| stepsto_6 (p : program) (A : array) (T : tree) (A' : array) (T' : tree) (T2 : tree):
    stepsto
      (state p A T)
      (state p A' T')
    ->
    stepsto
      (state p A (T2 || T))
      (state p A' (T2 || T'))
| stepsto_7 (p : program) (A : array):
    stepsto
      (state p A (statements skip))
      (state p A done)
| stepsto_8 (p : program) (A : array) (k : statement):
    stepsto
      (state p A (statements (seq skp k)))
      (state p A (statements k))
| stepsto_9 (p : program) (A : array) (k : statement) (d : nat) (e : expr):
    stepsto
      (state p A (statements (seq (assignment d e) k)))
      (
        match e with
        | const n => (state p (assign A d n) (statements k))
        | incr i => (state p (assign A d ((access A i) + 1)) (statements k))
        end
      )
| stepsto_10_11 (p : program) (A : array) (k : statement) (d : nat) (s : statement):
    stepsto
      (state p A (statements (seq (while d s) k)))
      (
        match (access A d) with
        | O => (state p A (statements k))
        | S n => (state p A (statements (join s (seq (while d s) k))))
        end
      )
| stepsto_12 (p : program) (A : array) (k : statement) (s : statement):
    stepsto
      (state p A (statements (seq (async s) k)))
      (state p A ((statements s) || (statements k)))
| stepsto_13 (p : program) (A : array) (k : statement) (s : statement):
    stepsto
      (state p A (statements (seq (finish s) k)))
      (state p A ((statements s) :> (statements k)))
| stepsto_14 (p : program) (A : array) (k : statement) (s : statement):
    stepsto
      (state p A (statements (seq (call s) k)))
      (state p A (statements (join s k)))
.

Example test_stepsto1:
  stepsto
    (state (p {}) (array_init 0) (done :> (statements {skp})))
    (state (p {}) (array_init 0) (statements {skp})).
Proof. apply stepsto_1. Qed.

(* TODO Example test_stepsto2: *)
Example test_stepsto2:
    stepsto
      (state (p {}) (array_init 0) (done :> (statements {skp})))
      (state (p {}) (array_init 1) (statements {skp}))  ->
    stepsto
      (state (p {}) (array_init 0) ((done :> (statements {skp})):> (statements {assignment 0 (const 1)})))
      (state (p {}) (array_init 1) ((statements {skp}) :> (statements {assignment 0 (const 1)}))).
Proof. apply stepsto_2. Qed.

Example test_stepsto3:
  stepsto
    (state (p {}) (array_init 0) (done || (statements {skp})))
    (state (p {}) (array_init 0) (statements {skp})).
Proof. apply stepsto_3. Qed.

Example test_stepsto4:
  stepsto
    (state (p {}) (array_init 0) ((statements {skp}) || done))
    (state (p {}) (array_init 0) (statements {skp})).
Proof. apply stepsto_4. Qed.


Example test_stepsto5:
    stepsto
      (state (p {}) (array_init 0) (done :> (statements {skp})))
      (state (p {}) (array_init 0) (done :> (statements {skp})))
    ->
    stepsto
      (state (p {}) (array_init 0) ((done :> (statements {skp})) || (statements {assignment 0 (const 1)})))
      (state (p {}) (array_init 0) ((done :> (statements {skp})) || (statements {assignment 0 (const 1)}))).
Proof. apply stepsto_5. Qed.

Definition a0 := state (p {}) (array_init 0).
Example test_stepsto6:
    stepsto
      (state (p {}) (array_init 0) (done :> (statements {skp})))
      (state (p {}) (array_init 0) (done :> (statements {skp})))
    ->
    stepsto
      (state (p {}) (array_init 0) ((statements {assignment 0 (const 1)}) || (done :> (statements {skp}))))
      (state (p {}) (array_init 0) ((statements {assignment 0 (const 1)}) || (done :> (statements {skp})))).
Proof. apply stepsto_6. Qed.

Example test_stepsto7:
  stepsto
    (state (p {}) (array_init 0) (statements skip))
    (state (p {}) (array_init 0) (done)).
Proof. apply stepsto_7. Qed.

Example test_stepsto8:
  stepsto
    (state (p {}) (array_init 0) (statements (seq skp (seq (assignment 0 (const 1)) skip) ) ) )
    (state (p {}) (array_init 0) (statements (seq (assignment 0 (const 1)) skip) ) ).
Proof. apply stepsto_8. Qed.

Example test_stepsto9:
  stepsto
    (state (p {}) (array_init 1) (statements (seq (assignment 0 (const 1)) skip)))
    (state (p {}) ([1]) (statements skip)).
Proof. apply stepsto_9. Qed.

(* TODO Example test_stepsto10: *)
(* TODO Example test_stepsto11: *)
Example test_stepsto10_11:
    stepsto
      (a0 (statements (seq (while 0 skip) skip)))
      (
        match (access (array_init 0) 0) with
        | O => (state (p {}) (array_init 0) (statements skip))
        | S n => (state (p {}) (array_init 0) (statements (join skip (seq (while 0 skip) skip))))
        end
      ).
Proof. apply stepsto_10_11. Qed.


Example test_stepsto12:
  stepsto
    (state (p {}) (array_init 0) (statements (seq (async skip) skip)))
    (state (p {}) (array_init 0) ((statements skip) || (statements skip))).
Proof. apply stepsto_12. Qed.

Example test_stepsto13:
  stepsto
    (state (p {}) (array_init 0) (statements (seq (finish skip) skip)))
    (state (p {}) (array_init 0) ((statements skip) :> (statements skip))).
Proof. apply stepsto_13. Qed.

Example test_stepsto14:
  stepsto
    (a0 (statements (seq (call skip) skip)))
    (a0 (statements (join skip skip))).
Proof. apply stepsto_14. Qed.


