(* Deadlock Freedom Proof *)

From LF Require Export FX10.

Inductive isComplete : State -> Prop :=
| doneTree (p : program) (A : array) :
    isComplete (state p A done)
.

Theorem isCompleteCheck : forall (p : program) (A : array),
  isComplete (state p A done).
Proof.
  - intros p A. apply doneTree.
Qed.

Theorem deadlock_freedom_fx10 : forall S : State,
  isComplete S \/ exists S', stepsto S S'.
Proof.
  Admitted.
(* TODO *)