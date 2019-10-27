
From LF Require Export Array.

Inductive expr : Type := 
| const (n : nat) : expr
| incr (A : array) (index : nat) : expr
.

Inductive sequence (X : Type) : Type :=
| skip
| seq (x : X) (l : sequence X)
.
Arguments skip {X}.
Arguments seq {X} _ _.

Inductive instr : Type :=
| skp : instr  (* Handled in statement so unnecessary *)
| assignment (A : array) (index : nat) (e : expr) : instr
| while (A : array) (index : nat) (s : sequence instr) : instr
| async (s : sequence instr) : instr
| finish (s : sequence instr) : instr
| call (s : sequence instr) : instr
.

(* 
Notation "a [ d ] = e" := (assignment a d e) (at level 64).
Notation "while ( a [ d ] ! 0 ) s" := (while a d s) (at level 64).
*)

Definition statement : Type := sequence instr.
Notation "x >> l" := (seq x l)
                     (at level 61, right associativity).
Notation "{ }" := skip.
Notation "{ x ; .. ; y }" := (seq x .. (seq y skip) ..).

Fixpoint join (s1 : statement) (s2 : statement) : statement :=
match s1 with 
| skip => s2
| seq i s => i >> (join s s2)
end.

Example test_join:  join {skp; skp; call {skp}} {skp; skp} = {skp; skp; call {skp}; skp; skp}.
Proof. simpl. reflexivity. Qed.

Inductive program : Type := 
| p (s : statement) : program
.

Check p ({ }).
Check p ({skp}).
Check p ({skp; skp}).
Check p ({skp; skp; async {skp}}).
Check p ({skp; skp; finish {async {skp}}}).
Check p ({finish {async {skp}}; while [1] 0 {assignment [5] 0 (const 1)}}).
Check p ({call {skp; call {skp; assignment [3; 5] 1 (incr [2] 0)}; skp; call {skp}}}).
