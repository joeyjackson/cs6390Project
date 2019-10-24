(** Featherweight X10 Implementation *)

Definition array := list nat.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint access (A : array) (index : nat) : nat :=
  match index with
  | O => match A with
    | nil => O
    | h :: t => h
  end
  | S index' => match A with
    | nil => O
    | h :: t => access t index'
  end
end.

Example test_access0:  (access [1; 2; 3] 0) = 1.
Proof. simpl. reflexivity.  Qed.
Example test_access1:  (access [1; 2; 3] 1) = 2.
Proof. simpl. reflexivity.  Qed.
Example test_access2:  (access [1; 2; 3] 2) = 3.
Proof. simpl. reflexivity.  Qed.
Example test_access3:  (access [1; 2; 3] 3) = 0.
Proof. simpl. reflexivity.  Qed.

Fixpoint insert (A : array) (index : nat) (value : nat) : array := 
  match index with
  | O => match A with
    | nil => value :: nil
    | h :: t => value :: t
  end
  | S index' => match A with
    | nil => value :: nil
    | h :: t => h :: insert t index' value
  end
end.

Example test_insert0:  (insert [1; 1; 1] 0 2) = [2; 1; 1].
Proof. simpl. reflexivity.  Qed.
Example test_insert1:  (insert [1; 1; 1] 1 2) = [1; 2; 1].
Proof. simpl. reflexivity.  Qed.
Example test_insert2:  (insert [1; 1; 1] 2 2) = [1; 1; 2].
Proof. simpl. reflexivity.  Qed.
Example test_insert3:  (insert [1; 1; 1] 3 2) = [1; 1; 1; 2].
Proof. simpl. reflexivity.  Qed.



Inductive statement : Type :=
| skip : statement
| seq (i : instr) (s : statement) : statement
.

Definition instr : Type :=
| skip : instr
(* a[d] = e *)
(* while (a[d] != 0) s *)
| async (s : statement) : instr
| finish (s : statement) : instr
| call
.

Definition expr : Type := 
| nat : expr
(* a[d] + 1 *)
.



