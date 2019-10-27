Definition array : Type := list nat.
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

Fixpoint assign (A : array) (index : nat) (value : nat) : array := 
  match index with
  | O => match A with
    | nil => nil
    | h :: t => value :: t
  end
  | S index' => match A with
    | nil => nil
    | h :: t => h :: assign t index' value
  end
end.

Example test_assign0:  (assign [1; 1; 1] 0 2) = [2; 1; 1].
Proof. simpl. reflexivity.  Qed.
Example test_assign1:  (assign [1; 1; 1] 1 2) = [1; 2; 1].
Proof. simpl. reflexivity.  Qed.
Example test_assign2:  (assign [1; 1; 1] 2 2) = [1; 1; 2].
Proof. simpl. reflexivity.  Qed.
Example test_assign3:  (assign [1; 1; 1] 3 2) = [1; 1; 1].
Proof. simpl. reflexivity.  Qed.
Example test_assign4:  (assign [1; 1; 1] 4 2) = [1; 1; 1].
Proof. simpl. reflexivity.  Qed.

Fixpoint array_init (size : nat) : array :=
  match size with
  | O => nil
  | S n => O :: array_init n
  end
.

Example test_array_init0:  array_init O = [].
Proof. simpl. reflexivity.  Qed.
Example test_array_init1:  array_init 1 = [0].
Proof. simpl. reflexivity.  Qed.
Example test_array_init2:  array_init 2 = [0; 0].
Proof. simpl. reflexivity.  Qed.
