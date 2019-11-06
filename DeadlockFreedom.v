(* Deadlock Freedom Proof *)

From LF Require Export FX10.
Require Import Setoid.

Inductive isComplete : State -> Prop :=
| doneTree (p : program) (A : array) :
    isComplete (state p A done)
.

Theorem isCompleteCheck : forall (p : program) (A : array),
  isComplete (state p A done).
Proof.
  - intros p A. apply doneTree.
Qed.

Theorem deadlock_freedom_fx10 : forall (p : program) (A : array) (T : tree),
  isComplete (state p A T) \/ exists A', exists T' , stepsto (state p A T) (state p A' T').
Proof.
  intros. simpl. induction T.
  - {
      simpl. left. constructor.
    }
  - {
      simpl.
      induction s.
      right. exists A. exists done. constructor.
      induction x. right.
      exists A. exists (statements s).
      try constructor.
      right. destruct e. exists (assign A index n). exists (statements s). constructor.
      exists (assign A index ((access A index0) + 1)). exists (statements s).
      constructor.
      right. exists A. exists (
                           match (access A index) with 
                           | O => (statements s)
                           | S n => (statements (join s0 (seq (while index s0) s)))
                           end). constructor.
      
      right. exists A. exists ((statements s0) || (statements s)). constructor.
      right. exists A. exists ((statements s0) :> (statements s)). constructor.
      right. exists A. exists (statements (join s0 s)). constructor.
      
    }
  - {
      simpl.
      induction T1. right. exists A. exists T2. constructor.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 :> T2). apply stepsto_2. apply H.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 :> T2). apply stepsto_2. apply H.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 :> T2). apply stepsto_2. apply H.
      
    }
  - {
      simpl. induction T1. right. exists A. exists T2. constructor.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 || T2). apply stepsto_5. apply H.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 || T2). apply stepsto_5. apply H.
      simpl. induction IHT1. inversion H. destruct H as [x]. destruct H as [x0]. right.
      exists x. exists (x0 || T2). apply stepsto_5. apply H.
      
    }
Qed.
