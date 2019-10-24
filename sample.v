Definition var := nat.

Inductive typ : Type :=
| unit : typ
| arr (A : typ) (B : typ) : typ
.

Inductive expr : Type :=
| u : expr
| evar (x : var) : expr
| lam (x : var) (A : typ) (e : expr) : expr
| app (e1 : expr) (e2 : expr) : expr
.

Fixpoint eq (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eq n' m'
  | _, _ => false
  end
.

Fixpoint substitute (e : expr) (s : expr) (x : var) : expr := 
  match e with
  | u => u
  | evar y =>
    if eq x y then s else e
  | lam y A e' =>
    if eq x y then e else lam y A (substitute e' s x)
  | app e1 e2 => app (substitute e1 s x) (substitute e2 s x)
  end
.

Inductive stepsto : expr -> expr -> Prop :=
| step_beta x A e1 e2 : stepsto (app (lam x A e1) e2) (substitute e1 e2 x)
| step_left e1 e2 e1' :
    stepsto e1 e1' -> stepsto (app e1 e2) (app e1' e2)
| step_right e1 e2 e2' :
    stepsto e2 e2' -> stepsto (app e1 e2) (app e1 e2')
| step_body x A e e' : stepsto e e' -> stepsto (lam x A e) (lam x A e')
.

Inductive ctx : Type :=
| nil : ctx
| cons (x : var) (t : typ) (G : ctx) : ctx
.

Inductive contains : ctx -> var -> typ -> Prop :=
| contains_hd x t G : contains (cons x t G) x t
| contains_tl x t y t' G : contains G x t -> contains (cons y t' G) x t
.

Inductive has_type : ctx -> expr -> typ -> Prop :=
| type_unit G : has_type G u unit
| type_var G x A : contains G x A -> has_type G (evar x) A
| type_lam G x A B e : has_type (cons x A G) e B ->
                       has_type G (lam x A e) (arr A B)
| type_app G e1 e2 A B : has_type G e1 (arr A B) ->
                         has_type G e2 A ->
                         has_type G (app e1 e2) B
.

Inductive value : expr -> Prop :=
| value_u : value u
| value_lam x A e : value (lam x A e)
.

Theorem progress e A : has_type nil e A ->
                       value e \/ exists e', stepsto e e'.
Proof.
  intros H.
  remember nil as G. (* This is a workaround for a bug. 
                        It adds a variable G := nil, and then replaces nil with G. *)
  (* We can induct over an inductively defined proposition, just like an inductively
     defined type. We are inducting over the proof that e has a type, which is typically
     how a progress theorem is proven. *)
  induction H as [ G                            (* <- These are the parameters of all 4 *)
                 | G x A H1                     (* <- has_type constructors, including  *)
                 | G x A B e H1 IH1             (* <- the premises. We also get some    *)
                 | G e1 e2 A B H1 IH1 H2 IH2 ]. (* <- inductive hypotheses.             *)
  - (* e is u : unit *)
    (* e is a value. *)
    left.
    apply value_u.
  - (* e is evar x : A, given x:A is in G *)
    (* e is neither a value, nor can step. But G is supposedly empty! *)
    subst.
    inversion H1. (* triggers the contradiction since nil cannot contain x:A. *)
  - (* e is lam x A e : arr A B*)
    (* e is a value. *)
    left.
    apply value_lam.
  - (* e is app e1 e2 : B, given e1 : arr A B and e2 : B *)
    (* We will definitely be able to step: either can step e1 => e1' in place,
       or else e1 is a value (specifically a lambda), so we can beta reduce. *)
    right.
    specialize (IH1 HeqG). (* simplify IH1 *)
    (** We stopped here in class. **)
    (* Two cases: Is e1 a value or can it step? *)
    destruct IH1 as [H_val | H_step].
    + (* e1 is a value. *)
      (* Two cases: Is e1 a unit or a lambda? *)
      inversion H_val as [H_u | x C e3 H_lam].
      * (* e1 is u *)
        (* But e1 supposedly has type arr A B! *)
        subst.
        inversion H1.
      * (* e1 is lam x C e3 *)
        subst.
        (* Prove there exists an e' such that ... by furnishing e' *)
        exists (substitute e3 e2 x).
        apply step_beta.
    + (* e1 can step. *)
      (* What does it step to? *)
      inversion H_step as [e1' H_stepsto].
      (* e1 steps to e1' *)
      (* Prove there exists an e' such that ... by furnishing e' *)
      exists (app e1' e2).
      apply step_left.
      apply H_stepsto.
Qed.

(* Notice we didn't ever use step_right or step_body to find the steps
   we needed. This is because we used the weak head normal form to
   define values (u and any lam x A e), and because we did not impose
   call-by-value. *)
