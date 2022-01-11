Load Cost.

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import ArithRing.

Undelimit Scope nat_scope.
Delimit Scope nat_scope with Nat.

Undelimit Scope Z_scope.
Delimit Scope Z_scope with Int.

Open Scope Z_scope.
Open Scope nat_scope.

Inductive list {A} : Type :=
  | Nil : list
  | Cons : A -> list -> list.

Arguments list : clear implicits.

Notation "x :: l" := (Cons x l).

Notation "[ ]" := Nil (format "[ ]").
Notation "[ x ]" := (Cons x Nil).
Notation "[ x ; y ; .. ; z ]" := (Cons x (Cons y .. (Cons z Nil) ..)).

Inductive signature : Type :=
  | Signature (arg_types : list Type) (return_type : Type).

Definition signature_to_fun_type s :=
  match s with
  | Signature arg_types return_type =>
    (fix f arg_types :=
      match arg_types with
      | [] => return_type
      | arg_type :: arg_types' => arg_type -> f arg_types'
      end
    ) arg_types
  end.

Definition signature_to_cost_fun_type s :=
  match s with
  | Signature arg_types _ =>
    (fix f arg_types :=
      match arg_types with
      | [] => nat : Type
      | arg_type :: arg_types' => arg_type -> f arg_types'
      end
    ) arg_types
  end.

Class Cost s (fun_ : signature_to_fun_type s) := {
  cost_fun: signature_to_cost_fun_type s;
}.

Definition big_o {A} f g :=
  {c : nat | forall (a : A), f a <= c * (g a)}.

Definition constant {A} f :=
  big_o f (fun (_ : A) => 1).

Definition unary_cost_constant {A} {R} {fun_} (cost : Cost (Signature [A] R) fun_) :=
  constant (@cost_fun _ _ cost).

Definition binary_cost_constant {A} {B} {R} {fun_} (cost : Cost (Signature [A; B] R) fun_) :=
  constant (fun '(a, b) => (@cost_fun _ _ cost) a b).

Definition length {A} :=
  fix length (l : list A) :=
    match l with
    | [] => 0
    | x :: l' => S (length l')
    end.

Definition length_cost {A} := ltac2:(Cost.refine_compute_cost [] 1 (eval red in (@length A)) []).

Section Example.

#[export] Instance length_Cost {A} : Cost (Signature [_] _) (@length A) := {
  cost_fun := length_cost;
}.

End Example.

Theorem length_cost_linear :
  forall {A}, big_o length_cost (fun (l : list A) => 1 + length l).
Proof.
  exists 3. intros l. induction l.
  - simpl. lia.
  - simpl. lia.
Qed.

Definition filter {A} (predicate : A -> bool) :=
  fix filter (l : list A) :=
    match l with
    | [] => []
    | x :: l' =>
      if predicate x
      then x :: (filter l')
      else filter l'
    end.

Definition filter_cost {A} predicate {predicate_Cost: Cost (Signature [_] _) predicate} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('predicate, 1), '(@cost_fun _ _ predicate_Cost))]
    1
    (eval red in (@filter A predicate))
    []
  ).

Theorem filter_cost_linear_when_predicate_cost_constant :
  forall {A} predicate {predicate_Cost: Cost _ predicate},
  unary_cost_constant predicate_Cost ->
  big_o (filter_cost predicate) (fun (l : list A) => 1 + length l).
Proof.
  intros ? ? ? ?. destruct H as (c & H). exists (c + 6). intros l. induction l.
  - simpl. lia.
  - simpl. specialize (H a). destruct (predicate a); lia.
Qed.

Section Example.

Definition tirivial_predicate := fun (_ : nat) => true.

#[export] Instance tirivial_predicate_Cost : Cost (Signature [_] _) tirivial_predicate := {
  cost_fun := ltac2:(Cost.refine_compute_cost [] 1 'tirivial_predicate []);
}.

Compute filter_cost tirivial_predicate [1; 2; 3].

Theorem tirivial_predicate_cost_constant : unary_cost_constant tirivial_predicate_Cost.
Proof.
  exists 1. intros ?. simpl. lia.
Qed.

Theorem tirivial_filter_filter :
  big_o (filter_cost tirivial_predicate) (fun l => 1 + length l).
Proof.
  apply filter_cost_linear_when_predicate_cost_constant. apply tirivial_predicate_cost_constant.
Qed.

End Example.

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Theorem list_forall_positive :
  forall {A} f g (l : list A),
  (forall a, (f a : Prop) -> (g a : Prop)) ->
  list_forall f l -> list_forall g l.
Proof.
  intros ? ? ? ? ? ?. induction l.
  - auto.
  - destruct H0 as (? & ?). split.
    + auto.
    + auto.
Qed.

Section Unused.

Fixpoint list_in {A} a (l : list A) :=
  match l with
  | [] => False
  | x :: l' => x = a \/ list_in a l'
  end.

End Unused.

Inductive is_permutation {A} : list A -> list A -> Prop :=
  | is_permutation_empty : is_permutation [] []
  | is_permutation_add a l1 l2 : is_permutation l1 l2 -> is_permutation (a :: l1) (a :: l2)
  | is_permutation_swap a b l : is_permutation (b :: a :: l) (a :: b :: l)
  | is_permutation_trans l1 l2 l3 : is_permutation l1 l2 -> is_permutation l2 l3 -> is_permutation l1 l3.

Section Example.

Theorem is_permutation_example : is_permutation [5; 3; 1; 2; 4] [1; 2; 3; 4; 5].
Proof.
  apply is_permutation_trans with [5; 1; 3; 2; 4].
  apply is_permutation_add.
  apply is_permutation_swap.
  apply is_permutation_trans with [1; 5; 3; 2; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_trans with [5; 2; 3; 4].
  apply is_permutation_add.
  apply is_permutation_swap.
  apply is_permutation_trans with [2; 5; 3; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_trans with [3; 5; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_swap.
Qed.

End Example.

Theorem is_permutation_refl : forall {A} (l : list A), is_permutation l l.
Proof.
  induction l.
  - apply is_permutation_empty.
  - apply is_permutation_add. auto.
Qed.

Theorem is_permutation_sym : forall {A} (l1 l2 : list A), is_permutation l1 l2 -> is_permutation l2 l1.
Proof.
  intros ? ? ? ?. induction H.
  - apply is_permutation_empty.
  - apply is_permutation_add. auto.
  - apply is_permutation_swap.
  - apply is_permutation_trans with l2; auto.
Qed.

Theorem permutation_length : forall {A} (l1 l2 : list A), is_permutation l1 l2 -> length l2 = length l1.
Proof.
  intros ? ? ? ?. induction H; simpl; lia.
Qed.

Theorem list_forall_permutation :
  forall {A} f (l1 l2 : list A),
  is_permutation l1 l2 ->
  list_forall f l1 -> list_forall f l2.
Proof.
  intros ? ? ? ? ?. induction H; intros ?.
  - auto.
  - destruct H0 as (? & ?). split; auto.
  - destruct H as (? & ? & ?). repeat split; auto.
  - auto.
Qed.
