Load "Cost".

Require Import Coq.ZArith.ZArith.
Require Import Lia.

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

Definition unary_cost_constant {A} {B} {fun_} (cost : Cost (Signature [A] B) fun_) :=
  constant (@cost_fun _ _ cost).

Definition length {A} :=
  fix length (l : list A) :=
    match l with
    | [] => 0
    | x :: l' => S (length l')
    end.

Definition length_cost {A} := ltac2:(Cost.refine_compute_cost [] 1 (eval red in (@length A)) []).

#[export] Instance length_Cost {A} : Cost (Signature [_] _) (@length A) := {
  cost_fun := length_cost;
}.

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
  intros ? ? ? ?. destruct H as (c & H). exists (6 + c). intros l. induction l.
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
