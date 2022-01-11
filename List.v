Load "Cost".

Require Import Coq.Bool.Bool.
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

Class DecidableBinaryRelation {A} (r : A -> A -> Prop) := {
  decide_binary_relation : A -> A -> bool;
  DecidableBinaryRelation_spec : forall a b, reflect (r a b) (decide_binary_relation a b);
}.

Class TotalOrder {A} (r : A -> A -> Prop) := {
  TotalOrder_DecidableBinaryRelation :> DecidableBinaryRelation r;
  TotalOrder_reflexivity : forall a, r a a;
  TotalOrder_transitivity : forall a b c, r a b -> r b c -> r a c;
  TotalOrder_antisymmetry : forall a b, r a b -> r b a -> a = b;
  TotalOrder_totality : forall a b, r a b \/ r b a;
}.

Class CostTotalOrder {A} (r : A -> A -> Prop) := {
  CostTotalOrder_TotalOrder :> TotalOrder r;
  CostTotalOrder_cost : Cost (Signature [_; _] _) decide_binary_relation;
}.

Class CostConstantTotalOrder {A} (r : A -> A -> Prop) := {
  CostConstantTotalOrder_CostTotalOrder :> CostTotalOrder r;
  CostConstantTotalOrder_cost_constant : binary_cost_constant CostTotalOrder_cost;
}.

#[export, program] Instance nat_le_DecidableBinaryRelation : DecidableBinaryRelation Nat.le := {
  decide_binary_relation := Nat.leb;
}.
Next Obligation.
  apply Nat.leb_spec0.
Qed.

#[export, program] Instance nat_le_TotalOrder : TotalOrder Nat.le.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.

#[export, program] Instance nat_leb_Cost : Cost (Signature [_; _] _) Nat.leb := {
  cost_fun := fun _ _ => 1;
}.

#[export, program] Instance nat_le_CostTotalOrder : CostTotalOrder Nat.le.

#[export, program] Instance nat_le_CostConstantTotalOrder : CostConstantTotalOrder Nat.le.
Next Obligation.
  exists 1. intros ?. simpl. destruct a. lia.
Qed.

Definition simple_sortedb {A} r {total_order : TotalOrder r} :=
  fix simple_sortedb (l : list A) :=
    match l with
    | [] => true
    | [_] => true
    | x :: ((y :: _) as l') => (@decide_binary_relation _ r _) x y && simple_sortedb l'
    end.

Definition simple_sortedb_cost {A} r {total_order : CostTotalOrder r} :=
  ltac2:(
    Cost.refine_compute_cost
    [
      (
        (
          '(
            @decide_binary_relation
            A
            r
            (@TotalOrder_DecidableBinaryRelation A r (@CostTotalOrder_TotalOrder A r total_order))
          ),
          2
        ),
        '(@cost_fun _ _ (@CostTotalOrder_cost _ _ total_order))
      )
    ]
    1
    (eval red in (@simple_sortedb A r (@CostTotalOrder_TotalOrder _ _ total_order)))
    []
  ).

Theorem simple_sortedb_cost_linear_when_cost_constant_total_order :
  forall {A} {r} (total_order : CostConstantTotalOrder r),
  big_o
    (simple_sortedb_cost r)
    (fun (l : list A) => 1 + length l).
Proof.
  intros ? ? ?. destruct total_order as (total_order & (c & H)). exists (18 + c). intros l. induction l.
  - simpl. lia.
  - simpl. destruct l.
    + lia.
    + rename a0 into b.
      replace (let (_, _, _, _, _) := @CostTotalOrder_TotalOrder A r total_order in 1) with 1.
      replace (let (CostTotalOrder_TotalOrder0, _) := total_order in 1) with 1.
      * specialize (H (a, b)) as ?. simpl in H0.
        unfold CostConstantTotalOrder_CostTotalOrder in IHl.
        destruct (@decide_binary_relation _ r _ a b); lia.
      * destruct total_order. auto.
      * destruct total_order as (total_order & ?). destruct total_order. auto.
Qed.
