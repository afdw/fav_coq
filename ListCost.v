Load List.

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

Arguments cost_fun {s} fun_ {Cost}.

Definition big_o {A} f g :=
  {c : nat | forall (a : A), f a <= c * (g a)}.

Definition constant {A} f :=
  big_o f (fun (_ : A) => 1).

Definition unary_cost_constant {A} {R} {fun_} (cost : Cost (Signature [A] R) fun_) :=
  constant (@cost_fun _ _ cost).

Definition binary_cost_constant {A} {B} {R} {fun_} (cost : Cost (Signature [A; B] R) fun_) :=
  constant (fun '(a, b) => (@cost_fun _ _ cost) a b).

Definition app_cost := ltac2:(Cost.refine_compute_cost [] 3 '@app []).

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
