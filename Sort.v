Load List.

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

Coercion TotalOrder_DecidableBinaryRelation : TotalOrder >-> DecidableBinaryRelation.

Class CostTotalOrder {A} (r : A -> A -> Prop) := {
  CostTotalOrder_TotalOrder :> TotalOrder r;
  CostTotalOrder_cost : Cost (Signature [_; _] _) decide_binary_relation;
}.

Coercion CostTotalOrder_TotalOrder : CostTotalOrder >-> TotalOrder.

Class CostConstantTotalOrder {A} (r : A -> A -> Prop) := {
  CostConstantTotalOrder_CostTotalOrder :> CostTotalOrder r;
  CostConstantTotalOrder_cost_constant : binary_cost_constant CostTotalOrder_cost;
}.

Coercion CostConstantTotalOrder_CostTotalOrder : CostConstantTotalOrder >-> CostTotalOrder.

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

Fixpoint sorted {A} r {total_order : TotalOrder r} (l : list A) :=
  match l with
  | [] => True
  | x :: l' => (list_forall (fun y => r x y) l') /\ sorted r l'
  end.

Fixpoint simple_sorted {A} r {total_order : TotalOrder r} (l : list A) :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as l') => r x y /\ simple_sorted r l'
  end.

Theorem simple_sorted_iff_sorted :
  forall {A} r {total_order : TotalOrder r} (l : list A),
  simple_sorted r l <-> sorted r l.
Proof.
  intros ? ? ? ?. induction l.
  - simpl. intuition auto.
  - simpl. destruct l.
    + simpl. intuition auto.
    + rename a0 into b.
      remember (simple_sorted r (b :: l)) as P. simpl. subst P.
      split.
      * intros (? & ?). specialize (proj1 IHl H0) as (? & ?). repeat split.
        -- auto.
        -- eapply list_forall_positive.
           2: apply H1.
           eauto using TotalOrder_transitivity.
        -- auto.
        -- auto.
      * intros ((? & ?) & ? & ?). split.
        -- auto.
        -- apply IHl. simpl. auto.
Qed.

Definition simple_sortedb {A} r {total_order : TotalOrder r} :=
  fix simple_sortedb (l : list A) :=
    match l with
    | [] => true
    | [_] => true
    | x :: ((y :: _) as l') => (@decide_binary_relation _ r _) x y && simple_sortedb l'
    end.

Theorem simple_sortedb_spec :
  forall {A} r {total_order : TotalOrder r} (l : list A),
  reflect (simple_sorted r l) (simple_sortedb r l).
Proof.
  intros ? ? ? ?. induction l.
  - simpl. apply ReflectT. auto.
  - simpl. destruct l.
    + apply ReflectT. auto.
    + rename a0 into b.
      destruct (@DecidableBinaryRelation_spec _ r _ a b); destruct IHl; constructor; intuition auto.
Qed.

Definition simple_sortedb_cost {A} r {total_order : CostTotalOrder r} :=
  ltac2:(
    Cost.refine_compute_cost
    [
      (
        ('(@decide_binary_relation _ _ total_order), 2),
        '(@cost_fun _ _ (@CostTotalOrder_cost _ _ total_order))
      )
    ]
    1
    (eval red in (@simple_sortedb A r total_order))
    []
  ).

Theorem simple_sortedb_cost_linear_on_cost_constant_total_order :
  forall {A} r {total_order : CostConstantTotalOrder r},
  big_o
    (simple_sortedb_cost r)
    (fun (l : list A) => 1 + length l).
Proof.
  intros ? ? ?. destruct total_order as (total_order & (c & H)). exists (c + 18). intros l. induction l.
  - simpl. lia.
  - simpl. destruct l.
    + lia.
    + rename a0 into b. unfold CostConstantTotalOrder_CostTotalOrder in IHl.
      specialize (H (a, b)). simpl in H. lia.
Qed.

Definition is_sorter {A} r {total_order : TotalOrder r} f :=
  forall (l : list A), is_permutation (f l) l /\ sorted r (f l).

Definition insert_sorted {A} r {total_order : TotalOrder r} :=
  fix insert_sorted a (l : list A) :=
    match l with
    | [] => [a]
    | x :: l' =>
      if (@decide_binary_relation _ r _) a x
      then a :: x :: l'
      else x :: (insert_sorted a l')
    end.

Theorem insert_sorted_correct :
  forall {A} r {total_order : TotalOrder r} a (l : list A),
  sorted r l ->
  is_permutation (insert_sorted r a l) (a :: l) /\ sorted r (insert_sorted r a l).
Proof.
  intros ? ? ? ? ? ?. induction l.
  - simpl. split.
    + apply is_permutation_add. apply is_permutation_empty.
    + auto.
  - rename a0 into b. destruct H as (? & ?). apply IHl in H0 as ?. destruct H1 as (? & ?).
    simpl. destruct (@DecidableBinaryRelation_spec _ r _ a b).
    + split.
      * apply is_permutation_refl.
      * simpl. repeat split.
        -- auto.
        -- eapply list_forall_positive.
           2: apply H.
           eauto using TotalOrder_transitivity.
        -- auto.
        -- auto.
    + split.
      * apply is_permutation_trans with (b :: a :: l).
        -- apply is_permutation_add. auto.
        -- apply is_permutation_swap.
      * simpl. split.
        -- apply list_forall_permutation with (a :: l).
           ++ apply is_permutation_sym. auto.
           ++ simpl. split.
              ** destruct (@TotalOrder_totality _ r _ a b); intuition auto.
              ** auto.
        -- auto.
Qed.

Definition insert_sorted_cost {A} r {total_order : CostTotalOrder r} :=
  ltac2:(
    Cost.refine_compute_cost
    [
      (
        ('(@decide_binary_relation _ _ total_order), 2),
        '(@cost_fun _ _ (@CostTotalOrder_cost _ _ total_order))
      )
    ]
    2
    (eval red in (@insert_sorted A r total_order))
    []
  ).

Theorem insert_sorted_cost_linear_on_cost_constant_total_order :
  forall {A} r {total_order : CostConstantTotalOrder r},
  big_o
    (fun '(a, l) => insert_sorted_cost r a l)
    (fun '(_, l) => 1 + length (l : list A)).
Proof.
  intros ? ? ?. destruct total_order as (total_order & (c & H)). exists (c + 19). intros (a, l). induction l.
  - simpl. lia.
  - rename a0 into b. unfold CostConstantTotalOrder_CostTotalOrder in IHl. simpl. specialize (H (a, b)).
    destruct (@DecidableBinaryRelation_spec _ r _ a b); lia.
Qed.

Definition insertion_sort {A} r {total_order : TotalOrder r} :=
  fix insertion_sort (l : list A) :=
    match l with
    | [] => []
    | x :: l' => insert_sorted r x (insertion_sort l')
    end.

Theorem insertion_sort_correct :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}, is_sorter r (insertion_sort r).
Proof.
  unfold is_sorter. intros ? ? ? ?. induction l.
  - simpl. auto using is_permutation_empty.
  - simpl. destruct IHl as (IHl1 & IHl2).
    specialize (insert_sorted_correct r a (insertion_sort r l) IHl2) as (? & ?).
    split.
    + apply is_permutation_trans with (a :: (insertion_sort r l)).
      * auto.
      * apply is_permutation_add. auto.
    + auto.
Qed.

Definition insertion_sort_cost {A} r {total_order : CostTotalOrder r} :=
  ltac2:(
    Cost.refine_compute_cost
    [
      (
        ('(@insert_sorted A r total_order), 2),
        '(@insert_sorted_cost A r total_order)
      )
    ]
    1
    (eval red in (@insertion_sort A r total_order))
    ['(@insertion_sort A r total_order)]
  ).

Theorem insertion_sort_cost_quadratic_on_cost_constant_total_order :
  forall {A} r {total_order : CostConstantTotalOrder r},
  big_o
    (insertion_sort_cost r)
    (fun (l : list A) => 1 + (length l) * (length l)).
Proof.
  intros ? ? ?. destruct (insert_sorted_cost_linear_on_cost_constant_total_order r) as (c & H).
  exists (c + 10). intros l. induction l.
  - simpl. lia.
  - simpl.
    specialize (H (a, insertion_sort r l)). simpl in H.
    replace (length (insertion_sort r l))
      with (length l)
      in H
      by (apply permutation_length; apply insertion_sort_correct).
    lia.
Qed.

Section Example.

Compute insertion_sort_cost _ [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1].
Compute insertion_sort_cost _ [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Compute insertion_sort_cost _ [10; 9; 8; 7; 6; 5; 4; 3; 2; 1].
Compute insertion_sort_cost _ [20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1].

End Example.
