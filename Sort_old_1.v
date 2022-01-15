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

Inductive locally_sorted {A} r {total_order : @TotalOrder A r} : list A -> Prop :=
  | locally_sorted_empty : locally_sorted r []
  | locally_sorted_single a : locally_sorted r [a]
  | locally_sorted_next a b l : r a b -> locally_sorted r (b :: l) -> locally_sorted r (a :: b :: l).

Theorem locally_sorted_iff_sorted :
   forall {A} r {total_order : TotalOrder r} (l : list A),
   locally_sorted r l <-> sorted r l.
 Proof.
  intros ? ? ? ?. split.
  - intros ?. induction H.
    + simpl. auto.
    + simpl. auto.
    + simpl. simpl in IHlocally_sorted. destruct IHlocally_sorted as (? & ?). repeat split.
      * auto.
      * eapply list_forall_positive.
        2: apply H1.
        eauto using TotalOrder_transitivity.
      * auto.
      * auto.
  - intros ?. induction l.
    + apply locally_sorted_empty.
    + simpl in H. destruct H as (? & ?). specialize (IHl H0). destruct l.
      * apply locally_sorted_single.
      * simpl in H. apply locally_sorted_next; intuition auto.
Qed.

Definition locally_sortedb {A} r {total_order : TotalOrder r} :=
  fix locally_sortedb (l : list A) :=
    match l with
    | [] => true
    | [_] => true
    | x :: ((y :: _) as l') => (@decide_binary_relation _ r _) x y && locally_sortedb l'
    end.

Theorem locally_sortedb_spec :
  forall {A} r {total_order : TotalOrder r} (l : list A),
  reflect (locally_sorted r l) (locally_sortedb r l).
Proof.
  intros ? ? ? ?. induction l.
  - simpl. apply ReflectT. apply locally_sorted_empty.
  - simpl. destruct l.
    + apply ReflectT. apply locally_sorted_single.
    + rename a0 into b. destruct (@DecidableBinaryRelation_spec _ r _ a b), IHl.
      * apply ReflectT. apply locally_sorted_next; auto.
      * apply ReflectF. intros ?. inversion H. auto.
      * apply ReflectF. intros ?. inversion H. auto.
      * apply ReflectF. intros ?. inversion H. auto.
Qed.

(*Definition simple_sortedb_cost {A} r {total_order : CostTotalOrder r} :=
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
Qed.*)

Definition is_sorter {A} r {total_order : TotalOrder r} f :=
  forall (l : list A), is_permutation (f l) l /\ sorted r (f l).

Theorem sorted_equal :
  forall {A} r {total_order : TotalOrder r} (l1 l2 : list A),
  sorted r l1 ->
  sorted r l2 ->
  is_permutation l1 l2 ->
  l1 = l2.
Proof.
  intros ? ? ? ? ? ? ? ?. rewrite <- locally_sorted_iff_sorted in H, H0.
  generalize dependent l1. induction H0; intros l1 ? ?.
  - inversion H; clear H; subst l1.
    + auto.
    + apply permutation_empty_inversion in H1. discriminate H1.
    + apply permutation_empty_inversion in H1. discriminate H1.
  - inversion H; clear H; subst l1.
    + apply is_permutation_sym in H1. apply permutation_empty_inversion in H1. discriminate.
    + apply permutation_single_inversion' in H1. subst a0. auto.
    + apply permutation_single_inversion in H1. discriminate.
  - inversion H1; clear H1; subst l1.
    + apply is_permutation_sym in H2. apply permutation_empty_inversion in H2. discriminate.
    + apply is_permutation_sym in H2. apply permutation_single_inversion in H2. discriminate.
    + specialize (IHlocally_sorted (b0 :: l0) H4).

  setoid_rewrite -> (locally_sorted_iff_sorted r).
  intros ? ? ? l1 l2 ? ? ?. generalize dependent l1. induction H0; intros l1 ? ?.
  - inversion H; clear H; subst l1.
    + auto.
    + apply permutation_empty_inversion in H1. discriminate H1.
    + apply permutation_empty_inversion in H1. discriminate H1.
  - inversion H; clear H; subst l1.
    + apply is_permutation_sym in H1. apply permutation_empty_inversion in H1. discriminate.
    + apply permutation_single_inversion' in H1. subst a0. auto.
    + apply permutation_single_inversion in H1. discriminate.
  - inversion H1; clear H1; subst l1.
    + apply is_permutation_sym in H2. apply permutation_empty_inversion in H2. discriminate.
    + apply is_permutation_sym in H2. apply permutation_single_inversion in H2. discriminate.
    + specialize (IHsorted (b0 :: l0) H4).


  - subst l1. apply is_permutation_alt_is_permutation in H1. inversion H1.
  - subst l1. apply is_permutation_alt_is_permutation in H1. inversion H1. destruct l1; discriminate.
  - subst l1.
apply app_permutation_inversion with (l3 := []) (l4 := []) in H1. admit. apply permutation_same_head in H1.
  intros ? ? ? l1 l2 ? ? ?. induction H; inversion H0.
  - auto.
  - subst l2. inversion H1. subst.

Lemma sorted_equal_cons :
  forall {A} r {total_order : TotalOrder r} a b (l1 l2 : list A),
  sorted r (a :: l1) ->
  sorted r (b :: l2) ->
  is_permutation (a :: l1) (b :: l2) ->
  a = b /\ is_permutation l1 l2.
Proof.
  intros ? ? ? a b l1 l2 ? ? ?.
  destruct H as (? & ?), H0 as (? & ?). clear H2 H3.
  assert (r a b). {
    apply is_permutation_alt_is_permutation in H1.
    inversion H1. subst a0 l4. destruct l0.
    - simpl in H2. injection H2 as -> ->. apply TotalOrder_reflexivity.
    - injection H2 as -> <-. apply list_forall_app in H. simpl in H. intuition auto.
  }
  assert (r b a). {
    apply is_permutation_sym in H1. apply is_permutation_alt_is_permutation in H1.
    inversion H1. subst a0 l4. destruct l0.
    - simpl in H3. injection H3 as -> ->. apply TotalOrder_reflexivity.
    - injection H3 as -> <-. apply list_forall_app in H0. simpl in H0. intuition auto.
  }
  assert (a = b) by (apply (@TotalOrder_antisymmetry _ r _); auto).
  split.
  - apply H4.
  - subst b. apply permutation_same_head with a. auto.
Qed.

Theorem sorted_equal :
  forall {A} r {total_order : TotalOrder r} (l1 l2 : list A),
  sorted r l1 ->
  sorted r l2 ->
  is_permutation l1 l2 ->
  l1 = l2.
Proof.
  intros ? ? ? l1 l2 ? ? ?. generalize dependent l2. induction l1; intros l2 ? ?.
  - symmetry. apply permutation_empty. apply is_permutation_sym. auto.
  - destruct l2.
    + apply permutation_empty. auto.
    + rename a0 into b. specialize (sorted_equal_cons _ _ _ _ _ H H0 H1) as (? & ?). f_equal.
      * auto.
      * destruct H as (? & ?), H0 as (? & ?). apply IHl1; auto.
Qed.

Theorem sorter_fully_defined :
  forall {A} r {total_order : TotalOrder r} f1 f2,
  is_sorter r f1 ->
  is_sorter r f2 ->
  forall (l : list A), f1 l = f2 l.
Proof.
  unfold is_sorter. intros ? ? ? ? ? ? ? ?.
  specialize (H l). specialize (H0 l). destruct H as (? & ?), H0 as (? & ?).
  apply (sorted_equal r).
  - auto.
  - auto.
  - apply is_permutation_trans with l.
    + auto.
    + apply is_permutation_sym. auto.
Qed.

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

Theorem insert_sorted_cost_constant_on_cost_constant_total_order_and_first_place :
  forall {A} r {total_order : CostConstantTotalOrder r},
  constant
    (fun (p : {'(a, l) | list_forall (fun b => r a b) (l : list A)}) =>
      let 'exist _ (a, l) _ := p in
        insert_sorted_cost r a l
    ).
Proof.
  intros ? ? ?. destruct total_order as (total_order & (c & H0)). exists (c + 21). intros ((a, l), H). destruct l.
  - simpl. lia.
  - rename a0 into b. simpl. specialize (H0 (a, b)). destruct (@DecidableBinaryRelation_spec _ r _ a b).
    + lia.
    + simpl in H. intuition auto.
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

Theorem insertion_sort_cost_linear_on_cost_constant_total_order_and_list :
  forall {A} r {total_order : CostConstantTotalOrder r},
  big_o
    (fun (p : {l | sorted r l}) => let 'exist _ l _ := p in insertion_sort_cost r l)
    (fun p => let 'exist _ l _ := p in 1 + length (l : list A)).
Proof.
  intros ? ? ?. destruct (insert_sorted_cost_constant_on_cost_constant_total_order_and_first_place r) as (c & H).
  exists (c + 10). intros (l, H0). induction l.
  - simpl. lia.
  - simpl in H0. destruct H0 as (? & ?). apply IHl in H1. clear IHl. simpl.
    apply list_forall_permutation with (l2 := insertion_sort r l) in H0.
    + specialize (H ltac:(exists (a, (insertion_sort r l)); auto)). simpl in H. lia.
    + apply is_permutation_sym. apply insertion_sort_correct.
Qed.

Section Example.

Compute insertion_sort_cost _ [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1].
Compute insertion_sort_cost _ [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Compute insertion_sort_cost _ [10; 9; 8; 7; 6; 5; 4; 3; 2; 1].
Compute insertion_sort_cost _ [20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1].

End Example.
