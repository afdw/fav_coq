Load Order.

Definition insert_sorted_impl {A} rb :=
  fix insert_sorted_impl a (l : list A) :=
    match l with
    | [] => [a]
    | x :: l' =>
      if (rb a x : bool)
      then a :: x :: l'
      else x :: (insert_sorted_impl a l')
    end.

Definition insert_sorted {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
  {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} :=
  insert_sorted_impl rb.

Theorem insert_sorted_correct :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    a (l : list A),
  sorted r l ->
  permutation (insert_sorted r a l) (a :: l) /\ sorted r (insert_sorted r a l).
Proof.
  intros ? ? ? ? ? ? ? ?. induction l.
  - simpl. split.
    + apply permutation_refl.
    + auto.
  - rename a0 into b. destruct H as (? & ?). apply IHl in H0 as ?; clear IHl. destruct H1 as (? & ?).
    simpl. destruct (DecidableBinaryRelation_spec r a b).
    + split.
      * apply permutation_refl.
      * simpl. repeat split.
        -- auto.
        -- eapply list_forall_positive.
           2: apply H.
           eauto using (TotalOrder_transitivity r).
        -- auto.
        -- auto.
    + split.
      * apply permutation_trans with (b :: a :: l).
        -- apply permutation_cons. auto.
        -- apply permutation_swap. apply permutation_refl.
      * simpl. split.
        -- apply list_forall_permutation with (a :: l).
           ++ apply permutation_sym. auto.
           ++ simpl. split.
              ** destruct (TotalOrder_totality r a b); intuition auto.
              ** auto.
        -- auto.
Qed.

Definition insert_sorted_impl_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('rb, 2), '(@cost_fun _ _ rb_Cost))]
    2
    (eval red in (@insert_sorted_impl A rb))
    []
  ).

Theorem insert_sorted_cost_linear_on_cost_constant_rb :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  big_o
    (fun '(a, l) => insert_sorted_impl_cost rb a l)
    (fun '(_, l) => 1 + length (l : list A)).
Proof.
  intros ? ? ? ? ? ? ?. destruct H as (c & H). exists (c + 19). intros (a, l). induction l.
  - simpl. lia.
  - rename a0 into b. simpl. specialize (H (a, b)). destruct (DecidableBinaryRelation_spec r a b); lia.
Qed.

Theorem insert_sorted_cost_constant_on_cost_constant_rb_and_first_place :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  constant
    (fun (p : {'(a, l) | list_forall (fun b => r a b) (l : list A)}) =>
      let 'exist _ (a, l) _ := p in
        insert_sorted_impl_cost rb a l
    ).
Proof.
  intros ? ? ? ? ? ? ?. destruct H as (c & H). exists (c + 21). intros ((a, l), H0). destruct l.
  - simpl. lia.
  - rename a0 into b. simpl. specialize (H (a, b)). destruct (DecidableBinaryRelation_spec r a b).
    + lia.
    + simpl in H0. intuition auto.
Qed.

Definition insertion_sort_impl {A} rb :=
  fix insertion_sort_impl (l : list A) :=
    match l with
    | [] => []
    | x :: l' => insert_sorted_impl rb x (insertion_sort_impl l')
    end.

Definition insertion_sort {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
  {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} :=
  insertion_sort_impl rb.

Theorem insertion_sort_correct :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb},
  is_sorter r (insertion_sort r).
Proof.
  unfold is_sorter. intros ? ? ? ? ? ?. induction l.
  - simpl. auto using permutation_nil.
  - simpl. destruct IHl as (IHl1 & IHl2).
    specialize (insert_sorted_correct _ a _ IHl2) as (? & ?).
    split.
    + apply permutation_trans with (a :: (insertion_sort r l)).
      * auto.
      * apply permutation_cons. auto.
    + auto.
Qed.

Definition insertion_sort_impl_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('(@insert_sorted_impl A rb), 2), '(@insert_sorted_impl_cost _ rb rb_Cost))]
    1
    (eval red in (@insertion_sort_impl A rb))
    ['(@insertion_sort_impl A rb)]
  ).

Theorem insertion_sort_cost_quadratic_on_cost_constant_rb :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  big_o
    (insertion_sort_impl_cost rb)
    (fun (l : list A) => 1 + (length l) * (length l)).
Proof.
  intros ? ? ? ? ? ? ?. destruct (insert_sorted_cost_linear_on_cost_constant_rb r H) as (c & H0).
  exists (c + 10). intros l. induction l.
  - simpl. lia.
  - simpl.
    specialize (H0 (a, insertion_sort_impl rb l)). simpl in H0.
    replace (length (insertion_sort_impl rb l))
      with (length l)
      in H0
      by (apply permutation_length; apply (insertion_sort_correct r)).
    lia.
Qed.

Theorem insertion_sort_cost_linear_on_cost_constant_total_order_and_sorted_list :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  big_o
    (fun (p : {l | sorted r l}) => let 'exist _ l _ := p in insertion_sort_impl_cost rb l)
    (fun p => let 'exist _ l _ := p in 1 + length (l : list A)).
Proof.
  intros ? ? ? ? ? ? ?.
  destruct (insert_sorted_cost_constant_on_cost_constant_rb_and_first_place r H) as (c & H0).
  exists (c + 10). intros (l, H1). induction l.
  - simpl. lia.
  - simpl in H1. destruct H1 as (? & ?). apply IHl in H2; clear IHl. simpl.
    apply list_forall_permutation with (l2 := insertion_sort_impl rb l) in H1.
    + specialize (H0 ltac:(exists (a, (insertion_sort_impl rb l)); auto)). simpl in H0. lia.
    + apply permutation_sym. apply (insertion_sort_correct r).
Qed.

Section Example.

Compute insertion_sort_impl_cost Nat.leb [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1].
Compute insertion_sort_impl_cost Nat.leb [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Compute insertion_sort_impl_cost Nat.leb [10; 9; 8; 7; 6; 5; 4; 3; 2; 1].
Compute insertion_sort_impl_cost Nat.leb [20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1].

Compute insertion_sort Nat.le [4; 4; 6; 1; 0; 40; 3].

End Example.
