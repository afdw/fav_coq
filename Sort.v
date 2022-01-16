Load List.

Class DecidableBinaryRelation {A} (r : A -> A -> Prop) (rb : A -> A -> bool) := {
  DecidableBinaryRelation_spec : forall a b, reflect (r a b) (rb a b);
}.

Arguments DecidableBinaryRelation_spec {A}%type_scope r%function_scope {rb}%function_scope
  {DecidableBinaryRelation} _.

Class TotalOrder {A} (r : A -> A -> Prop) := {
  TotalOrder_reflexivity : forall a, r a a;
  TotalOrder_transitivity : forall a b c, r a b -> r b c -> r a c;
  TotalOrder_antisymmetry : forall a b, r a b -> r b a -> a = b;
  TotalOrder_totality : forall a b, r a b \/ r b a;
}.

Arguments TotalOrder_reflexivity {A}%type_scope r%function_scope {TotalOrder} _.
Arguments TotalOrder_transitivity {A}%type_scope r%function_scope {TotalOrder} _ _ _ _ _.
Arguments TotalOrder_antisymmetry {A}%type_scope r%function_scope {TotalOrder} _ _ _ _.
Arguments TotalOrder_totality {A}%type_scope r%function_scope {TotalOrder} _ _.

#[export, program] Instance nat_le_DecidableBinaryRelation : DecidableBinaryRelation Nat.le Nat.leb.
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

Fixpoint sorted {A} r {total_order : TotalOrder r} (l : list A) :=
  match l with
  | [] => True
  | x :: l' => (list_forall (fun y => r x y) l') /\ sorted r l'
  end.

Fixpoint locally_sorted {A} r {total_order : TotalOrder r} (l : list A) :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as l') => r x y /\ locally_sorted r l'
  end.

Theorem locally_sorted_iff_sorted :
  forall {A} r {total_order : TotalOrder r} (l : list A),
  locally_sorted r l <-> sorted r l.
Proof.
  intros ? ? ? ?. induction l.
  - simpl. intuition auto.
  - simpl. destruct l.
    + simpl. intuition auto.
    + rename a0 into b.
      remember (locally_sorted r (b :: l)) as P. simpl. subst P.
      split.
      * intros (? & ?). specialize (proj1 IHl H0) as (? & ?). repeat split.
        -- auto.
        -- eapply list_forall_positive.
           2: apply H1.
           eauto using (TotalOrder_transitivity r).
        -- auto.
        -- auto.
      * intros ((? & ?) & ? & ?). split.
        -- auto.
        -- apply IHl. simpl. auto.
Qed.

Definition locally_sortedb_impl {A} rb :=
  fix locally_sortedb_impl (l : list A) :=
    match l with
    | [] => true
    | [_] => true
    | x :: ((y :: _) as l') => rb x y && locally_sortedb_impl l'
    end.

Definition locally_sortedb {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
  {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} :=
  locally_sortedb_impl rb.

Theorem locally_sortedb_spec :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    (l : list A),
  reflect (locally_sorted r l) (locally_sortedb r l).
Proof.
  intros ? ? ? ?. induction l.
  - simpl. apply ReflectT. auto.
  - simpl. destruct l.
    + apply ReflectT. auto.
    + rename a0 into b.
      destruct (DecidableBinaryRelation_spec r a b); destruct IHl; constructor; intuition auto.
Qed.

Definition locally_sortedb_impl_cost {A} rb {rb_Cost: Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('rb, 2), '(@cost_fun _ _ rb_Cost))]
    1
    (eval red in (@locally_sortedb_impl A rb))
    []
  ).

Theorem locally_sortedb_impl_cost_linear_on_cost_constant_rb :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} {rb_Cost: Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  big_o
    (locally_sortedb_impl_cost rb)
    (fun (l : list A) => 1 + length l).
Proof.
  intros ? ? ? ? ? ? ?. destruct H as (c & H). exists (c + 18). intros l. induction l.
  - simpl. lia.
  - simpl. destruct l.
    + lia.
    + rename a0 into b. specialize (H (a, b)). lia.
Qed.

Definition is_sorter {A} r {total_order : TotalOrder r} f :=
  forall (l : list A), is_permutation (f l) l /\ sorted r (f l).

Lemma sorted_equal_cons :
  forall {A} r {total_order : TotalOrder r} a b (l1 l2 : list A),
  sorted r (a :: l1) ->
  sorted r (b :: l2) ->
  is_permutation (a :: l1) (b :: l2) ->
  a = b /\ is_permutation l1 l2.
Proof.
  intros ? ? ? a b l1 l2 ? ? ?.
  assert (a = b). {
    apply permutation_cons_inversion in H1. destruct H1 as [? | (? & ?)].
    - auto.
    - destruct H as (? & _), H0 as (? & _).
      rewrite list_forall_list_in in H. rewrite list_forall_list_in in H0.
      apply H in H2; clear H. apply H0 in H1; clear H0. apply (TotalOrder_antisymmetry r); auto.
  }
  split.
  - apply H2.
  - subst b. apply permutation_same_head_inversion in H1. auto.
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
      * destruct H as (_ & ?), H0 as (_ & ?). apply IHl1; auto.
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
  is_permutation (insert_sorted r a l) (a :: l) /\ sorted r (insert_sorted r a l).
Proof.
  intros ? ? ? ? ? ? ? ?. induction l.
  - simpl. split.
    + apply is_permutation_add. apply is_permutation_empty.
    + auto.
  - rename a0 into b. destruct H as (? & ?). apply IHl in H0 as ?. destruct H1 as (? & ?).
    simpl. destruct (DecidableBinaryRelation_spec r a b).
    + split.
      * apply is_permutation_refl.
      * simpl. repeat split.
        -- auto.
        -- eapply list_forall_positive.
           2: apply H.
           eauto using (TotalOrder_transitivity r).
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
              ** destruct (TotalOrder_totality r a b); intuition auto.
              ** auto.
        -- auto.
Qed.

Definition insert_sorted_impl_cost {A} rb {rb_Cost: Cost (Signature [_; _] _) rb} :=
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
    {rb_Cost: Cost (Signature [_; _] _) rb},
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
    {rb_Cost: Cost (Signature [_; _] _) rb},
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
  - simpl. auto using is_permutation_empty.
  - simpl. destruct IHl as (IHl1 & IHl2).
    specialize (insert_sorted_correct _ a _ IHl2) as (? & ?).
    split.
    + apply is_permutation_trans with (a :: (insertion_sort r l)).
      * auto.
      * apply is_permutation_add. auto.
    + auto.
Qed.

Definition insertion_sort_impl_cost {A} rb {rb_Cost: Cost (Signature [_; _] _) rb} :=
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
    {rb_Cost: Cost (Signature [_; _] _) rb},
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

Theorem insertion_sort_cost_linear_on_cost_constant_total_order_and_list :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost: Cost (Signature [_; _] _) rb},
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
    + apply is_permutation_sym. apply (insertion_sort_correct r).
Qed.

Section Example.

Compute insertion_sort_impl_cost Nat.leb [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1].
Compute insertion_sort_impl_cost Nat.leb [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
Compute insertion_sort_impl_cost Nat.leb [10; 9; 8; 7; 6; 5; 4; 3; 2; 1].
Compute insertion_sort_impl_cost Nat.leb [20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1].

Compute insertion_sort Nat.le [4; 4; 6; 1; 0; 40; 3].

End Example.
