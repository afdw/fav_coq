Load Permutation.

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

Definition locally_sortedb_impl_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('rb, 2), '(@cost_fun _ _ rb_Cost))]
    1
    (eval red in (@locally_sortedb_impl A rb))
    []
  ).

Theorem locally_sortedb_impl_cost_linear_on_cost_constant_rb :
  forall {A} r {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} {rb_Cost : Cost (Signature [_; _] _) rb},
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
  forall (l : list A), permutation (f l) l /\ sorted r (f l).

Lemma sorted_equal_cons :
  forall {A} r {total_order : TotalOrder r} a b (l1 l2 : list A),
  sorted r (a :: l1) ->
  sorted r (b :: l2) ->
  permutation (a :: l1) (b :: l2) ->
  a = b /\ permutation l1 l2.
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
  permutation l1 l2 ->
  l1 = l2.
Proof.
  intros ? ? ? l1 l2 ? ? ?. generalize dependent l2. induction l1; intros l2 ? ?.
  - symmetry. apply permutation_nil_inversion. apply permutation_sym. auto.
  - destruct l2.
    + apply permutation_nil_inversion. auto.
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
  - apply permutation_trans with l.
    + auto.
    + apply permutation_sym. auto.
Qed.

Theorem sorted_app :
  forall {A} r {total_order : TotalOrder r} (l1 l2 : list A),
  sorted r l1 ->
  sorted r l2 ->
  list_forall (fun x => list_forall (fun y => r x y) l2) l1 ->
  sorted r (l1 ++ l2).
Proof.
  intros ? ? ? ?. induction l1; intros ? ? ? ?.
  - auto.
  - simpl. simpl in H, H1. destruct H as (? & ?), H1 as (? & ?). split.
    + apply list_forall_app; auto.
    + apply IHl1.
      * intuition auto.
      * auto.
      * eapply list_forall_positive.
        2: apply H3.
        intros b ?. simpl in H4. intuition auto.
Qed.
