Load InsertionSort.

Definition quicksort_impl_left_predicate {A} (rb : A -> A -> bool) x := fun y => negb (rb x y).

Definition quicksort_impl_right_predicate {A} (rb : A -> A -> bool) x := fun y => rb x y.

Definition quicksort_impl {A} rb :=
  fix quicksort_impl (n : nat) (l : list A) :=
    match n with
    | 0 =>
      match l with
      | [] => []
      | _ :: _ => []
      end
    | S n' =>
      match l with
      | [] => []
      | x :: l' =>
        quicksort_impl n' (filter (quicksort_impl_left_predicate rb x) l') ++
          x ::
          quicksort_impl n' (filter (quicksort_impl_right_predicate rb x) l')
      end
    end.

Definition quicksort {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
  {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} :=
  fun l => quicksort_impl rb (length l) l.

Lemma quicksort_impl_enough_fuel :
  forall {A} rb n m (l : list A),
  length l <= n ->
  length l <= m ->
  quicksort_impl rb n l = quicksort_impl rb m l.
Proof.
  intros ? ? ?. induction n; intros ? ? ? ?.
  - destruct m.
    + auto.
    + destruct l; simpl in H; try lia. auto.
  - destruct m.
    + destruct l; simpl in H0; try lia. auto.
    + simpl. destruct l.
      * auto.
      * f_equal.
        -- specialize (length_filter_le (quicksort_impl_left_predicate rb a) l) as ?.
           simpl in H, H0. apply IHn; lia.
        -- f_equal. specialize (length_filter_le (quicksort_impl_right_predicate rb a) l) as ?.
           simpl in H, H0. apply IHn; lia.
Qed.

Theorem quicksort_correct :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb},
  is_sorter r (quicksort r).
Proof.
  unfold is_sorter, quicksort. intros ? ? ? ? ? ?.
  remember (length l) as n. assert (length l <= n) by lia; clear Heqn.
  generalize dependent l. induction n using nat_strong_induction; intros l ?.
  destruct n.
  - destruct l.
    + simpl. split.
      * apply permutation_nil.
      * auto.
    + simpl in H0. lia.
  - destruct l.
    + simpl. split.
      * apply permutation_nil.
      * auto.
    + simpl. unfold quicksort_impl_left_predicate, quicksort_impl_right_predicate. simpl in H0.
      specialize (length_filter_le (fun y => negb (rb a y)) l) as ?.
      specialize (length_filter_le (fun y => rb a y) l) as ?.
      destruct (
        H
        (length (filter (fun y => negb (rb a y)) l))
        ltac:(lia)
        (filter (fun y => negb (rb a y)) l)
        ltac:(lia)
      ) as (? & ?).
      destruct (
        H
        (length (filter (fun y => rb a y) l))
        ltac:(lia)
        (filter (fun y => rb a y) l)
        ltac:(lia)
      ) as (? & ?).
      rewrite <- (quicksort_impl_enough_fuel _ n) in H3, H4, H5, H6; try lia. clear H H0 H1 H2.
      split.
      * clear H4 H6. apply permutation_insert.
        assert (predicate_xor (fun y => negb (rb a y)) (fun y => rb a y)). {
          unfold predicate_xor. intros x. destruct (rb a x); intuition auto.
        }
        specialize (permutation_filter l (fun y => negb (rb a y)) (fun y => rb a y) H) as ?; clear H.
        eapply permutation_app_trans.
        -- apply H0.
        -- apply permutation_sym. auto.
        -- apply permutation_sym. auto.
      * apply sorted_app.
        -- auto.
        -- simpl. split.
           ++ eapply list_forall_permutation.
              ** apply permutation_sym. apply H5.
              ** rewrite list_forall_list_in. intros b ?.
                 rewrite list_in_filter in H. destruct H as (? & ?).
                 destruct (DecidableBinaryRelation_spec r a b); try discriminate.
                 auto.
           ++ auto.
        -- simpl. eapply list_forall_permutation.
           ++ apply permutation_sym. apply H3.
           ++ rewrite list_forall_list_in. intros b ?.
              rewrite list_in_filter in H. destruct H as (? & ?). split.
              ** destruct (DecidableBinaryRelation_spec r a b); try discriminate.
                 specialize (TotalOrder_totality r a b); intuition auto.
              ** eapply list_forall_permutation.
                 --- apply permutation_sym. apply H5.
                 --- rewrite list_forall_list_in. intros c ?.
                     rewrite list_in_filter in H1. destruct H1 as (? & ?).
                     destruct (DecidableBinaryRelation_spec r a b); try discriminate.
                     destruct (DecidableBinaryRelation_spec r a c); try discriminate.
                     destruct (DecidableBinaryRelation_spec r b a).
                     +++ apply (TotalOrder_transitivity r) with a; auto.
                     +++ specialize (TotalOrder_totality r a b); intuition auto.
Qed.

Definition quicksort_impl_left_predicate_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('rb, 2), '(@cost_fun _ _ rb_Cost))]
    2
    (eval red in (@quicksort_impl_left_predicate A rb))
    []
  ).

Definition quicksort_impl_right_predicate_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    Cost.refine_compute_cost
    [(('rb, 2), '(@cost_fun _ _ rb_Cost))]
    2
    (eval red in (@quicksort_impl_right_predicate A rb))
    []
  ).

#[export] Instance quicksort_impl_left_predicate_Cost {A}
  (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb} :
  Cost (Signature [_; _] _) (quicksort_impl_left_predicate rb) := {
  cost_fun := quicksort_impl_left_predicate_cost rb;
}.

#[export] Instance quicksort_impl_right_predicate_Cost {A}
  (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb} :
  Cost (Signature [_; _] _) (quicksort_impl_right_predicate rb) := {
  cost_fun := quicksort_impl_right_predicate_cost rb;
}.

Definition quicksort_impl_cost {A} rb {rb_Cost : Cost (Signature [_; _] _) rb} :=
  ltac2:(
    let use_rel_2 t :=
      match Constr.Unsafe.kind t with
      | Constr.Unsafe.Lambda _ body =>
        let body_subst := Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var @x)] 0 body in
        Constr.Unsafe.closenl [@x] 2 body_subst
      | _ => Control.throw Match_failure
      end in
    Cost.refine_compute_cost
    [
      (
        (use_rel_2 '(fun x => filter (quicksort_impl_left_predicate rb x)), 1),
        use_rel_2 '(fun x =>
          @filter_cost
          _
          (quicksort_impl_left_predicate rb x)
          (Cost_cons _ _ _ _ (@quicksort_impl_left_predicate_Cost _ _ rb_Cost) _)
        )
      );
      (
        (use_rel_2 '(fun x => filter (quicksort_impl_right_predicate rb x)), 1),
        use_rel_2 '(fun x =>
          @filter_cost
          _
          (quicksort_impl_right_predicate rb x)
          (Cost_cons _ _ _ _ (@quicksort_impl_right_predicate_Cost _ _ rb_Cost) _)
        )
      );
      (('(@app A), 2), '(@app_cost A))
    ]
    2
    (eval red in (@quicksort_impl A rb))
    ['(@quicksort_impl A rb)]
  ).

Theorem quicksort_impl_left_predicate_cost_constant_on_cost_constant_rb :
  forall {A} (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  binary_cost_constant (quicksort_impl_left_predicate_Cost rb).
Proof.
  intros ? ? ? ?. destruct H as (c & H). exists (c + 4). intros (a, b). specialize (H (a, b)).
  simpl. unfold quicksort_impl_left_predicate_cost. lia.
Qed.

Theorem quicksort_impl_right_predicate_cost_constant_on_cost_constant_rb :
  forall {A} (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  binary_cost_constant (quicksort_impl_right_predicate_Cost rb).
Proof.
  intros ? ? ? ?. destruct H as (c & H). exists (c + 4). intros (a, b). specialize (H (a, b)).
  simpl. unfold quicksort_impl_right_predicate_cost. lia.
Qed.

Lemma quicksort_cost_enough_fuel :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb}
    n m l,
  length l <= n ->
  length l <= m ->
  quicksort_impl_cost rb n l = quicksort_impl_cost rb m l.
Proof.
  intros ? ? ? ? ? ? ? ?. generalize dependent n. induction m; intros ? ? ? ?.
  - destruct n.
    + lia.
    + destruct l.
      * auto.
      * simpl in H0. lia.
  - destruct n.
    + destruct l.
      * simpl. lia.
      * simpl in H. lia.
    + destruct l.
      * simpl. lia.
      * simpl. simpl in H. simpl in H0.
        specialize (length_filter_le (quicksort_impl_left_predicate rb a) l) as ?.
        specialize (length_filter_le (quicksort_impl_right_predicate rb a) l) as ?.
        rewrite (IHm n (filter (quicksort_impl_left_predicate rb a) l) ltac:(lia) ltac:(lia)).
        rewrite (IHm n (filter (quicksort_impl_right_predicate rb a) l) ltac:(lia) ltac:(lia)).
        clear IHm.
        rewrite (quicksort_impl_enough_fuel _  n m); try lia.
        rewrite (quicksort_impl_enough_fuel _  n m); try lia.
Qed.

Theorem quicksort_cost_quadratic_on_cost_constant_rb :
  forall {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
    {rb} {decidable_binary_relation : DecidableBinaryRelation r rb}
    {rb_Cost : Cost (Signature [_; _] _) rb},
  binary_cost_constant rb_Cost ->
  big_o
    (fun l => quicksort_impl_cost rb (length l) l)
    (fun (l : list A) => 1 + (length l) * (length l)).
Proof.
  intros ? ? ? ? ? ? ?.
  specialize (@app_cost_linear A) as ?.
  specialize (
    filter_cost_linear_when_predicate_cost_constant_binary
    (quicksort_impl_left_predicate rb)
    (quicksort_impl_left_predicate_cost_constant_on_cost_constant_rb rb H)
  ) as ?.
  specialize (
    filter_cost_linear_when_predicate_cost_constant_binary
    (quicksort_impl_right_predicate rb)
    (quicksort_impl_right_predicate_cost_constant_on_cost_constant_rb rb H)
  ) as ?.
  clear H. destruct H0 as (c1 & H0), H1 as (c2 & H1), H2 as (c3 & H2).
  exists ((c1 + c2 + c3) * 2 + 18). intros l.
  remember (length l) as n. assert (length l <= n) by lia; clear Heqn.
  generalize dependent l. induction n using nat_strong_induction; intros l ?.
  destruct n.
  - simpl. destruct l; lia.
  - destruct l.
    + simpl. lia.
    + simpl. destruct (list_empty_or_not_empty l).
      * subst l. destruct n.
        -- simpl. lia.
        -- simpl. lia.
      * simpl in H3. apply le_S_n in H3.
        specialize (length_filter_le (quicksort_impl_left_predicate rb a) l) as ?.
        specialize (length_filter_le (quicksort_impl_right_predicate rb a) l) as ?.
        specialize (
          H0
          (
            (quicksort_impl rb (length l) (filter (quicksort_impl_left_predicate rb a) l)),
            (a :: quicksort_impl rb (length l) (filter (quicksort_impl_right_predicate rb a) l))
          )
        ).
        simpl in H0. do 2 rewrite (quicksort_impl_enough_fuel _ (length l) n) in H0; try lia.
        le_chain H0; clear H0.
        specialize (H1 (a, l)). simpl in H1. le_chain H1; clear H1.
        specialize (H2 (a, l)). simpl in H2. le_chain H2; clear H2.
        specialize (quicksort_correct r (filter (quicksort_impl_left_predicate rb a) l)) as (? & _).
        apply permutation_length in H0.
        unfold quicksort in H0. rewrite <- (quicksort_impl_enough_fuel _ n) in H0; try lia.
        specialize (quicksort_correct r (filter (quicksort_impl_right_predicate rb a) l)) as (? & _).
        apply permutation_length in H1.
        unfold quicksort in H1. rewrite <- (quicksort_impl_enough_fuel _ n) in H1; try lia.
        rewrite <- H0; clear H0. rewrite <- H1; clear H1.
        rewrite (
          quicksort_cost_enough_fuel
          _
          n
          (length (filter (quicksort_impl_left_predicate rb a) l))
          (filter (quicksort_impl_left_predicate rb a) l)
          ltac:(lia)
          ltac:(lia)
        ).
        rewrite (
          quicksort_cost_enough_fuel
          _
          n
          (length (filter (quicksort_impl_right_predicate rb a) l))
          (filter (quicksort_impl_right_predicate rb a) l)
          ltac:(lia)
          ltac:(lia)
        ).
        specialize (
          H
          (length (filter (quicksort_impl_left_predicate rb a) l))
          ltac:(lia)
          (filter (quicksort_impl_left_predicate rb a) l)
          ltac:(lia)
        ) as ?. le_chain H0; clear H0.
        specialize (
          H
          (length (filter (quicksort_impl_right_predicate rb a) l))
          ltac:(lia)
          (filter (quicksort_impl_right_predicate rb a) l)
          ltac:(lia)
        ) as ?. le_chain H0; clear H0.
        clear H.
        assert (predicate_xor (quicksort_impl_left_predicate rb a) (quicksort_impl_right_predicate rb a)). {
          unfold quicksort_impl_left_predicate, quicksort_impl_right_predicate.
          unfold predicate_xor. intros x. destruct (rb a x); intuition auto.
        }
        specialize (permutation_filter l _ _ H) as ?; clear H.
        apply permutation_length in H0. rewrite length_app in H0.
        replace (fun x => quicksort_impl_right_predicate rb a x)
          with (quicksort_impl_right_predicate rb a) in H0 by auto.
        remember (length (filter (quicksort_impl_left_predicate rb a) l)) as m.
        remember (length (filter (quicksort_impl_right_predicate rb a) l)) as k.
        rewrite H0 in *. repeat (eapply le_trans_rev; [le_chain_l H3 |]).
        assert (length l >= 1). {
          destruct l.
          - destruct n0. auto.
          - simpl. lia.
        }
        rewrite H0 in H. clear n0 Heqm Heqk H0 H3 H4 H5. nia.
Qed.

Section Example.

Compute quicksort Nat.le [4; 4; 6; 1; 0; 40; 3].

End Example.
