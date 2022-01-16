Load InsertionSort.

Definition quicksort_impl_left_predicate {A} (rb : A -> A -> bool) x := fun y => negb (rb x y).

Definition quicksort_impl_right_predicate {A} (rb : A -> A -> bool) x := fun y => rb x y.

Definition quicksort_impl {A} rb :=
  fix quicksort_impl (n : nat) (l : list A) :=
    match n, l with
    | 0, [] => []
    | S n', x :: l' =>
      quicksort_impl n' (filter (quicksort_impl_left_predicate rb x) l') ++
        x ::
        quicksort_impl n' (filter (quicksort_impl_right_predicate rb x) l')
    | _, _ => []
    end.

Definition quicksort {A} (r : A -> A -> Prop) {total_order : TotalOrder r}
  {rb} {decidable_binary_relation : DecidableBinaryRelation r rb} :=
  fun l => quicksort_impl rb (length l) l.

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
  (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb} x :
  Cost (Signature [_] _) (quicksort_impl_left_predicate rb x) := {
  cost_fun := quicksort_impl_left_predicate_cost rb x;
}.

#[export] Instance quicksort_impl_right_predicate_Cost {A}
  (rb : A -> A -> bool) {rb_Cost : Cost (Signature [_; _] _) rb} x :
  Cost (Signature [_] _) (quicksort_impl_right_predicate rb x) := {
  cost_fun := quicksort_impl_right_predicate_cost rb x;
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
          (@quicksort_impl_left_predicate_Cost _ _ rb_Cost _)
        )
      );
      (
        (use_rel_2 '(fun x => filter (quicksort_impl_right_predicate rb x)), 1),
        use_rel_2 '(fun x =>
          @filter_cost
          _
          (quicksort_impl_right_predicate rb x)
          (@quicksort_impl_right_predicate_Cost _ _ rb_Cost _)
        )
      );
      (('(@app A), 2), '(@app_cost A))
    ]
    2
    (eval red in (@quicksort_impl A rb))
    ['(@quicksort_impl A rb)]
  ).

Section Example.

Print quicksort_impl_cost.

Compute quicksort Nat.le [4; 4; 6; 1; 0; 40; 3].

End Example.
