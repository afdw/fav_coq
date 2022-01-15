Load Cost.

Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import ArithRing.

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

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Theorem list_forall_positive :
  forall {A} f g (l : list A),
  (forall a, (f a : Prop) -> (g a : Prop)) ->
  list_forall f l -> list_forall g l.
Proof.
  intros ? ? ? ? ? ?. induction l.
  - auto.
  - destruct H0 as (? & ?). split.
    + auto.
    + auto.
Qed.

Fixpoint list_in {A} a (l : list A) :=
  match l with
  | [] => False
  | x :: l' => x = a \/ list_in a l'
  end.

Theorem list_forall_list_in :
  forall {A} f (l : list A),
  list_forall f l <-> (forall a, list_in a l -> f a).
Proof.
  intros ? ? l. induction l.
  - simpl. intuition auto.
  - simpl. split.
    + intros (? & ?) b [? | ?].
      * subst b. auto.
      * apply IHl; auto.
    + intros ?. split.
      * apply H. left. auto.
      * apply IHl. intuition auto.
Qed.

Inductive is_permutation {A} : list A -> list A -> Prop :=
  | is_permutation_empty : is_permutation [] []
  | is_permutation_add a l1 l2 : is_permutation l1 l2 -> is_permutation (a :: l1) (a :: l2)
  | is_permutation_swap a b l : is_permutation (b :: a :: l) (a :: b :: l)
  | is_permutation_trans l1 l2 l3 : is_permutation l1 l2 -> is_permutation l2 l3 -> is_permutation l1 l3.

Section Example.

Theorem is_permutation_example : is_permutation [5; 3; 1; 2; 4] [1; 2; 3; 4; 5].
Proof.
  apply is_permutation_trans with [5; 1; 3; 2; 4].
  apply is_permutation_add.
  apply is_permutation_swap.
  apply is_permutation_trans with [1; 5; 3; 2; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_trans with [5; 2; 3; 4].
  apply is_permutation_add.
  apply is_permutation_swap.
  apply is_permutation_trans with [2; 5; 3; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_trans with [3; 5; 4].
  apply is_permutation_swap.
  apply is_permutation_add.
  apply is_permutation_swap.
Qed.

End Example.

Theorem is_permutation_refl : forall {A} (l : list A), is_permutation l l.
Proof.
  induction l.
  - apply is_permutation_empty.
  - apply is_permutation_add. auto.
Qed.

Theorem is_permutation_sym : forall {A} (l1 l2 : list A), is_permutation l1 l2 -> is_permutation l2 l1.
Proof.
  intros ? ? ? ?. induction H.
  - apply is_permutation_empty.
  - apply is_permutation_add. auto.
  - apply is_permutation_swap.
  - apply is_permutation_trans with l2; auto.
Qed.

Theorem permutation_length : forall {A} (l1 l2 : list A), is_permutation l1 l2 -> length l2 = length l1.
Proof.
  intros ? ? ? ?. induction H; simpl; lia.
Qed.

Theorem permutation_empty : forall {A} (l : list A), is_permutation l [] -> l = [].
Proof.
  intros ? ? ?. remember [] as l'. induction H.
  - auto.
  - discriminate.
  - discriminate.
  - subst l3. rewrite <- (IHis_permutation2 eq_refl). auto.
Qed.

Theorem permutation_single : forall {A} a (l : list A), is_permutation l [a] -> l = [a].
Proof.
  intros ? ? ? ?. remember [a] as l'. induction H.
  - auto.
  - injection Heql' as ? ?. subst a0 l2. f_equal. apply permutation_empty. auto.
  - discriminate.
  - subst l3. rewrite <- (IHis_permutation2 eq_refl). auto.
Qed.

Theorem list_forall_permutation :
  forall {A} f (l1 l2 : list A),
  is_permutation l1 l2 ->
  list_forall f l1 -> list_forall f l2.
Proof.
  intros ? ? ? ? ?. induction H; intros ?.
  - auto.
  - destruct H0 as (? & ?). split; auto.
  - destruct H as (? & ? & ?). repeat split; auto.
  - auto.
Qed.

Fixpoint app {A} (l1 l2 : list A) :=
  match l1 with
  | [] => l2
  | x :: l1' => x :: app l1' l2
  end.

Infix "++" := app (right associativity, at level 60).

Theorem app_assoc : forall {A} (l1 l2 l3 : list A), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros ? l1 l2 l3. induction l1.
  - auto.
  - simpl. f_equal. auto.
Qed.

Theorem app_empty_inversion : forall {A} (l1 l2 : list A), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros ? ? ? ?. destruct l1, l2; auto; discriminate.
Qed.

Theorem list_in_app : forall {A} a (l1 l2 : list A), list_in a (l1 ++ l2) <-> list_in a l1 \/ list_in a l2.
Proof.
  intros ? a l1 l2. induction l1.
  - simpl. intuition auto.
  - rename a0 into b. simpl. rewrite IHl1. intuition auto.
Qed.

Theorem list_forall_app :
  forall {A} f (l1 l2 : list A),
  list_forall f (l1 ++ l2) <-> list_forall f l1 /\ list_forall f l2.
Proof.
  setoid_rewrite list_forall_list_in. setoid_rewrite list_in_app. intuition auto.
Qed.

Theorem list_in_insert : forall {A} a (l1 l2 : list A), list_in a (l1 ++ a :: l2).
Proof.
  intros ? ? ? ?. induction l1.
  - simpl. intuition auto.
  - simpl. intuition auto.
Qed.

Section Unused.

Fixpoint rev {A} (l : list A) :=
  match l with
  | [] => []
  | x :: l' => rev l' ++ [x]
  end.

Theorem list_empty_or_not_empty : forall {A} (l : list A), {l = []} + {l <> []}.
Proof.
  intros ? l. destruct l.
  - left. auto.
  - right. discriminate.
Qed.

End Unused.

Inductive is_permutation_alt {A} : list A -> list A -> Prop :=
  | is_permutation_alt_empty : is_permutation_alt [] []
  | is_permutation_alt_insert a l1 l2 l3 :
    is_permutation_alt (l1 ++ l2) l3 ->
    is_permutation_alt (l1 ++ a :: l2) (a :: l3).

Section Example.

Theorem is_permutation_alt_example : is_permutation_alt [5; 3; 1; 2; 4] [1; 2; 3; 4; 5].
Proof.
  replace [5; 3; 1; 2; 4] with ([5; 3] ++ 1 :: [2; 4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 3; 2; 4] with ([5; 3] ++ 2 :: [4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 3; 4] with ([5] ++ 3 :: [4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 4] with ([5] ++ 4 :: []) by auto; apply is_permutation_alt_insert; simpl.
  replace [5] with ([] ++ 5 :: []) by auto; apply is_permutation_alt_insert; simpl.
  apply is_permutation_alt_empty.
Qed.

Theorem is_permutation_alt_example_move : is_permutation_alt [5; 3; 1; 2; 4] [3; 1; 2; 4; 5].
Proof.
  replace [5; 3; 1; 2; 4] with ([5] ++ 3 :: [1; 2; 4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 1; 2; 4] with ([5] ++ 1 :: [2; 4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 2; 4] with ([5] ++ 2 :: [4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [5; 4] with ([5] ++ 4 :: []) by auto; apply is_permutation_alt_insert; simpl.
  replace [5] with ([] ++ 5 :: []) by auto; apply is_permutation_alt_insert; simpl.
  apply is_permutation_alt_empty.
Qed.

Theorem is_permutation_alt_example_sym : is_permutation_alt [1; 2; 3; 4; 5] [5; 3; 1; 2; 4].
Proof.
  replace [1; 2; 3; 4; 5] with ([1; 2; 3; 4] ++ 5 :: []) by auto; apply is_permutation_alt_insert; simpl.
  replace [1; 2; 3; 4] with ([1; 2] ++ 3 :: [4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [1; 2; 4] with ([] ++ 1 :: [2; 4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [2; 4] with ([] ++ 2 :: [4]) by auto; apply is_permutation_alt_insert; simpl.
  replace [4] with ([] ++ 4 :: []) by auto; apply is_permutation_alt_insert; simpl.
  apply is_permutation_alt_empty.
Qed.

End Example.

Theorem is_permutation_alt_refl : forall {A} (l : list A), is_permutation_alt l l.
Proof.
  induction l.
  - apply is_permutation_alt_empty.
  - replace (a :: l) with ([] ++ a :: l) by auto. apply is_permutation_alt_insert. auto.
Qed.

Lemma app_insert_split :
  forall {A} a (l1 l2 l3 l4 : list A),
  l1 ++ l2 = l3 ++ a :: l4 ->
    (exists l5 : list A, l3 = l1 ++ l5 /\ l2 = l5 ++ a :: l4) \/
    (exists l5 : list A, l4 = l5 ++ l2 /\ l1 = l3 ++ a :: l5).
Proof.
  intros ? a l1. induction l1; intros l2 l3 l4 ?.
  - destruct l3.
    + simpl in H. subst l2. left. exists []. auto.
    + rename a0 into b. simpl in H. subst l2. left. exists (b :: l3). auto.
  - rename a0 into b. destruct l3.
    + injection H as -> <-. right. exists l1. auto.
    + rename a0 into c. injection H as -> ?. specialize (IHl1 _ _ _ H). clear H.
      destruct IHl1 as [(l5 & -> & ->) | (l5 & -> & ->)].
      * left. exists l5. auto.
      * right. exists l5. auto.
Qed.

Lemma permutation_alt_split:
  forall {A} a (l1 l2 l3 : list A),
  is_permutation_alt l1 (l2 ++ a :: l3) ->
  exists l4 l5, l1 = l4 ++ a :: l5 /\ is_permutation_alt (l4 ++ l5) (l2 ++ l3).
Proof.
  intros ? a l1 l2 l3 ?. remember (l2 ++ a :: l3) as l4. generalize dependent l2. induction H; intros l2' Heql4.
  - destruct l2'; discriminate.
  - rename a0 into b. destruct l2'.
    + injection Heql4 as <- ->. exists l1, l2. auto.
    + injection Heql4 as <- ->.
      specialize (IHis_permutation_alt l2' eq_refl).  destruct IHis_permutation_alt as (l9 & l10 & ? & ?).
      apply app_insert_split in H0. destruct H0 as [(l6 & -> & ->) | (l6 & -> & ->)].
      * rewrite app_assoc in H1. exists (l1 ++ b :: l6), l10. simpl. split.
        -- rewrite app_assoc. auto.
        -- rewrite app_assoc. simpl. apply is_permutation_alt_insert. auto.
      * rewrite app_assoc in H. exists l9, (l6 ++ b :: l2). simpl. split.
        -- rewrite app_assoc. auto.
        -- rewrite <- app_assoc. apply is_permutation_alt_insert. rewrite app_assoc. auto.
Qed.

Lemma is_permutation_alt_move :
  forall {A} a (l1 l2 l3 : list A),
  is_permutation_alt l1 (l2 ++ a :: l3) ->
  is_permutation_alt l1 (a :: l2 ++ l3).
Proof.
  intros A a l1 l2 l3 ?.
  apply permutation_alt_split in H. destruct H as (l4 & l5 & -> & ?).
  apply is_permutation_alt_insert. auto.
Qed.

Theorem is_permutation_alt_trans :
  forall {A} (l1 l2 l3 : list A),
  is_permutation_alt l1 l2 ->
  is_permutation_alt l2 l3 ->
  is_permutation_alt l1 l3.
Proof.
  intros ? l1 l2 l3 ? ?.
  generalize dependent l2. generalize dependent l1. induction l3; intros l1 l2 H1 H2.
  - inversion H2. subst l2. auto.
  - inversion H2. subst a0 l2 l5. clear H2.
    apply is_permutation_alt_move in H1.
    inversion H1. subst a0 l1 l6. apply is_permutation_alt_insert. apply IHl3 with (l0 ++ l4); auto.
Qed.

Theorem is_permutation_alt_sym :
  forall {A} (l1 l2 : list A),
  is_permutation_alt l1 l2 ->
  is_permutation_alt l2 l1.
Proof.
  intros ? l1 l2 ?. generalize dependent l1. induction l2; intros l1 ?.
  - inversion H. apply is_permutation_alt_empty.
  - inversion H. subst a0 l1 l4. clear H. apply IHl2 in H2. clear IHl2.
    generalize dependent l3. generalize dependent l2. induction l0; intros l2 l3 ?.
    + simpl. simpl in H2. replace (a :: l2) with ([] ++ a :: l2) by auto.
      apply is_permutation_alt_insert. auto.
    + rename a0 into b. simpl in H2. inversion H2. subst a0 l2 l5. simpl.
      replace (a :: l1 ++ b :: l4) with ((a :: l1) ++ b :: l4) by auto.
      apply is_permutation_alt_insert. simpl. auto.
Qed.

Theorem is_permutation_alt_is_permutation :
  forall {A} (l1 l2 : list A),
  is_permutation_alt l1 l2 <-> is_permutation l1 l2.
Proof.
  intros ? l1 l2. split.
  - intros ?. induction H.
    + apply is_permutation_empty.
    + apply is_permutation_trans with (a :: l1 ++ l2).
      * clear H IHis_permutation_alt l3. induction l1.
        -- simpl. apply is_permutation_refl.
        -- rename a0 into b. simpl. apply is_permutation_trans with (b :: a :: l1 ++ l2).
           ++ apply is_permutation_add. auto.
           ++ apply is_permutation_swap.
      * apply is_permutation_add. auto.
  - intros ?. induction H.
    + apply is_permutation_alt_empty.
    + replace (a :: l1) with ([] ++ a :: l1) by auto. apply is_permutation_alt_insert; auto.
    + cut (is_permutation_alt (b :: [a] ++ l) (a :: [b] ++ l)).
      * auto.
      * apply is_permutation_alt_move. apply is_permutation_alt_refl.
    + clear H H0. apply is_permutation_alt_trans with l2; auto.
Qed.

Theorem permutation_same_head_inversion :
  forall {A} a (l1 l2 : list A),
  is_permutation (a :: l1) (a :: l2) ->
  is_permutation l1 l2.
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ? ? ?. inversion H. subst a0 l4. destruct l0.
  - injection H0 as ->. auto.
  - injection H0 as -> <-. apply is_permutation_alt_trans with (a  :: l0 ++ l3).
    + apply is_permutation_alt_move. apply is_permutation_alt_refl.
    + auto.
Qed.

Theorem app_permutation_inversion :
  forall {A} (l1 l2 l3 l4 : list A),
  is_permutation (l1 ++ l3) (l2 ++ l4) ->
  is_permutation l1 l2 ->
  is_permutation l3 l4.
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ? ? ? ? ?. generalize dependent l4. generalize dependent l3. induction H0; intros l3_ l4_ ?.
  - auto.
  - rewrite app_assoc in H. simpl in H.
    apply is_permutation_alt_sym in H. apply is_permutation_alt_move in H. apply is_permutation_alt_sym in H.
    apply is_permutation_alt_is_permutation in H. apply permutation_same_head_inversion in H.
    apply is_permutation_alt_is_permutation in H. apply IHis_permutation_alt. rewrite app_assoc. auto.
Qed.

Theorem permutation_empty_inversion :
  forall {A} (l : list A),
  is_permutation l [] ->
  l = [].
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ?. inversion H. auto.
Qed.

Theorem permutation_single_inversion :
  forall {A} a (l : list A),
  is_permutation l [a] ->
  l = [a].
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ? ?. inversion H. subst a0 l3. rewrite is_permutation_alt_is_permutation in H2.
  apply permutation_empty_inversion in H2. apply app_empty_inversion in H2. destruct H2 as (-> & ->). auto.
Qed.

Theorem permutation_single_inversion' :
  forall {A} (a b : A),
  is_permutation [a] [b] ->
  a = b.
Proof.
  intros ? ? ? ?. apply permutation_single_inversion in H. injection H as ->. auto.
Qed.

Theorem permutation_cons_inversion :
  forall {A} a b (l1 l2 : list A),
  is_permutation (a :: l1) (b :: l2) ->
  a = b \/ list_in a l2 /\ list_in b l1.
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ? ? ? ?. inversion H. subst a0 l4. destruct l0.
  - injection H0 as -> ->. left. auto.
  - injection H0 as -> <-. right. split.
    + apply is_permutation_alt_sym in H2. inversion H2. subst a0 l5. apply list_in_insert.
    + apply list_in_insert.
Qed.
