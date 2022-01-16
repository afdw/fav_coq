Load ListCost.

Inductive is_permutation_alt {A} : list A -> list A -> Prop :=
  | is_permutation_alt_empty : is_permutation_alt [] []
  | is_permutation_alt_insert a l1 l2 l3 :
    is_permutation_alt (l1 ++ l2) l3 ->
    is_permutation_alt (l1 ++ a :: l2) (a :: l3).

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

Theorem permutation_length : forall {A} (l1 l2 : list A), is_permutation l1 l2 -> length l2 = length l1.
Proof.
  setoid_rewrite <- is_permutation_alt_is_permutation.
  intros ? ? ? ?. induction H.
  - auto.
  - rewrite length_app. rewrite length_app in IHis_permutation_alt. simpl. lia.
Qed.

Theorem list_forall_permutation :
  forall {A} f (l1 l2 : list A),
  is_permutation_alt l1 l2 ->
  list_forall f l1 -> list_forall f l2.
Proof.
  intros ? ? ? ? ?. induction H; intros ?.
  - auto.
  - simpl. apply list_forall_app in H0. simpl in H0.
    rewrite list_forall_app in IHis_permutation_alt. intuition auto.
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

