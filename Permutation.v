Load ListCost.

Inductive permutation {A} : list A -> list A -> Prop :=
  | permutation_nil : permutation [] []
  | permutation_insert a l1 l2 l3 :
    permutation (l1 ++ l2) l3 ->
    permutation (l1 ++ a :: l2) (a :: l3).

Inductive permutation_small {A} : list A -> list A -> Prop :=
  | permutation_small_empty : permutation_small [] []
  | permutation_small_cons a l1 l2 : permutation_small l1 l2 -> permutation_small (a :: l1) (a :: l2)
  | permutation_small_swap a b l : permutation_small (b :: a :: l) (a :: b :: l)
  | permutation_small_trans l1 l2 l3 :
    permutation_small l1 l2 ->
    permutation_small l2 l3 ->
    permutation_small l1 l3.

Section Example.

Theorem permutation_example : permutation [5; 3; 1; 2; 4] [1; 2; 3; 4; 5].
Proof.
  replace [5; 3; 1; 2; 4] with ([5; 3] ++ 1 :: [2; 4]) by auto; apply permutation_insert; simpl.
  replace [5; 3; 2; 4] with ([5; 3] ++ 2 :: [4]) by auto; apply permutation_insert; simpl.
  replace [5; 3; 4] with ([5] ++ 3 :: [4]) by auto; apply permutation_insert; simpl.
  replace [5; 4] with ([5] ++ 4 :: []) by auto; apply permutation_insert; simpl.
  replace [5] with ([] ++ 5 :: []) by auto; apply permutation_insert; simpl.
  apply permutation_nil.
Qed.

Theorem permutation_example_move : permutation [5; 3; 1; 2; 4] [3; 1; 2; 4; 5].
Proof.
  replace [5; 3; 1; 2; 4] with ([5] ++ 3 :: [1; 2; 4]) by auto; apply permutation_insert; simpl.
  replace [5; 1; 2; 4] with ([5] ++ 1 :: [2; 4]) by auto; apply permutation_insert; simpl.
  replace [5; 2; 4] with ([5] ++ 2 :: [4]) by auto; apply permutation_insert; simpl.
  replace [5; 4] with ([5] ++ 4 :: []) by auto; apply permutation_insert; simpl.
  replace [5] with ([] ++ 5 :: []) by auto; apply permutation_insert; simpl.
  apply permutation_nil.
Qed.

Theorem permutation_example_sym : permutation [1; 2; 3; 4; 5] [5; 3; 1; 2; 4].
Proof.
  replace [1; 2; 3; 4; 5] with ([1; 2; 3; 4] ++ 5 :: []) by auto; apply permutation_insert; simpl.
  replace [1; 2; 3; 4] with ([1; 2] ++ 3 :: [4]) by auto; apply permutation_insert; simpl.
  replace [1; 2; 4] with ([] ++ 1 :: [2; 4]) by auto; apply permutation_insert; simpl.
  replace [2; 4] with ([] ++ 2 :: [4]) by auto; apply permutation_insert; simpl.
  replace [4] with ([] ++ 4 :: []) by auto; apply permutation_insert; simpl.
  apply permutation_nil.
Qed.

Theorem permutation_small_example : permutation_small [5; 3; 1; 2; 4] [1; 2; 3; 4; 5].
Proof.
  apply permutation_small_trans with [5; 1; 3; 2; 4].
  apply permutation_small_cons.
  apply permutation_small_swap.
  apply permutation_small_trans with [1; 5; 3; 2; 4].
  apply permutation_small_swap.
  apply permutation_small_cons.
  apply permutation_small_trans with [5; 2; 3; 4].
  apply permutation_small_cons.
  apply permutation_small_swap.
  apply permutation_small_trans with [2; 5; 3; 4].
  apply permutation_small_swap.
  apply permutation_small_cons.
  apply permutation_small_trans with [3; 5; 4].
  apply permutation_small_swap.
  apply permutation_small_cons.
  apply permutation_small_swap.
Qed.

End Example.

Theorem permutation_small_refl : forall {A} (l : list A), permutation_small l l.
Proof.
  induction l.
  - apply permutation_small_empty.
  - apply permutation_small_cons. auto.
Qed.

Theorem permutation_refl : forall {A} (l : list A), permutation l l.
Proof.
  induction l.
  - apply permutation_nil.
  - replace (a :: l) with ([] ++ a :: l) by auto. apply permutation_insert. auto.
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

Lemma permutation_split:
  forall {A} a (l1 l2 l3 : list A),
  permutation l1 (l2 ++ a :: l3) ->
  exists l4 l5, l1 = l4 ++ a :: l5 /\ permutation (l4 ++ l5) (l2 ++ l3).
Proof.
  intros ? a l1 l2 l3 ?. remember (l2 ++ a :: l3) as l4. generalize dependent l2. induction H; intros l2' Heql4.
  - destruct l2'; discriminate.
  - rename a0 into b. destruct l2'.
    + injection Heql4 as <- ->. exists l1, l2. auto.
    + injection Heql4 as <- ->.
      specialize (IHpermutation l2' eq_refl).  destruct IHpermutation as (l9 & l10 & ? & ?).
      apply app_insert_split in H0. destruct H0 as [(l6 & -> & ->) | (l6 & -> & ->)].
      * rewrite app_assoc in H1. exists (l1 ++ b :: l6), l10. simpl. split.
        -- rewrite app_assoc. auto.
        -- rewrite app_assoc. simpl. apply permutation_insert. auto.
      * rewrite app_assoc in H. exists l9, (l6 ++ b :: l2). simpl. split.
        -- rewrite app_assoc. auto.
        -- rewrite <- app_assoc. apply permutation_insert. rewrite app_assoc. auto.
Qed.

Lemma permutation_move :
  forall {A} a (l1 l2 l3 : list A),
  permutation l1 (l2 ++ a :: l3) ->
  permutation l1 (a :: l2 ++ l3).
Proof.
  intros A a l1 l2 l3 ?.
  apply permutation_split in H. destruct H as (l4 & l5 & -> & ?).
  apply permutation_insert. auto.
Qed.

Theorem permutation_trans :
  forall {A} (l1 l2 l3 : list A),
  permutation l1 l2 ->
  permutation l2 l3 ->
  permutation l1 l3.
Proof.
  intros ? l1 l2 l3 ? ?.
  generalize dependent l2. generalize dependent l1. induction l3; intros l1 l2 H1 H2.
  - inversion H2. subst l2. auto.
  - inversion H2. subst a0 l2 l5. clear H2.
    apply permutation_move in H1.
    inversion H1. subst a0 l1 l6. apply permutation_insert. apply IHl3 with (l0 ++ l4); auto.
Qed.

Theorem permutation_sym :
  forall {A} (l1 l2 : list A),
  permutation l1 l2 ->
  permutation l2 l1.
Proof.
  intros ? l1 l2 ?. generalize dependent l1. induction l2; intros l1 ?.
  - inversion H. apply permutation_nil.
  - inversion H. subst a0 l1 l4. clear H. apply IHl2 in H2. clear IHl2.
    generalize dependent l3. generalize dependent l2. induction l0; intros l2 l3 ?.
    + simpl. simpl in H2. replace (a :: l2) with ([] ++ a :: l2) by auto.
      apply permutation_insert. auto.
    + rename a0 into b. simpl in H2. inversion H2. subst a0 l2 l5. simpl.
      replace (a :: l1 ++ b :: l4) with ((a :: l1) ++ b :: l4) by auto.
      apply permutation_insert. simpl. auto.
Qed.

Theorem permutation_cons :
  forall {A} a (l1 l2 : list A),
  permutation l1 l2 ->
  permutation (a :: l1) (a :: l2).
Proof.
  intros ? ? ? ? ?. replace (a :: l1) with ([] ++ a :: l1) by auto. apply permutation_insert. auto.
Qed.

Theorem permutation_swap :
  forall {A} a b (l1 l2 : list A),
  permutation l1 l2 ->
  permutation (b :: a :: l1) (a :: b :: l2).
Proof.
  intros ? ? ? ? ? ?.
  replace (b :: a :: l1) with ([b] ++ a :: l1) by auto. apply permutation_insert.
  apply permutation_cons. auto.
Qed.

Theorem permutation_small_permutation :
  forall {A} (l1 l2 : list A),
  permutation_small l1 l2 <-> permutation l1 l2.
Proof.
  intros ? l1 l2. split.
  - intros ?. induction H.
    + apply permutation_nil.
    + replace (a :: l1) with ([] ++ a :: l1) by auto. apply permutation_insert; auto.
    + cut (permutation (b :: [a] ++ l) (a :: [b] ++ l)).
      * auto.
      * apply permutation_move. apply permutation_refl.
    + clear H H0. apply permutation_trans with l2; auto.
  - intros ?. induction H.
    + apply permutation_small_empty.
    + apply permutation_small_trans with (a :: l1 ++ l2).
      * clear H IHpermutation l3. induction l1.
        -- simpl. apply permutation_small_refl.
        -- rename a0 into b. simpl. apply permutation_small_trans with (b :: a :: l1 ++ l2).
           ++ apply permutation_small_cons. auto.
           ++ apply permutation_small_swap.
      * apply permutation_small_cons. auto.
Qed.

Theorem permutation_length : forall {A} (l1 l2 : list A), permutation l1 l2 -> length l2 = length l1.
Proof.
  intros ? ? ? ?. induction H.
  - auto.
  - rewrite length_app. rewrite length_app in IHpermutation. simpl. lia.
Qed.

Theorem list_forall_permutation :
  forall {A} f (l1 l2 : list A),
  permutation l1 l2 ->
  list_forall f l1 -> list_forall f l2.
Proof.
  intros ? ? ? ? ?. induction H; intros ?.
  - auto.
  - simpl. apply list_forall_app in H0. simpl in H0.
    rewrite list_forall_app in IHpermutation. intuition auto.
Qed.

Theorem permutation_same_head_inversion :
  forall {A} a (l1 l2 : list A),
  permutation (a :: l1) (a :: l2) ->
  permutation l1 l2.
Proof.
  intros ? ? ? ? ?. inversion H. subst a0 l4. destruct l0.
  - injection H0 as ->. auto.
  - injection H0 as -> <-. apply permutation_trans with (a  :: l0 ++ l3).
    + apply permutation_move. apply permutation_refl.
    + auto.
Qed.

Theorem app_permutation_inversion :
  forall {A} (l1 l2 l3 l4 : list A),
  permutation (l1 ++ l3) (l2 ++ l4) ->
  permutation l1 l2 ->
  permutation l3 l4.
Proof.
  intros ? ? ? ? ? ? ?. generalize dependent l4. generalize dependent l3. induction H0; intros l3_ l4_ ?.
  - auto.
  - rewrite app_assoc in H. simpl in H.
    apply permutation_sym in H. apply permutation_move in H. apply permutation_sym in H.
    apply permutation_same_head_inversion in H. apply IHpermutation. rewrite app_assoc. auto.
Qed.

Theorem permutation_nil_inversion :
  forall {A} (l : list A),
  permutation l [] ->
  l = [].
Proof.
  intros ? ? ?. inversion H. auto.
Qed.

Theorem permutation_single_inversion :
  forall {A} a (l : list A),
  permutation l [a] ->
  l = [a].
Proof.
  intros ? ? ? ?. inversion H. subst a0 l3. apply permutation_nil_inversion in H2.
  apply app_nil_inversion in H2. destruct H2 as (-> & ->). auto.
Qed.

Theorem permutation_single_inversion' :
  forall {A} (a b : A),
  permutation [a] [b] ->
  a = b.
Proof.
  intros ? ? ? ?. apply permutation_single_inversion in H. injection H as ->. auto.
Qed.

Theorem permutation_cons_inversion :
  forall {A} a b (l1 l2 : list A),
  permutation (a :: l1) (b :: l2) ->
  a = b \/ list_in a l2 /\ list_in b l1.
Proof.
  intros ? ? ? ? ? ?. inversion H. subst a0 l4. destruct l0.
  - injection H0 as -> ->. left. auto.
  - injection H0 as -> <-. right. split.
    + apply permutation_sym in H2. inversion H2. subst a0 l5. apply list_in_insert.
    + apply list_in_insert.
Qed.
