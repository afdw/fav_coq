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

Fixpoint app {A} (l1 l2 : list A) :=
  match l1 with
  | [] => l2
  | x :: l1' => x :: app l1' l2
  end.

Infix "++" := app (right associativity, at level 60).

Definition length {A} :=
  fix length (l : list A) :=
    match l with
    | [] => 0
    | x :: l' => S (length l')
    end.

Definition filter {A} (predicate : A -> bool) :=
  fix filter (l : list A) :=
    match l with
    | [] => []
    | x :: l' =>
      if predicate x
      then x :: (filter l')
      else filter l'
    end.

Fixpoint rev {A} (l : list A) :=
  match l with
  | [] => []
  | x :: l' => rev l' ++ [x]
  end.

Fixpoint list_forall {A} f (l : list A) :=
  match l with
  | [] => True
  | x :: l' => f x /\ list_forall f l'
  end.

Fixpoint list_in {A} a (l : list A) :=
  match l with
  | [] => False
  | x :: l' => x = a \/ list_in a l'
  end.

Theorem nat_strong_induction :
  forall (P : nat -> Prop),
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros ? ? ?. cut (forall m, m <= n -> P m).
  - intros ?. specialize (H0 n). apply H0. lia.
  - induction n.
    + intros ? ?. apply H. intros k ?. lia.
    + intros ? ?. apply H. intros k ?. apply IHn. lia.
Qed.

Lemma le_trans_rev : forall n m p, m <= p -> n <= m -> n <= p.
Proof.
  eauto using le_trans.
Qed.

Ltac le_chain_l H :=
  match type of H with
  | ?a <= ?b =>
    match goal with
    | [ |- ?a <= ?b ] => exact H
    | [ |- ?l <= S ?c ] => eapply le_trans_rev; [apply le_n_S; le_chain_l H | apply le_refl]
    | [ |- ?l <= ?c + ?d ] => eapply le_trans_rev; [apply plus_le_compat_l; le_chain_l H | apply le_refl]
    | [ |- ?l <= ?c + ?d ] => eapply le_trans_rev; [apply plus_le_compat_r; le_chain_l H | apply le_refl]
    | [ |- ?l <= ?c * ?d ] => eapply le_trans_rev; [apply mult_le_compat_l; le_chain_l H | apply le_refl]
    | [ |- ?l <= ?c * ?d ] => eapply le_trans_rev; [apply mult_le_compat_r; le_chain_l H | apply le_refl]
    end
  end.

Ltac le_chain_r H :=
  match type of H with
  | ?a <= ?b =>
    match goal with
    | [ |- ?a <= ?b ] => exact H
    | [ |- S ?c <= ?r ] => eapply le_trans; [apply le_n_S; le_chain_r H | apply le_refl]
    | [ |- ?c + ?d <= ?r ] => eapply le_trans; [apply plus_le_compat_l; le_chain_r H | apply le_refl]
    | [ |- ?c + ?d <= ?r ] => eapply le_trans; [apply plus_le_compat_r; le_chain_r H | apply le_refl]
    | [ |- ?c * ?d <= ?r ] => eapply le_trans; [apply mult_le_compat_l; le_chain_r H | apply le_refl]
    | [ |- ?c * ?d <= ?r ] => eapply le_trans; [apply mult_le_compat_r; le_chain_r H | apply le_refl]
    end
  end.

Ltac le_chain H := first[eapply le_trans_rev; [le_chain_l H |] | eapply le_trans; [le_chain_r H |]].

Ltac clear_S :=
  simpl; repeat match goal with
  | [ |- context[S ?n] ] => progress (rewrite <- (Nat.add_1_r n); simpl)
  end.

Theorem list_empty_or_not_empty : forall {A} (l : list A), {l = []} + {l <> []}.
Proof.
  intros ? l. destruct l.
  - left. auto.
  - right. discriminate.
Qed.

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

Theorem app_assoc : forall {A} (l1 l2 l3 : list A), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros ? l1 l2 l3. induction l1.
  - auto.
  - simpl. f_equal. auto.
Qed.

Theorem app_nil_inversion : forall {A} (l1 l2 : list A), l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros ? ? ? ?. destruct l1, l2; auto; discriminate.
Qed.

Theorem length_app : forall {A} (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros ? ? ?. induction l1.
  - auto.
  - simpl. auto.
Qed.

Theorem length_filter_le : forall {A} f (l : list A), length (filter f l) <= length l.
Proof.
  intros ? ? ?. induction l.
  - auto.
  - simpl. destruct (f a); simpl; lia.
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

Theorem list_in_filter : forall {A} a f (l : list A), list_in a (filter f l) <-> list_in a l /\ f a = true.
Proof.
  intros ? ? ? ?. induction l.
  - simpl. intuition auto.
  - rename a0 into b. simpl. remember (f b) as f_b. destruct f_b.
    + simpl. split.
      * intros [-> | ?].
        -- auto.
        -- intuition auto.
      * intuition auto.
    + split.
      * intuition auto.
      * intros ([-> | ?] & ?).
        -- rewrite H in Heqf_b. discriminate.
        -- intuition auto.
Qed.
