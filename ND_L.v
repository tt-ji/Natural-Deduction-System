Require Import Coq.Sets.Ensembles.
(* 
Require Import base_pc.
Require Import formulas.
Require Import syntax.
 *)
Notation "a ∈ A" := (In _ A a)(at level 11).
Notation " [ a ] " := (Singleton _ a)(at level 0).
Notation "A ∪ B" := (Union _ A B)(at level 10).
Notation "[ ]" := (Empty_set _)(at level 15).
Notation "A ⊆ B" := (Included _ A B)(at level 13).

Inductive Formula : Type:=
  | X : nat -> Formula
  | Not : Formula -> Formula
  | Or : Formula -> Formula -> Formula.

Notation "¬ a" := (Not a)(at level 5,right associativity).
Notation "a ∨ b" := (Or a b)(at level 6,right associativity).
Notation "a → b" := (¬ a ∨ b)(at level 8,right associativity).


(*Notation "a ∧ b" := (¬(¬ a ∨ ¬ b))(at level 7, right associativity).
Notation "a ↔ b" := ((a → b) ∧ (b → a))(at level 9, right associativity).*)



Inductive prove_ND : Ensemble Formula -> Formula -> Prop :=
  | N1 : forall Γ A , A ∈ Γ -> prove_ND Γ A
  | N2 : forall Γ Γ1 B ,(forall A, A ∈ Γ1 -> prove_ND Γ A) 
           -> prove_ND Γ1 B -> prove_ND Γ B
  | N3 : forall Γ A B, prove_ND (Γ ∪ [¬A]) B 
           -> prove_ND (Γ  ∪ [¬A]) ¬B -> prove_ND Γ A
  | N4 : forall Γ A B, prove_ND (Γ ∪ [A → B] ∪ [A]) B
  | N5 : forall Γ A B, prove_ND (Γ ∪ [A])  B -> prove_ND Γ (A → B).

Notation "Γ ├N A" := (prove_ND Γ A)(at level 14).
Notation "├N A" := (prove_ND (Empty_set Formula) A)(at level 15).


(*三段论，对应书上定理3.5.1*)
Theorem I : forall A B C,   [A → B] ∪ [B → C] ├N A → C.
Proof.
  intros. 
  pose proof (N1 ([A → B] ∪ [B → C] ∪ [A]) (A → B)) as H0. 
  assert (A → B ∈ ([A → B] ∪ [B → C]) ∪ [A] ).
  { left. left. reflexivity. } apply H0 in H. 
  pose proof (N1 ([A → B] ∪ [B → C] ∪ [A])  A) as H1.
  assert (A ∈ ([A → B] ∪ [B → C]) ∪ [A] ).
  { right. reflexivity. }  apply H1 in H2.
  pose proof (N4 ([ ]) A B) as H3.
  pose proof (N2 ([A → B] ∪ [B → C] ∪ [A]) ((([ ]) ∪ [A → B]) ∪ [A]) B ) 
    as H4. 
  assert (forall A0 : Formula, A0 ∈ (([ ]) ∪ [A → B]) ∪ [A] 
    -> ([A → B] ∪ [B → C]) ∪ [A] ├N A0).
  { intros. destruct H5. 
    - apply N1. left. left. destruct H5. inversion H5. apply H5.
    - apply N1. right. apply H5.
  }
  apply H4 in H5.
  clear H0 H H1 H2 H3 H4.
  pose proof (N1 ([A → B] ∪ [B → C] ∪ [B]) (B → C)) as H0.
  assert (B → C ∈ ([A → B] ∪ [B → C]) ∪ [B] ).
  { left. right. reflexivity. } apply H0 in H.
  pose proof (N4 ([ ]) B C) as H1.
  pose proof (N2 ([A → B] ∪ [B → C] ∪ [B]) ((([ ]) ∪ [B → C]) ∪ [B]) C) 
    as H2.
  assert (forall A0 : Formula, A0 ∈ (([ ]) ∪ [B → C]) ∪ [B] ->
  ([A → B] ∪ [B → C]) ∪ [B] ├N A0).
  { intros. destruct H3.
    - apply N1. left. right. destruct H3. inversion H3. apply H3.
    - apply N1. right. assumption.
  }
  apply H2 in H3.
  clear H0 H H1 H2.
  pose proof (N5 ([A → B] ∪ [B → C]) A C) as H.
  assert (([A → B] ∪ [B → C]) ∪ [A] ├N C).
  { apply N2 with (Γ1 := [A → B] ∪ [B → C] ∪ [B]).
    - intros A0 H0. destruct H0.
      + apply N1. left. apply H0.
      + inversion H0. rewrite H0 in *. apply H5.
    - apply H3.
  }
  apply H in H0. apply H0. 
  apply N4. apply N4.
Qed.

(*========================================================*)
(*N_L*)
Fact equal_MP : forall Γ p q, Γ├N p → q -> Γ├N p ->  Γ├N q.
Proof.
  intros. 
  pose proof (N4 Γ p q) as H1.
  pose proof (N2 Γ ((Γ ∪ [p → q]) ∪ [p]) q) as H2.
  assert (forall A : Formula,
      A ∈ (Γ ∪ [p → q]) ∪ [p] -> Γ ├N A).
  { intros. inversion H3.
     - inversion H4. apply N1. apply H6. apply N1 in H6. 
       pose proof (N2 Γ [p → q]  A) as H8.
       assert (forall A : Formula, A ∈ [p → q] -> Γ ├N A).
       { intros. inversion H9. apply H.  }
       apply H8 in H9. apply H9. apply H6.
    - pose proof (N2 Γ [p] A) as H6.
      assert (forall A : Formula, A ∈ [p] -> Γ ├N A).
      { intros. inversion H7. rewrite <- H8. apply H0. }
      apply H6 in H7. assumption. apply H6 in H7;
      apply N1; apply H4. }
  apply H2 in H3. apply H3.
  apply H2 in H3; apply H1.
Qed.

Fact L0 : forall Γ p, p ∈ Γ -> Γ├N p.
Proof.
  intros. apply N1. apply H.
Qed.

Fact L1 : forall p q, ├N p → (q → p).
Proof.
  intros. repeat apply N5. apply N1.
  left. right. apply In_singleton.
Qed.

Fact L2 : forall p q r, ├N (p → (q → r) )→( (p → q) → (p → r)).
Proof.
  intros.
  apply N5. apply N5. apply N5.
  set (((([ ]) ∪ [p → q → r]) ∪ [p → q]) ∪ [p] ) as M1.
  pose proof (N4 ([ ]) p (q → r)) as H1. 
  set ((([ ]) ∪ [p → q → r]) ∪ [p] ) as M2.
  pose proof (N2 M1 M2 (q → r)).
  assert (forall A : Formula, A ∈ M2 -> M1 ├N A).
  { intros. destruct H0.
    - apply N1. unfold M1. left. left. apply H0.
    - apply N1. unfold M1. right. apply H0. }
  apply H in H0. 
  pose proof (N4 ([ ]) p q) as H2.
  set ((([ ]) ∪ [p → q]) ∪ [p] ) as M3.
  pose proof (N2 M1 M3 q) as H3.
  assert (forall A : Formula, A ∈ M3 -> M1 ├N A).
  { intros. destruct H4.
     - apply N1. unfold M1. left. right.
        assert (([ ]) ∪ [p → q] = [p → q]).
        { apply Extensionality_Ensembles. 
  unfold Same_set. split.
  - unfold Included. intros. inversion H5.
    -- destruct H6.
    -- apply H6.
  - unfold Included. apply Union_intror. }
  rewrite H5 in H4. apply H4. 
  - apply N1. unfold M1. right. apply H4. }
  apply H3 in H4. apply (equal_MP M1 q r).
  apply H0. apply H4. apply H2. apply H1.
Qed.

Fact L3 : forall p q, ├N (¬ p → ¬ q) → (q → p).
Proof.
  intros. repeat apply N5.
  set ((([ ]) ∪ [¬ p → ¬ q]) ∪ [q] ) as M.
  pose proof (N1 (M ∪ [¬p]) ¬p) as H.
  assert (¬p ∈ M ∪ [¬p]).
  { right. apply In_singleton. }
  apply H in H0.
  pose proof (N1 (M ∪ [¬p]) (¬ p → ¬ q)) as H1.
  assert (¬ p → ¬ q ∈ M ∪ [¬ p]).
  { unfold M. left. left. right. apply In_singleton. }
  apply H1 in H2.
  pose proof (N4 ([ ]) ¬ p ¬ q) as H3.
  pose proof (N2 (([ ]) ∪ [¬ p → ¬ q] ∪ [q] ∪ [¬ p]) 
    ((([ ]) ∪ [¬ p → ¬ q]) ∪ [¬ p]) ¬ q) as H4.
  assert (forall A : Formula,
      A ∈ (([ ]) ∪ [¬ p → ¬ q]) ∪ [¬ p] ->
      ((([ ]) ∪ [¬ p → ¬ q]) ∪ [q]) ∪ [¬ p] ├N A).
  { intros. apply N1. destruct H5.
     -  left. left. apply H5.
     - right. apply H5. }
  apply H4 in H5. clear H H1 H4.
  pose proof (N1 (((([ ]) ∪ [¬ p → ¬ q]) ∪ [q] ∪ [¬ p]))  q) as H6.
  assert (q ∈ ((([ ]) ∪ [¬ p → ¬ q]) ∪ [q]) ∪ [¬ p]).
   { left. right. apply In_singleton. } apply H6 in H. clear H6.
  pose proof (N3 M p q) as H6. apply H6 in H. apply H.
  apply H5. apply H3.
Qed.

(* 
Fact L_to_N:forallΓp,Γ⊢p->Γ⊢Np.
Proof.
intros. induction H.
- apply N_L0; auto.
- apply N_L1.
- apply N_L2.
- apply N_L3.
- apply N_MP with p; auto.
Qed.
 *)
(*========================================================*)
(*L系统中其他定理证明*)
(*双重否定律*)
Corollary dnl : forall p, [¬¬p]├N p.
Proof.
  intros.
  assert ([¬ ¬ p] ∪ [¬ p] ├N ¬ p) as H1.
  { apply N1. right. apply In_singleton. }
  assert ([¬ ¬ p] ∪ [¬ p] ├N ¬¬ p) as H2.
  { apply N1. left. apply In_singleton. }
  pose proof (N3 ([¬ ¬ p] ) p ¬ p) as H3.
  apply H3 in H1. apply H1. apply H2.
Qed.

(*归谬律*)
Lemma reduction_to_absurdity : forall Γ p q, (Γ ∪ [p])├N q 
  -> (Γ ∪ [p])├N ¬ q -> Γ├N ¬ p.
Proof.
  intros.
  assert (Γ ∪ [¬ ¬ p] ├N q).
  { assert (Γ ∪ [¬ ¬ p] ∪ [p] ├N q).
     { pose proof (N2 (Γ ∪ [¬ ¬ p] ∪ [p]) (Γ ∪ [p] ) q) as H1.
         assert ((forall A : Formula,
         A ∈ Γ ∪ [p] -> (Γ ∪ [¬ ¬ p]) ∪ [p] ├N A)). 
         { intros. apply N1. inversion H2.
            - left. left. apply H3.
            - right. apply H3. }
     apply H1 in H2. apply H2. apply H. }
  apply N5 in H1. assert (Γ ∪ [¬ ¬ p] ├N p). 
  { pose proof (dnl p).
     pose proof (N2 (Γ ∪ [¬ ¬ p]) [¬ ¬ p] p) as H3.
     assert (forall A : Formula,
                  A ∈ [¬ ¬ p] -> Γ ∪ [¬ ¬ p] ├N A).
    { intros. apply N1. right. assumption. }
    apply H3 in H4. apply H4. apply H2. }
    pose proof (equal_MP (Γ ∪ [¬ ¬ p]) p q) as H3.
    apply H3 in H1. apply H1. apply H2. }
  assert (Γ ∪ [¬ ¬ p] ├N ¬ q).
  { pose proof (N2 (Γ ∪ [¬ ¬ p] ∪ [p]) (Γ ∪ [p] ) ¬ q) as H2.
     assert (forall A : Formula, A ∈ Γ ∪ [p] ->
       (Γ ∪ [¬ ¬ p]) ∪ [p] ├N A).
     { intros. inversion H3. 
        - apply N1. left. left. assumption.
        - apply N1. right. assumption. }
  apply H2 in H3. apply N5 in H3. assert (Γ ∪ [¬ ¬ p] ├N p).
  { pose proof (dnl p).
     pose proof (N2 (Γ ∪ [¬ ¬ p]) [¬ ¬ p] p) as H5.
     assert (forall A : Formula,
                  A ∈ [¬ ¬ p] -> Γ ∪ [¬ ¬ p] ├N A).
    { intros. apply N1. right. assumption. }
    apply H5 in H6. apply H6. apply H4. } 
  pose proof (equal_MP (Γ ∪ [¬ ¬ p]) p ¬ q) as H5.
  apply H5 in H3. apply H3. apply H4. apply H2 in H3. apply H0. apply H0.
 }
  pose proof (N3 Γ ¬ p q) as H3.
  apply H3 in H1. apply H1. apply H2.
Qed.

Corollary dnl' : forall p, [p]├N ¬¬p.
Proof.
  intros.
  assert ([p] ∪ [¬ p]├N p) as H1.
  { apply N1. left. apply In_singleton. }
  assert ([p] ∪ [¬ p]├N ¬ p) as H2.
  { apply N1. right. apply In_singleton. }
  pose proof (reduction_to_absurdity [p] ¬ p p) as H3.
  apply H3 in H1. apply H1. apply H2.
Qed.

Lemma equal : forall {U} (Γ : Ensemble U), ([ ]) ∪ Γ = Γ.
Proof.
  intros. apply Extensionality_Ensembles. 
  unfold Same_set. split.
  - unfold Included. intros. inversion H.
    -- destruct H0.
    -- apply H0.
  - unfold Included. apply Union_intror.
Qed.

Corollary dnl1 : forall p, ├N ¬¬p → p.
Proof. intros. apply N5. rewrite equal. apply dnl. Qed.

Corollary dnl1' : forall p, ├N p → ¬¬p.
Proof. intros. apply N5. rewrite equal. apply dnl'. Qed.

Fact Union_l : forall Γ p, Γ├N p -> forall A, Γ ∪ A├N p.
Proof.
  intros. 
  pose proof (N2 (Γ ∪ A) Γ p) as H1.
  assert (forall A0 : Formula, A0 ∈ Γ -> Γ ∪ A ├N A0).
  { intros. apply N1. left. assumption. } apply H1 in H0.
  apply H0. apply H.
Qed.

Fact Union_r : forall Γ p, Γ├N p -> forall A, A ∪ Γ├N p.
Proof.
  intros.
  pose proof (N2 (A ∪ Γ) Γ p) as H1.
  assert (forall A0 : Formula, A0 ∈ Γ -> A ∪ Γ ├N A0).
  { intros. apply N1. right. auto. } apply H1 in H0; auto.
Qed.

(*否定前件律，对应书上习题3-3(1)*)
Theorem II : forall A B, [¬A] ├N A → B.
Proof.
  intros. apply N5.
  pose proof (N1 ([¬A] ∪ [A] ∪ [¬B]) ¬A).
  assert (¬ A ∈ ([¬ A] ∪ [A]) ∪ [¬ B]).
  { left. left. reflexivity. } apply H in H0.
  pose proof (N1 ([¬A] ∪ [A] ∪ [¬B]) A).
  assert (A ∈ ([¬ A] ∪ [A]) ∪ [¬ B]).
  { left. right. reflexivity. } apply H1 in H2. 
  pose proof (N3 _ _ _ H2 H0). apply H3.
Qed.

Theorem II' : forall Γ A B, Γ ∪ [¬A] ├N A → B.
Proof.
  intros. apply N5.
  pose proof (N1 (Γ ∪[¬A] ∪ [A] ∪ [¬B]) ¬A).
  assert (¬ A ∈ ((Γ ∪ [¬ A]) ∪ [A]) ∪ [¬ B]).
  { left. left. right. apply In_singleton. }
  apply H in H0.
  pose proof (N1 (Γ ∪[¬A] ∪ [A] ∪ [¬B]) A).
  assert (A ∈ ((Γ ∪ [¬ A]) ∪ [A]) ∪ [¬ B]).
  { left. right. apply In_singleton. }
  apply H1 in H2. pose proof (N3 _ _ _ H2 H0). 
  apply H3.
Qed.

Theorem II'' : forall Γ A B, Γ├N ¬A →A → B.
Proof.
  intros. apply N5. apply II'.
Qed.

(*对应书上习题3-3(2)*)
Theorem III : forall  A B, [A → B] ∪ [¬B] ├N ¬A.
Proof.
  intros.
  pose proof (N1 ([A → B] ∪ [¬B] ∪ [A]) A) as H.
  assert (A ∈ ([A → B] ∪ [¬ B]) ∪ [A] ).
  { right. reflexivity. } apply H in H0.
  pose proof (N1 (([A → B] ∪ [¬B] ∪ [A]) ) A → B ) as H1.
  assert (A → B ∈ ([A → B] ∪ [¬ B]) ∪ [A] ).
  { left. left. reflexivity. } apply H1 in H2.
  pose proof (N4 ([ ]) A B) as H3.
  pose proof (N2 ( ([A → B] ∪ [¬ B]) ∪ [A] ) (([ ]) ∪ [A → B] ∪ [A]) B  )
    as H4. 
  assert (forall A0 : Formula, A0 ∈ (([ ]) ∪ [A → B]) ∪ [A] 
    -> ([A → B] ∪ [¬ B]) ∪ [A] ├N A0).
  { intros A0 H5. apply N1. destruct H5.
    - destruct H5. inversion H5. left. left. assumption.
    - right. apply H5.
   } apply H4 in H5; try apply H3.
  clear H H1 H3 H4.
  pose proof (N1 ([A → B] ∪ [¬B] ∪ [A]) ¬B) as H6.
  assert (¬ B ∈ ([A → B] ∪ [¬ B]) ∪ [A]).
  { left. right. reflexivity. } apply H6 in H. clear H6.
  pose proof (reduction_to_absurdity ([A → B] ∪ [¬ B]) A B H5 H).
  apply H1.
Qed.

(*对应书上习题3-3(3)*)
Theorem IV : forall A B, [A → B] ∪ [A → ¬ B]├N ¬ A.
Proof.
  intros.
  pose proof (N1 ([A → B] ∪ [A → ¬ B] ∪ [A]) (A → B)) as H0.
  assert (A → B ∈ ([A → B] ∪ [A → ¬ B]) ∪ [A]).
  { left. left. reflexivity. } apply H0 in H. clear H0.
  pose proof (N1 ([A → B] ∪ [A → ¬ B] ∪ [A]) A) as H0.
  assert (A ∈ ([A → B] ∪ [A → ¬ B]) ∪ [A]).
  { right. reflexivity. } apply H0 in H1. clear H0.
  pose proof (N4 ([ ]) A B) as H2.
  pose proof (N2 ([A → B] ∪ [A → ¬ B] ∪ [A]) (([ ]) ∪ [A → B] ∪ [A]) B)
    as H3.
  assert (forall A0 : Formula, A0 ∈ (([ ]) ∪ [A → B]) ∪ [A] 
     -> ([A → B] ∪ [A → ¬ B]) ∪ [A] ├N A0).
  { intros A0 H4. apply N1. destruct H4.
    - destruct H0. inversion H0. left. left. apply H0.
    - right. assumption.
   } apply H3 in H0. clear H3.
  pose proof (N1 ([A → B] ∪ [A → ¬ B] ∪ [A]) (A → ¬ B)) as H3.
  assert (A → ¬ B ∈ ([A → B] ∪ [A → ¬ B]) ∪ [A]).
  { left. right. reflexivity. } apply H3 in H4. clear H3.
  pose proof (N4 ([ ]) A ¬ B) as H5.
  pose proof (N2 ([A → B] ∪ [A → ¬ B] ∪ [A]) ((([ ]) ∪ [A → ¬ B]) ∪ [A]) ¬ B)
    as H6.
  assert (forall A0 : Formula, A0 ∈ (([ ]) ∪ [A → ¬ B]) ∪ [A] 
    -> ([A → B] ∪ [A → ¬ B]) ∪ [A] ├N A0).
  { intros. apply N1. destruct H3.
    - destruct H3. inversion H3. left. right. apply H3.
    - right. assumption.
  } apply H6 in H3; try apply H5. clear H6.
  pose proof (reduction_to_absurdity ([A → B] ∪ [A → ¬ B]) 
     A B H0 H3). apply H6. apply H2.
Qed.

(*对应书上习题3-3(4)*)
Theorem V : forall A B, [¬ (A → B)] ├N A.
Proof.
  intros.
  pose proof (N1 ([¬ (A → B)] ∪ [¬ A]) ¬ A) as H.
  assert (¬ A ∈ [¬ (A → B)] ∪ [¬ A]).
  { right. reflexivity. }
  assert ([¬A] ├N A → B).
  { apply II. }
  pose proof (N2 ([¬ (A → B)] ∪ [¬ A]) ([¬ A]) (A → B)) 
    as H2.
  assert (forall A0 : Formula, A0 ∈ [¬ A] 
    -> [¬ (A → B)] ∪ [¬ A] ├N A0).
  { intros A0 H3. apply N1. right. apply H3. }
  apply H2 in H3; try apply H1.
  pose proof (N1 ([¬ (A → B)] ∪ [¬ A]) (¬ (A → B))) as H4.
  assert (¬ (A → B) ∈ [¬ (A → B)] ∪ [¬ A]).
  { left. reflexivity. } apply H4 in H5.
  pose proof (N3 _ _ _ H3 H5).
  apply H6.
Qed.

(*否定肯定律*)
Lemma 否定肯定律 : forall Γ p, Γ ├N (¬p → p) → p.
Proof.
  intros. apply N5. assert (([ ]) ∪ [¬ p → p]├N p).
  { pose proof N4 ([ ]) ¬ p p. 
     assert (([ ]) ∪ [¬ p → p] ∪ [¬ p] ├N ¬ p).
     { apply N1. right. apply In_singleton. }
    pose proof (N3 (([ ]) ∪ [¬ p → p]) p p) as H1.
    apply H1 in H. apply H. apply H0. }
  pose proof (N2 (Γ ∪ [¬ p → p]) (([ ]) ∪ [¬ p → p]) p) as H1.
  assert (forall p0 : Formula, p0 ∈ (([ ]) ∪ [¬ p → p]) -> Γ ∪ [¬ p → p] ├N p0).
  { intros. inversion H0. 
     - destruct H2.
     - apply N1. right. apply H2. } apply H1 in H0.
  apply H0. apply H.
Qed.


