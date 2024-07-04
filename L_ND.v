Require Import Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a)(at level 11).
Notation " [ a ] " := (Singleton _ a)(at level 0).
Notation "[ ]" := (Empty_set _)(at level 15).

(*定义公式*)
Inductive Formula : Type:=
  | X (n: nat): Formula
  | Not (p : Formula): Formula
  | Contain (p q: Formula): Formula.

Notation "¬ q" := (Not q)(at level 5,right associativity).
Notation "p → q" := (Contain p q)(at level 8,right associativity).

Inductive unionset (A B: Formula -> Prop) : Formula -> Prop :=
  | union_l : forall p, A p -> (unionset A B) p
  | union_r : forall p, B p -> (unionset A B) p.
Notation " A ∪ B" := (unionset A B)(at level 70, right associativity).

(* 命题演算L系统 *)
Inductive prove_L (A: Formula -> Prop) : Formula -> Prop :=
  | L0 : forall p, A p -> prove_L A p
  | L1 : forall p q, prove_L A (p → (q → p))
  | L2 : forall p q r, prove_L A ((p → (q → r)) → ((p → q) → (p → r)))
  | L3 : forall p q, prove_L A ((¬p → ¬q)→ (q → p))
  | MP : forall p q, prove_L A (p → q) -> prove_L A p -> prove_L A q.
Notation " B ├ p " := (prove_L B p)(at level 80).
Notation " ├ p " := (prove_L (Empty_set Formula) p)(at level 80).

Theorem identity : forall A p, A ├ p → p.
Proof.
  intros.
  pose proof (L1 A p (p → p)) as H.
  pose proof (L2 A p (p → p) p) as H0.
  pose proof (MP A _ _ H0 H) as H1.
  pose proof (L1 A p p) as H2.
  pose proof (MP A _ _ H1 H2) as H3.
  apply H3.
Qed.

Lemma Union_l : forall Γ p, Γ ├ p -> forall A, Γ ∪ A ├ p.
Proof.
  intros.
  induction H.
  - pose proof (union_l Γ A p) as H0. apply H0 in H. 
    pose proof (L0 (Γ ∪ A) p) as H1. 
    apply H1 in H. apply H.
  - pose proof (L1 (Γ ∪ A) p q). auto.
  - pose proof (L2 (Γ ∪ A) p q r). auto.
  - pose proof (L3 (Γ ∪ A) p q). auto.
  - pose proof (MP (Γ ∪ A) _ _ IHprove_L1 IHprove_L2). auto.
Qed.

Lemma Union_r : forall Γ p , Γ ├ p -> forall A, A ∪ Γ ├ p.
Proof.
  intros.
  induction H.
  - pose proof (union_r A Γ p) as H0. apply H0 in H. 
    pose proof (L0 (A ∪ Γ) p) as H1. 
    apply H1 in H. apply H.
  - pose proof (L1 (A ∪ Γ) p q). auto.
  - pose proof (L2 (A ∪ Γ) p q r). auto.
  - pose proof (L3 (A ∪ Γ) p q). auto.
  - pose proof (MP (A ∪ Γ) _ _ IHprove_L1 IHprove_L2). auto.
Qed.

(*演绎定理*)
Theorem deductive : forall A p q, A ∪ [p] ├ q <-> A ├ p → q.
Proof.
  intros; split.
  - intros. induction H.
    + destruct H.
      * pose proof (L1 A p0 p) as H0.
        pose proof (L0 A p0) as H1.
        apply H1 in H.
        pose proof (MP A _ _ H0 H) as H2.
        apply H2.
      * destruct H.
        pose proof (identity A p) as H0.
        apply H0.
    + pose proof (L1 A p0 q) as H.
      pose proof (L1 A (p0 → q → p0) p) as H0.
      pose proof (MP A _ _ H0 H) as H1.
      apply H1.
    + pose proof (L2 A p0 q r) as H.
      pose proof (L1 A ((p0 → q → r) → (p0 → q) → p0 → r) p) as H0.
      pose proof (MP A _ _ H0 H) as H1.
      apply H1.
    + pose proof (L3 A p0 q) as H.
      pose proof (L1 A ((¬ p0 → ¬ q) → q → p0) p) as H0.
      pose proof (MP A _ _ H0 H) as H1.
      apply H1.
    + pose proof (L2 A p p0 q) as H1.
      pose proof (MP A _ _ H1 IHprove_L1) as H2.
      pose proof (MP A _ _ H2 IHprove_L2) as H3.
      apply H3.
  - intros. 
    pose proof (Union_l A p → q).
    specialize H0 with [p].
    apply H0 in H.
    pose proof (union_r A [p] p) as H1.
    pose proof (L0 (A ∪ [p]) p) as H2.
    apply H2 in H1.
    + pose proof (MP (A ∪ [p]) _ _ H H1). auto.
    + reflexivity.
Qed.

Theorem neg_pre : forall A p q, A ├ ¬q → (q → p).
Proof.
  intros.
  pose proof (L3  A p q) as H.
  pose proof (L1  A (¬p → ¬q)→ (q → p) ¬q) as H0.
  pose proof (MP  A _ _ H0 H) as H1.
  pose proof (L2 A ¬q (¬p → ¬q) (q → p)) as H2.
  pose proof (MP A _ _ H2 H1) as H3.
  pose proof (L1 A ¬q ¬p) as H4.
  pose proof (MP A _ _ H3 H4) as H5.
  apply H5.
Qed.

Theorem nega_posi : forall A p, A ├ (¬p → p) → p.
Proof.
  intros. apply deductive.
  set (A ∪ [¬ p → p]) as M.
  pose proof (neg_pre M ¬(¬p → p) p) as H.
  pose proof (L2 M ¬p p ¬(¬p → p)) as H0.
  pose proof (MP M _ _ H0 H) as H1.
  pose proof L0 M (¬p → p).
  assert (M ¬ p → p). { unfold M. apply union_r. reflexivity. }
  pose proof H2 H3.
  pose proof (MP M _ _ H1 H4) as H5.
  pose proof (L3 M p (¬p → p)) as H6.
  pose proof (MP M _ _ H6 H5) as H7.
  pose proof (MP M _ _ H7 H4) as H8.
  apply H8.
Qed.

Theorem contra : forall A p q, A ∪ [ ¬ p] ├ q -> A ∪ [ ¬ p] ├ ¬ q -> A ├ p.
Proof.
  intros.
  pose proof (neg_pre (A ∪ [¬ p]) p q).
  pose proof (MP (A ∪ [¬ p]) _ _ H1 H0).
  pose proof (MP (A ∪ [¬ p]) _ _ H2 H).
  apply deductive in H3.
  pose proof (nega_posi A p).
  pose proof (MP A _ _ H4 H3).
  apply H5.
Qed.

(*L_ND*)
Theorem N1 : forall Γ p, p ∈ Γ -> Γ├ p.
Proof.
  intros.
  pose proof (L0 Γ p) as H1.
  apply H1. apply H.
Qed.

Theorem N2 : forall Γ Γ1 B, (forall A, Γ1├ A -> Γ├ A)
   -> Γ1├ B -> Γ├ B.
Proof.
  intros.
  pose proof (H B) as H1.
  apply H1 in H0. apply H0.
Qed.

Theorem N3 : forall Γ A B, (Γ ∪ [¬A])├ B 
  -> (Γ  ∪ [¬A])├ ¬B -> Γ├ A.
Proof.
  intros.
  pose proof (contra Γ A B) as H1.
  apply H1 in H. apply H. apply H0.
Qed.

Theorem N4 : forall Γ A B, Γ ∪ [A → B] ∪ [A]├ B.
Proof.
  intros.
  pose proof (L0 (Γ ∪ [A → B] ∪ [A]) A) as H1.
  assert ((Γ ∪ [A → B] ∪ [A]) A).
  { right. right. reflexivity. } 
  apply H1 in H.
  pose proof (L0 (Γ ∪ [A → B] ∪ [A]) A → B) as H2.
  assert ((Γ ∪ [A → B] ∪ [A]) A → B).
  { right. left. reflexivity. }
  apply H2 in H0.
  pose proof (MP (Γ ∪ [A → B] ∪ [A]) A B H0 H) as H3.
  apply H3.
Qed.

Theorem N5 : forall Γ A B, Γ ∪ [A]├ B -> Γ├ (A → B).
Proof.
  intros.
  apply deductive. assumption.
Qed.


