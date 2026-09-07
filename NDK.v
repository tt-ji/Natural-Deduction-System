Require Export Coq.Arith.Arith.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Vectors.Vector. 
Import VectorNotations.
Require Export Coq.Sets.Ensembles.

Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a) (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "A ~ B" := (Setminus _ A B) (at level 0, right associativity).

Corollary UnionI : forall {U} (a:U) B C, a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. split; intros; destruct H; eauto with sets. Qed.

Corollary Single : forall {U} (a x:U), a ∈ [ x ] <-> a = x.
Proof. split; intros; destruct H; auto. apply In_singleton. Qed.

Global Hint Resolve UnionI Single: sets.

(** symbols*)
(* 个体变元 *)
Inductive Var : Set :=
  | X : nat -> Var.

(* 个体常元 *)
Inductive Con : Set :=
  | C : nat -> Con.

(* 函数 *)
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.

(* 谓词 *)
Inductive Rel : Set :=
  | R : nat -> nat -> Rel.

(* 变元相关性质 *)
Definition var_num (v: Var): nat:=
  match v with
  | X n => n
  end.

(* 常元相关性质 *)
Definition con_num (v: Con): nat:=
  match v with
  | C n => n
  end.

(* 元数(arity)函数 *)
Definition arity_F (f : Fun) : nat :=
  match f with
  | F a b => S a
  end.

(* 元数(arity)谓词 *)
Definition arity_R (r : Rel) : nat :=
  match r with
  | R a b => S a
  end.

(* 项 *)
Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, Vector.t term (arity_F f) -> term.

(* 项向量 *)
Print Vector.t.
(* 
Inductive t (A : Type) : nat -> Type :=
  | nil : t A 0
  | cons : A -> forall n : nat, t A n -> t A (S n).
*)

(* 原子公式 项之间的谓词关系是原子公式*)

(* 公式 *)
Inductive Formula :=
  | atomic : forall (r: Rel), Vector.t (term) (arity_R r) -> Formula
  | Not : Formula -> Formula
  | or : Formula -> Formula -> Formula 
  | ForAll : Var -> Formula -> Formula.

Notation "¬ q" := (Not q)(at level 5, right associativity).
Notation "p ∨ q" := (or p q)(at level 11, right associativity).
Notation "∀ x , p" := (ForAll x p) (at level 7, right associativity).

(* 其他的逻辑联结词可以用 ¬ 和 ∨ 表示 *)
Notation "p ∧ q" := (¬(¬ p ∨ ¬ q))(at level 9, right associativity).
Notation "p → q" := (¬ p ∨ q)(at level 11,right associativity).
Notation "p ↔ q" := ((p → q) ∧ (q → p))(at level 12, right associativity).

(* 存在量词可以用全称量词和否定表示 *)
Definition Exists x p := Not (ForAll x (Not p)).
Notation "∃ x , p" := (Exists x p) (at level 8, right associativity).

(** 约束和自由*)
(* 空集 *)
Definition Φ := @ Empty_set Formula.

(* 变量集为空 *)
Definition Φ_Vr := @ Empty_set Var.

(* 常元集为空 *)
Definition Φ_Co := @ Empty_set Con.

(* 项的变元集T_Vr：项中无量词, 项中的变元都是自由的, 故该变元集也是自由变元集 *)
Fixpoint term_Ens (t: term) :=
  match t with
  | Tcon c => Φ_Vr
  | Tvar x => [x]
  | Tfun  _ q => let fix Vector_Ens (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => Φ_Vr
                   | cons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
                   end in Vector_Ens _ q
  end. 

(* 项向量的变元集TV_Vr，该变元集也是自由变元集 *)
Fixpoint Vector_Ens (n: nat) (r: Vector.t (term) n) :=
  match r with 
  | nil _ => Φ_Vr
  | cons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
  end.

(* 公式的变元集F_Vr *)
Fixpoint Formula_Ens (p: Formula) :=
  match p with 
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_Ens q
  | or m n =>  (Formula_Ens m) ∪ (Formula_Ens n)
  | ForAll x q => (Formula_Ens q) ∪ [x]
  end.

(* 项的常元集T_C_set *)
Fixpoint term_C_set (t: term) :=
  match t with
  | Tcon c => [c]
  | Tvar x => Φ_Co
  | Tfun  _ q => let fix Vector_C_set (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => Φ_Co 
                   | cons _ h _ q => (term_C_set h) ∪  (Vector_C_set _ q)
                   end in Vector_C_set _ q
  end.

(* 项向量的常元集TV_C_set *)
Fixpoint Vector_C_set (n: nat) (r: Vector.t (term) n) :=
  match r with 
  | nil _ => Φ_Co
  | cons _ h _ q => (term_C_set h) ∪ (Vector_C_set _ q)
  end.

(* 公式的常元集F_C_set *)
Fixpoint Formula_C_set (p: Formula) :=
  match p with 
  | atomic _ q => Vector_C_set _ q
  | Not q => Formula_C_set q
  | or m n =>  (Formula_C_set m) ∪ (Formula_C_set n)
  | ForAll x q => (Formula_C_set q) 
  end.

(* 公式的自由变元集 *)
Fixpoint Formula_free_Ens (p: Formula) :=
  match p with 
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_free_Ens q
  | or m n => (Formula_free_Ens m) ∪ (Formula_free_Ens n)
  | ForAll x q => (Formula_free_Ens q) ~ [x]
  end.

(* 公式的约束变元集 *)
Fixpoint Formula_bound_Ens (p: Formula) :=
  match p with 
  | atomic _ q => Φ_Vr
  | Not q => Formula_bound_Ens q
  | or m n => (Formula_bound_Ens m) ∪ (Formula_bound_Ens n)
  | ForAll x q => (Formula_bound_Ens q) ∪ [x]
  end.

(* 闭项: 只含个体常元的项叫做闭项，即项的变元集为空 *)
Definition closed_term (t: term) := term_Ens t = Φ_Vr.
  
(* 语句(闭式): 不含自由变元的公式，即公式的自由变元集为空 *)
Definition statement (p: Formula) := Formula_free_Ens p = Φ_Vr.

(* 项的变元和常元组成的项子集 *)
Fixpoint ST (t: term) : Ensemble term :=
  match t with
  | Tcon c => [t]
  | Tvar x => [t]
  | Tfun  _ q => let fix Vector_ST (n: nat) (r: Vector.t (term) n) :=
                   match r with 
                   | nil _ => (@ Empty_set term)
                   | cons _ h _ q => (ST h) ∪ (Vector_ST _ q)
                   end in [t] ∪ (Vector_ST _ q)
  end.

  (* 项向量的仅由变元和常元组成的子项集 *)
Fixpoint Vector_ST (n: nat) (r: Vector.t (term) n) : Ensemble term :=
   match r with 
   | nil _ => (@ Empty_set term)
   | cons _ h _ q => (ST h) ∪ (Vector_ST _ q)
   end.

(* 公式的仅由变元和常元组成的子项集 *)
Fixpoint Formula_ST (t: Formula) : Ensemble term :=
  match t with
  | atomic _ vr => (Vector_ST _ vr)
  | Not a => (Formula_ST a)
  | or a b => (Formula_ST a) ∪ (Formula_ST b)
  | ForAll x a => [(Tvar x)] ∪ (Formula_ST a)
  end.

(* 对子项集封闭的项集 *)
Definition Closed_ST (ET : Ensemble term) := forall s, s ∈ ET -> (ST s) ⊆ ET.

(* 公式的子公式集 *)
Fixpoint Formula_SF (s: Formula) : Ensemble Formula :=
  match s with
  | atomic _ _ => [s]
  | Not a => [s] ∪ (Formula_SF a)
  | or a b => [s] ∪ (Formula_SF a) ∪ (Formula_SF b)
  | ForAll x a => [s] ∪ (Formula_SF a)
  end.

(* 对子公式封闭的公式集 *)
Definition Closed_SF (S: Ensemble Formula) := forall s, s ∈ S 
  -> (Formula_SF s) ⊆ S.

(* 加强版排中律 *)
Theorem classicT : forall P, {P} + {~ P}.
Proof.
  intros. assert { x: bool | if x then P else ~ P }.
  { apply constructive_indefinite_description. destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H, x; auto.
Qed.

(* 项t对p中变元x是自由的 *)
Fixpoint t_x_free (p: Formula) (t: term) (x: Var) :=
  match p with 
  | atomic _ q => true 
  | Not q => t_x_free q t x
  | or m n => andb (t_x_free m t x) (t_x_free n t x)
  | ForAll y q => match (classicT (x ∈ (Formula_free_Ens p))) with
                  | left _ => match (classicT (y ∈ (term_Ens t))) with
                              | left _ => false
                              | right _ => t_x_free q t x
                              end
                  | right _ => true
                  end
  end.

(* 变元x不在公式集Γ的任何公式中自由出现 *)
Definition not_free_in_Ens (x: Var) (Γ: Ensemble Formula) : Prop :=
  forall A, A ∈ Γ -> ~ (x ∈ (Formula_free_Ens A)).

(** 替换的性质 *)
Definition eqbv (n m: Var) : bool :=
  match n, m with
  | X p, X q => p =? q
  end.

Lemma eqbv_eq : forall x y, eqbv x y = true <-> x = y.
Proof.
  intros [n] [m]; split; simpl.
  - intro H. apply Nat.eqb_eq in H. subst. reflexivity.
  - intro H. inversion H. apply Nat.eqb_refl.
Qed.

Lemma eqbv_refl : forall x, eqbv x x = true.
Proof.
  intros [n]. simpl. apply Nat.eqb_refl.
Qed.

Definition eqbc (n m: Con) : bool :=
  match n, m with
  | C p, C q => p =? q
  end.

(* 在项t中把变元x替换成t': t(x;t') *)
Fixpoint substitute_t (t t': term) (x: Var) :=
  match t with
  | Tcon c => Tcon c
  | Tvar y => if (eqbv x y) then t' else Tvar y 
  | Tfun  _ q => let fix substitute_v (n: nat) (r: Vector.t (term) n)
                   (t': term) (x: Var) :=
                   match r with 
                   | [] => []
                   | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x) 
                   end in (Tfun _ (substitute_v _ q t' x))
  end.
Notation " r { x ; s } ":= (substitute_t r s x)(at level 0).

(* 在项t中把常元x替换成t': tc(x;t') *)
Fixpoint substitute_tc (t t': term) (x: Con) :=
  match t with
  | Tcon c => if (eqbc x c) then t' else Tcon c
  | Tvar y => Tvar y
  | Tfun  _ q => let fix substitute_vc (n: nat) (r: Vector.t (term) n)
                   (t': term) (x: Con) :=
                   match r with 
                   | [] => []
                   | h :: q => (substitute_tc h t' x) :: (substitute_vc _ q t' x) 
                   end in (Tfun _ (substitute_vc _ q t' x))
  end.

(* 向量项替换 *)
Fixpoint substitute_v (n: nat) (r: Vector.t term n) 
  (t': term) (x: Var) :=
  match r with 
  | [] => []
  | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x)
  end.

(* 公式p中把变元x替换成t' *)
Fixpoint substitute_f (p: Formula) (t': term) (x: Var) :=
  match p with 
  | atomic _ q => atomic _ (substitute_v _ q t' x) 
  | Not q => Not (substitute_f q t' x)
  | or m n => or (substitute_f m t' x) (substitute_f n t' x)
  | ForAll y q => if (eqbv x y) then ForAll y q
                    else ForAll y (substitute_f q t' x)
  end.
Notation " p { x ;; r } ":= (substitute_f p r x)(at level 0).


(** 自然演绎系统 *)
Section Predicate_Calculus.
Inductive ND_K : Ensemble Formula -> Formula -> Prop :=
  | K1 : forall Γ A , A ∈ Γ -> ND_K Γ A
  | K2 : forall Γ Γ1 B ,(forall A, A ∈ Γ1 -> ND_K Γ A) 
           -> ND_K Γ1 B -> ND_K Γ B
  | K3 : forall Γ A B, ND_K (Γ ∪ [¬A]) B 
           -> ND_K (Γ  ∪ [¬A]) ¬B -> ND_K Γ A
  | K4l : forall Γ A B, ND_K (Γ ∪ [A ∧ B]) A
  | K4r : forall Γ A B, ND_K (Γ ∪ [A ∧ B]) B
  | K5 : forall Γ A B, ND_K (Γ ∪ [A] ∪ [B]) (A ∧ B)
  | K6 : forall Γ A B C, ND_K (Γ ∪ [A]) C -> ND_K (Γ ∪ [B]) C
           -> ND_K (Γ ∪ [A ∨ B]) C
  | K7l : forall Γ A B, ND_K (Γ ∪ [A]) (A ∨ B)
  | K7r : forall Γ A B, ND_K (Γ ∪ [A]) (B ∨ A)
  | K8 : forall Γ A B, ND_K (Γ ∪ [A → B] ∪ [A]) B
  | K9 : forall Γ A B, ND_K (Γ ∪ [A]) B -> ND_K Γ (A → B)
  | K10l : forall Γ A B, ND_K (Γ ∪ [A ↔ B] ∪ [A]) B
  | K10r : forall Γ A B, ND_K (Γ ∪ [A ↔ B] ∪ [B]) A
  | K11 : forall Γ A B, ND_K (Γ ∪ [A]) B -> ND_K (Γ ∪ [B]) A
            -> ND_K Γ (A ↔ B)
  | K12 : forall Γ A x a, t_x_free A a x = true 
            -> ND_K Γ ((∀ x , A) → (substitute_f A a x))
  | K13 : forall Γ A x, not_free_in_Ens x Γ -> ND_K Γ A
            -> ND_K Γ (∀ x , A)
  | K14 : forall Γ A B x, ~(x ∈ (Formula_free_Ens B))
            -> not_free_in_Ens x Γ -> ND_K (Γ ∪ [A]) B
            -> ND_K (Γ ∪ [∃ x , A]) B
  | K15 : forall Γ A x a, t_x_free A a x = true
            -> ND_K Γ ((substitute_f A a x) → (∃ x , A)).
Notation "Γ ├ A" := (ND_K Γ A)(at level 14).

(** 定理6.2.1：∀xA ⊢ ∀y,A{x;y}，其中y不在A中自由出现且项(Tvar y)对x可代入 *)
Theorem ND_K_1 : forall Γ A x y, ~ (y ∈ (Formula_free_Ens A)) 
  -> t_x_free A (Tvar y) x = true -> not_free_in_Ens y Γ 
  -> (Γ ∪ [∀ x , A]) ├ (∀ y , A {x ;; Tvar y}).
Proof.
  intros Γ A x y Hnotfree Hfree HnotfreeG.
  set (Δ := Γ ∪ [∀ x , A]).
  pose proof (K12 Δ A x (Tvar y) Hfree) as H_impl.
  assert (H_in : ∀ x , A ∈ Δ).
  { unfold Δ. apply UnionI. right. apply In_singleton. }
  pose proof (K1 Δ (∀ x , A) H_in) as H_all.
  pose proof (K8 Δ (∀ x , A) (A {x ;; Tvar y})) as H_mp.
  assert (H_prem : forall C,
    C ∈ (Δ ∪ [(∀ x , A) → (A {x ;; Tvar y})] ∪ [∀ x , A]) -> Δ ├ C).
  { intros C HC. apply UnionI in HC. destruct HC as [HC | HC].
    - apply UnionI in HC. destruct HC as [HC | HC].
      + apply K1. assumption.
      + apply Single in HC. subst C. exact H_impl.
    - apply Single in HC. subst C. apply H_all. }
  pose proof (K2 Δ (Δ ∪ [(∀ x , A) → (A {x ;; Tvar y})] ∪ [∀ x , A])
               (A {x ;; Tvar y}) H_prem H_mp) as H_Axy.
  assert (H_nfΔ : not_free_in_Ens y Δ).
  { unfold not_free_in_Ens, Δ. intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply HnotfreeG. assumption.
    - apply Single in HC. subst C.
      unfold Formula_free_Ens.
      intro H. destruct H as [Hy _].
      exact (Hnotfree Hy). }
  pose proof (K13 Δ (A {x ;; Tvar y}) y H_nfΔ H_Axy) as H_final.
  unfold Δ in H_final. exact H_final.
Qed.

(** 辅助引理: 项代入恒等 t{x;;Tvar x} = t *)
Lemma substitute_t_id : forall t x, substitute_t t (Tvar x) x = t.
Proof.
  refine (fix rec t x := _).
  destruct t as [v0 | | f v0]; simpl; auto.
  - destruct (eqbv x v0) eqn:Heq.
    + apply eqbv_eq in Heq. subst. reflexivity.
    + reflexivity.
  - f_equal. induction v0; simpl; auto.
    f_equal; induction v0. apply rec. apply rec.
    auto. apply IHv0.
Qed.

(** 辅助引理: 向量代入恒等 *)
Lemma substitute_v_id : forall n (v: Vector.t term n) x,
  substitute_v n v (Tvar x) x = v.
Proof.
  induction v.
  - simpl. auto.
  - simpl. intro. rewrite IHv. f_equal. apply substitute_t_id.
Qed.

(** 辅助引理: 公式代入恒等 A{x;;Tvar x} = A *)
Lemma substitute_f_id : forall A x, substitute_f A (Tvar x) x = A.
Proof.
  induction A; simpl; auto;intro.
  - f_equal. apply substitute_v_id.
  - rewrite IHA. reflexivity.
  - rewrite IHA1, IHA2. reflexivity.
  - destruct (eqbv x v) eqn:Heq.
    + apply eqbv_eq in Heq. subst. reflexivity.
    + rewrite IHA. reflexivity.
Qed.

(** 辅助引理: 变元对自身总是可代入的 t_x_free A (Tvar x) x = true *)
Lemma t_x_free_self : forall A x, t_x_free A (Tvar x) x = true.
Proof.
  intros. induction A; simpl; auto. 
  - rewrite IHA1, IHA2. reflexivity.
  - destruct (classicT (x ∈ (Setminus Var (Formula_free_Ens A) [v]))) as [Hin | Hnotin].
    + destruct (classicT (v ∈ [x])) as [Hin' | Hnotin'].
      * simpl in Hin'. apply Single in Hin'. subst v. destruct Hin. destruct H0. apply In_singleton.      
      * apply IHA.
    + reflexivity.
Qed.

(** 定理6.2.2：∃ x, (∀ y, A) ⊢ (∀ y, (∃ x, A)) *)
Theorem ND_K_2 : forall Γ A x y, not_free_in_Ens x Γ ->
  not_free_in_Ens y Γ -> (Γ ∪ [∃ x, (∀ y , A)]) ├ (∀ y, (∃ x, A)).
Proof.
  intros Γ A x y Hx Hfx.
  assert (H_all_y : (Γ ∪ [∀ y, A]) ├ (∀ y, A)).
  { apply K1. apply UnionI. right. apply In_singleton. }
  assert (H_impl_1 : (Γ ∪ [∀ y, A]) ├ ((∀ y, A) → A)).
  { pose proof (K12 (Γ ∪ [∀ y, A]) A y (Tvar y) (t_x_free_self A y)).
    rewrite (substitute_f_id A y) in H. exact H. }
  pose proof (K8 (Γ ∪ [∀ y, A]) (∀ y, A) A) as H_K8.
  assert (H_prem1 : forall C, C ∈ ((Γ ∪ [∀ y, A]) ∪ [(∀ y, A) → A] ∪ [∀ y, A])
    -> (Γ ∪ [∀ y, A]) ├ C).
  { intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply UnionI in HC. destruct HC as [HC | HC].
      + apply UnionI in HC. destruct HC as [HC | HC].
        * apply K1. left. assumption.
        * apply Single in HC. subst C. apply H_all_y.
      + apply Single in HC. subst C. exact H_impl_1.
    - apply Single in HC. subst C. apply H_all_y. }
  pose proof (K2 (Γ ∪ [∀ y, A])
    ((Γ ∪ [∀ y, A]) ∪ [(∀ y, A) → A] ∪ [∀ y, A]) A H_prem1 H_K8) as H_A.
  assert (H_impl_2 : (Γ ∪ [∀ y, A]) ├ (A → (∃ x, A))).
  { pose proof (K15 (Γ ∪ [∀ y, A]) A x (Tvar x) (t_x_free_self A x)).
    rewrite (substitute_f_id A x) in H. exact H. }
  pose proof (K8 (Γ ∪ [∀ y, A]) A (∃ x, A)) as H_K8_2.
  assert (H_prem2 : forall C, C ∈ ((Γ ∪ [∀ y, A]) ∪ [A → (∃ x, A)] ∪ [A])
    -> (Γ ∪ [∀ y, A]) ├ C).
  { intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply UnionI in HC. destruct HC as [HC | HC].
      + apply UnionI in HC. destruct HC as [HC | HC].
        * apply K1. left. assumption.
        * apply Single in HC. subst C. apply H_all_y.
      + apply Single in HC. subst C. exact H_impl_2.
    - apply Single in HC. subst C. exact H_A. }
  pose proof (K2 (Γ ∪ [∀ y, A])
    ((Γ ∪ [∀ y, A]) ∪ [A → (∃ x, A)] ∪ [A]) (∃ x, A) H_prem2 H_K8_2) as H_exists.
  assert (H_nf_y : not_free_in_Ens y (Γ ∪ [∀ y, A])).
  { unfold not_free_in_Ens. intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply Hfx. assumption.
    - apply Single in HC. subst C.
      unfold Formula_free_Ens.
      intro H. inversion H. destruct H1. apply In_singleton. }
  pose proof (K13 (Γ ∪ [∀ y, A]) (∃ x, A) y H_nf_y H_exists) as H_forall.
  assert (H_x_nf : ~ (x ∈ (Formula_free_Ens (∀ y, (∃ x, A))))).
  { unfold Formula_free_Ens.
    intro H. inversion H. destruct H0. destruct H2. apply In_singleton. }
  pose proof (K14 Γ (∀ y, A) (∀ y, (∃ x, A)) x H_x_nf Hx H_forall) as H_final.
  exact H_final.
Qed.

(** MP规则: 从 Γ ├ P → Q 和 Γ ├ P 推出 Γ ├ Q *)
Lemma apply_MP : forall Γ P Q, Γ ├ (P → Q) -> Γ ├ P -> Γ ├ Q.
Proof.
  intros Γ P Q H_impl H_P.
  pose proof (K8 Γ P Q) as H_K8.
  assert (H_prem : forall C, C ∈ (Γ ∪ [P → Q] ∪ [P]) -> Γ ├ C).
  { intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply UnionI in HC. destruct HC as [HC | HC].
      + apply K1. assumption.
      + apply Single in HC. subst C. exact H_impl.
    - apply Single in HC. subst C. exact H_P. }
  apply (K2 Γ (Γ ∪ [P → Q] ∪ [P]) Q H_prem H_K8).
Qed.

(** 双重否定消去: Γ ∪ [¬¬P] ├ P *)
Lemma double_neg_elim : forall Γ P, (Γ ∪ [¬ ¬ P]) ├ P.
Proof.
  intros Γ P.
  assert (H1 : ((Γ ∪ [¬ ¬ P]) ∪ [¬ P]) ├ ¬ P).
  { apply K1. apply UnionI. right. apply In_singleton. }
  assert (H2 : ((Γ ∪ [¬ ¬ P]) ∪ [¬ P]) ├ ¬ ¬ P).
  { apply K1. apply UnionI. left. apply UnionI. right. apply In_singleton. }
  apply (K3 (Γ ∪ [¬ ¬ P]) P (¬ P) H1 H2).
Qed.

(** 定理6.2.3a: (∀x)A ⊢ ¬(∃x)¬A *)
Theorem ND_K_3a : forall Γ A x,
  not_free_in_Ens x Γ ->
  (Γ ∪ [∀ x, A]) ├ ¬(∃ x, ¬ A).
Proof.
  intros Γ A x Hnf.
  set (Γ' := Γ ∪ [∀ x, A]).
  assert (H_nf_Γ' : not_free_in_Ens x Γ').
  { unfold not_free_in_Ens, Γ'. intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply Hnf. assumption.
    - apply Single in HC. subst C.
      unfold Formula_free_Ens. cbn.
      unfold Formula_free_Ens.
      intro H. inversion H. destruct H1. apply In_singleton. }
  assert (H_K12 : (Γ' ∪ [¬ A]) ├ ((∀ x, A) → A)).
  { pose proof (K12 (Γ' ∪ [¬ A]) A x (Tvar x) (t_x_free_self A x)).
    rewrite (substitute_f_id A x) in H. exact H. }
  assert (H_all : (Γ' ∪ [¬ A]) ├ (∀ x, A)).
  { apply K1. unfold Γ'. apply UnionI. left. apply UnionI. right. apply In_singleton. }
  assert (H_A : (Γ' ∪ [¬ A]) ├ A).
  { apply (apply_MP (Γ' ∪ [¬ A]) (∀ x, A) A H_K12 H_all). }
  assert (H_inner_K3 : (Γ' ∪ [¬ A]) ├ ¬(∃ x, ¬ A)).
  { apply (K3 (Γ' ∪ [¬ A]) (¬(∃ x, ¬ A)) A).
    - assert (H_K12' : ((Γ' ∪ [¬ A]) ∪ [¬ ¬ (∃ x, ¬ A)]) ├ ((∀ x, A) → A)).
      { pose proof (K12 ((Γ' ∪ [¬ A]) ∪ [¬ ¬ (∃ x, ¬ A)]) A x (Tvar x) (t_x_free_self A x)).
        rewrite (substitute_f_id A x) in H. exact H. }
      assert (H_all' : ((Γ' ∪ [¬ A]) ∪ [¬ ¬ (∃ x, ¬ A)]) ├ (∀ x, A)).
      { apply K1. apply UnionI. left.
        unfold Γ'. apply UnionI. left. apply UnionI. right. apply In_singleton. }
      apply (apply_MP ((Γ' ∪ [¬ A]) ∪ [¬ ¬ (∃ x, ¬ A)]) (∀ x, A) A H_K12' H_all').
    - apply K1. apply UnionI. left. apply UnionI. right. apply In_singleton. }
  assert (H_x_nf : ~ (x ∈ (Formula_free_Ens (¬(∃ x, ¬ A))))).
  { unfold Formula_free_Ens. cbn.
    intro H. inversion H. destruct H1. apply In_singleton. }
  pose proof (K14 Γ' (¬ A) (¬(∃ x, ¬ A)) x H_x_nf H_nf_Γ' H_inner_K3) as H_K14.
  pose proof (double_neg_elim Γ' (∃ x, ¬ A)) as H_DNE.
  assert (H_lift : (Γ' ∪ [¬ ¬ (∃ x, ¬ A)]) ├ ¬(∃ x, ¬ A)).
  { apply (K2 (Γ' ∪ [¬ ¬ (∃ x, ¬ A)]) (Γ' ∪ [∃ x, ¬ A]) (¬(∃ x, ¬ A))).
    - intros C HC. apply UnionI in HC. destruct HC as [HC | HC].
      + apply K1. apply UnionI. left. assumption.
      + apply Single in HC. subst C. exact H_DNE.
    - exact H_K14. }
  apply (K3 Γ' (¬(∃ x, ¬ A)) (∃ x, ¬ A) H_DNE H_lift).
Qed.

(** 定理6.2.3b: ¬(∃x)¬A ⊢ (∀x)A *)
Theorem ND_K_3b : forall Γ A x,
  not_free_in_Ens x Γ ->
  (Γ ∪ [¬(∃ x, ¬ A)]) ├ (∀ x, A).
Proof.
  intros Γ A x Hnf.
  set (Γ' := Γ ∪ [¬(∃ x, ¬ A)]).
  assert (H_nf_Γ' : not_free_in_Ens x Γ').
  { unfold not_free_in_Ens, Γ'. intros C HC.
    apply UnionI in HC. destruct HC as [HC | HC].
    - apply Hnf. assumption.
    - apply Single in HC. subst C.
      unfold Formula_free_Ens. cbn.
      unfold Formula_free_Ens.
      intro H. inversion H. destruct H1. apply In_singleton. }
  assert (H_A : Γ' ├ A).
  { assert (H_K15 : (Γ' ∪ [¬ A]) ├ ((¬ A) → (∃ x, ¬ A))).
    { pose proof (K15 (Γ' ∪ [¬ A]) (¬ A) x (Tvar x) (t_x_free_self (¬ A) x)).
      rewrite (substitute_f_id (¬ A) x) in H. exact H. }
    assert (H_notA : (Γ' ∪ [¬ A]) ├ ¬ A).
    { apply K1. apply UnionI. right. apply In_singleton. }
    assert (H_exists : (Γ' ∪ [¬ A]) ├ (∃ x, ¬ A)).
    { apply (apply_MP (Γ' ∪ [¬ A]) (¬ A) (∃ x, ¬ A) H_K15 H_notA). }
    assert (H_not_exists : (Γ' ∪ [¬ A]) ├ ¬(∃ x, ¬ A)).
    { apply K1. unfold Γ'. apply UnionI. left. apply UnionI. right. apply In_singleton. }
    apply (K3 Γ' A (∃ x, ¬ A) H_exists H_not_exists). }
  apply (K13 Γ' A x H_nf_Γ' H_A).
Qed.

(** 同一律: Γ ├ A → A *)
Theorem identity_law : forall Γ A, Γ ├ (A → A).
Proof.
  intros Γ A. apply K9. apply K1.
  apply UnionI. right. apply In_singleton.
Qed.

(** 否定前件律: Γ ├ ¬A → (A → B) *)
Theorem neg_antecedent_law : forall Γ A B, Γ ├ (¬A → (A → B)).
Proof.
  intros Γ A B. apply K9. apply K9.
  apply (K3 (Γ ∪ [¬A] ∪ [A]) B A).
  - apply K1. apply UnionI. left. apply UnionI. 
    right. apply In_singleton.
  - apply K1. apply UnionI. left. apply UnionI. left. 
    apply UnionI. right. apply In_singleton.
Qed.

(** 否定肯定律: (¬A → A) → A *)
Theorem neg_affirm_law : forall Γ A, Γ ├ ((¬A → A) → A).
Proof.
  intros Γ A. apply K9.
  set (Δ := Γ ∪ [¬A → A]). apply (K3 Δ A A).
  - apply (apply_MP (Δ ∪ [¬A]) (¬A) A).
    + apply K1. unfold Δ.
      apply UnionI. left. apply UnionI. right. apply In_singleton.
    + apply K1. apply UnionI. right. apply In_singleton.
  - apply K1. apply UnionI. right. apply In_singleton.
Qed.
End Predicate_Calculus.

