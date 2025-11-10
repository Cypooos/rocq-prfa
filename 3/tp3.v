(** Exercise session 3 — Proof terms

  Once more:
  - When you see REPLACE_ME, replace it with the relevant value.
  - Try to solve the exercises without looking at the live coding
  - Exercises all start with "EXERCISE". Instructions follow the keyword.

**)

From Stdlib Require Import List.
Import ListNotations.

Set Default Goal Selector "!".

Axiom REPLACE_ME : forall {A : Type}, A.

(** EXERCISE

  Prove the following statements using proof terms.
  If it's too hard to do directly, you can use the interactive mode together
  with the [refine] tactic.

**)

Definition ex1 : forall (P Q : Prop), P -> Q -> P :=
  (fun P => fun Q => fun p => fun q => p).

Definition ex2 : forall (P Q R : Prop), P -> (P -> Q) -> (P -> Q -> R) -> R :=
  fun P Q R p f g => g p (f p).

(** We give you this type for "lower than" (lt). **)

Inductive lt (n : nat) : nat -> Prop :=
| lt_B : lt n (S n)
| lt_S m : lt n m -> lt n (S m).

(** EXERCISE

  Prove the following lemma interactively using [intros] and [apply].

**)
Lemma lt_plus_4 :
  forall n m,
    lt n m ->
    lt n (4 + m).
Proof.
intros n m h.
 repeat apply lt_S.
 apply h.
Qed.
(** EXERCISE

  Prove the following with a proof term.

**)
Definition lt_plus_4' n m : lt n m -> lt n (4 + m) :=
  fun h => lt_S n (3+m) (lt_S n (2+m) (lt_S n (1+m) (lt_S n m h))).

(** EXERCISE

  Prove the following with a proof term.
  Hint: Use [Print "\/"] if needed.

**)

Definition or_comm P Q : P \/ Q -> Q \/ P :=
  fun h => match h with or_introl p => or_intror p | or_intror q => or_introl q end.

(** EXERCISE

  Prove the following with a proof term.

**)
Definition ex3 :
  forall X (P Q : X -> Prop),
    (forall x, P x <-> Q x) ->
    (forall x, Q x) ->
    forall x, P x
:= fun X P Q eq qa x => let (_,r) := eq x in r (qa x).

(** EXERCISE

  Prove the following with a proof term.

**)
Definition Russel X : ~ (X <-> ~ X) :=
  fun h => let (x_nx,nx_x) := h in 
  (fun x => (x_nx x) x) (nx_x (fun x => (x_nx x) x)).

(** Impredicative encodings

  Thanks to impredicativity of [Prop] (the ability to quantify over
  propositions within propositions) it is possible to define most connectives
  using only [forall] and [->] (no inductive definitions).

  For instance, one can define [False] as follows:

**)

Definition iFalse := forall (P : Prop), P.

(** EXERCISE

  Show that [iFalse] is equivalent to [False].

**)
Lemma iFalse_iff : False <-> iFalse.
Proof.
  split.
   - intro h. destruct h.
   - intro h. exact (h False).
Qed.
(** EXERCISE

  Define the impredicative encoding of [True] and show it equivalent to [True].

**)


Definition iTrue : Prop := forall (P:Prop), P -> P.

Lemma iTrue_iff : True <-> iTrue.
Proof.
split.
- intros _ p h. exact h.
- intros _. exact I. 
Qed.
(** EXERCISE

  Now do the same thing for conjunction, disjunction and the existential
  quantifier.

**)

Definition iAnd (P Q : Prop) : Prop :=
 forall C, (P -> Q -> C) -> C.

Lemma iAnd_iff :
  forall P Q,
    P /\ Q <-> iAnd P Q.
Proof.
  split; intro h.
  - destruct h as [hP hQ]. intros C h. exact (h hP hQ).
  - split. 
    * apply (h P). intros p _. exact p.
    * apply (h Q). intros _ q. exact q.
Qed.

Definition iOr (P Q : Prop) : Prop :=
  forall C, (P -> C) -> (Q -> C) -> C.

Lemma iOr_iff :
  forall P Q,
    P \/ Q <-> iOr P Q.
Proof.
  split; intro h.
  - destruct h as [p | q]; intros C hP hQ.
   * exact (hP p).
   * exact (hQ q).
  - apply (h (P \/ Q)).
   * intro p. left. exact p.
   * intro q. right. exact q.  
Qed.

Definition iEx (X : Type) (P : X -> Prop) : Prop :=
  forall A, (forall x, P x -> A) -> A.

Lemma iEx_iff :
  forall X P,
    (exists (x : X), P x) <-> iEx X P.
Proof.
  split; intro h.
   - intros A H. destruct h as [x hPx]. exact (H x hPx).
   - apply (h (exists x:X, P x)). intros x hPx. exists x. exact hPx.
Qed.  


(** Advanced exercises **)

(** Mutual inductive types

  It is also possible to define several inductive types at the same time.
  You just combine them with the [with] keyword.

  This way we can define the type of trees mutually with that of forests
  (which are basically lists of trees).

**)

Inductive ntree (A : Type) :=
| nnode : A -> nforest A -> ntree A

with nforest (A : Type) :=
| nnil : nforest A
| ncons : ntree A -> nforest A -> nforest A.

(** You can then define mutual definitions over such types by using [Fixpoint]
  and the [with] keyword.
**)

Fixpoint count {A} (t : ntree A) {struct t} : nat :=
  match t with
  | nnode _ a l => 1 + count_list l
  end

with count_list {A} (l : nforest A) {struct l} : nat :=
  match l with
  | nnil _ => 0
  | ncons _ t tl => count t + count_list tl
  end.

(** EXERCISE

  Define a map function for [ntree].
  Hint: You probably will have to change [Definition] into something else.

**)

Definition ntree_map {A B} (f : A -> B) (t : ntree A) : ntree B :=
  REPLACE_ME.

(** Nested inductive types

  Finally, you can define more inductive types by using what is called nesting.
  In the type below, you define a tree as something that contains a list of
  trees.

**)

Inductive tree :=
| N (ts : list tree).

(** EXERCISE

  Can you give an element of type [tree]?

**)


Definition ex4 : tree :=
  REPLACE_ME.

Inductive All {X} (P : X -> Type) : list X -> Type :=
| All_nil : All P nil
| All_cons x l : P x -> All P l -> All P (x :: l).

Arguments All_nil {X P}.
Arguments All_cons {X P}.

Fixpoint tree_rect_strong (P : tree -> Type)
    (f : forall (ts : list tree), All P ts -> P (N ts))
    (t : tree) : P t :=
  let fix F ts : All P ts :=
    match ts with
    | [] => All_nil
    | t' :: l => All_cons _ _ (tree_rect_strong P f t') (F l)
    end
  in
  match t with
  | N ts => f ts (F ts)
  end.

(** EXERCISE

  - Extend the type [tree] to have labelled nodes.
  - Prove a bijection between the new [tree] and [ntree],
    ie. define functions
    to_tree : forall A, ntree A -> tree A
    from_tree : forall A, tree A -> ntree A
    and show that they invert each other.

**)

(** Here is the Fibonnaci function.

  Notice the [as] keyword to give a name to subexpression [S n].
  This way Coq knows that [S n] is a subterm of the one we started with.

**)

Fixpoint fib n : nat :=
  match n with
  | 0 | 1 => 1
  | S (S n as m) => fib m + fib n
  end.

(** EXERCISE

  Define the Fibonnaci function [fib] using [nat_rect] directly.

**)

(** EXERCISE

  Define it using course-of-values recursion, a form of strong induction shown
  below.
  Of course you need to prove [brec] first.

**)

Fixpoint below (P : nat -> Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S n => P n * below P n
  end.

Compute below _ 5.

Fixpoint brec' (P : nat -> Type)
  (F : forall n', below P n' -> P n') (n : nat) {struct n} : P n * below P n :=
  REPLACE_ME.

Definition brec {P : nat -> Type}
  (F : forall n, below P n -> P n) : forall n, P n :=
  REPLACE_ME.

(** Inconsistencies

  There are three crucial potential breaking points ofconsistency of type
  theory:
  - termination of recursive functions, which needs to be ensured
  - strict positivity of inductives, which you have seen in the lecture
  - having type hierarchies rather than a [Type : Type] rule

**)

Unset Guard Checking.

(** EXERCISE

  Define a function of type [nat -> nat] and use it to deduce [False].
  Note that this is surprisingly tricky.

**)

Set Guard Checking.

Unset Positivity Checking.

(** EXERCISE

  Define an inductive type [bad] such that [bad <-> ~ bad], use lemma [Russell]
  from above to derive a contradiction.

**)

Set Positivity Checking.

(** EXERCISE

  We are going to prove a theorem allowing to prove [False] from [Type : Type].
  Fill in the missing parts below.

**)

Module Hierarchy.

  Definition embeds X Y :=
    exists (E : X -> Y) (D : Y -> X),
      forall x, D (E x) = x.

  Fact embeds_refl X :
    embeds X X.
  Proof.
  Admitted.

  Definition Tyi :=
    Type.

  Inductive tree (A : Tyi) (D : A -> Tyi) : Tyi :=
  | T (a : A) (f : D a -> tree A D).

  Arguments T { _ _}.

  Definition sub {A : Tyi} {D : A -> Tyi} (s t : @tree A D) : Prop :=
    match t with
    | T a f => exists x, f x = s
    end.

  Fact sub_irrefl {A D} :
    forall s : tree A D, ~ sub s s.
  Proof.
  Admitted.

  Lemma hier A D (E : Tyi -> A) :
    ~ embeds (tree A D) (D (E (tree A D))).
  Proof.
  Admitted.

  Theorem hierarchy :
    forall (X : Tyi),
      ~ embeds Tyi X.
  Proof.
  Admitted.

  (** We now enable the [Type : Type] rule **)
  Unset Universe Checking.

  Lemma inconsistent : False.
  Proof.
    unshelve eapply hierarchy.
    - exact Tyi.
    - apply embeds_refl.
  Qed.

End Hierarchy.
