(** Exercise session 2 — Inductive types

  Part 1

  Similar to last week, when you see REPLACE_ME, replace it with the relevant
  value. Again try to solve the exercises without looking at the live coding
  file. Even if it seems easy when you see us doing it, it might not be so easy
  to do on your own, so try to do it!

  Exercises all start with "EXERCISE".
  When it is written before a lemma, just prove it. :)

**)

Axiom REPLACE_ME : forall {A : Type}, A.

Module define_nat.

  (* Inductive types can be defined using the Inductive keyword *)
  Inductive nat :=
  | O : nat
  | S : nat -> nat.

  (** EXERCISE

    Define addition.

  **)
  Fixpoint add (n m : nat) {struct n} : nat :=
  match n with 
    | O => m
    | S n' => S (add n' m)
  end.

  (** EXERCISE

    Define subtraction on natural numbers, truncating at 0.
    In other words, when n < m then sub n m = 0.

  **)
  Fixpoint sub (n m : nat) : nat := match n,m with 
    | _, O => n
    | O, _ => O
    | S n', S m' => sub n' m'
  end.

  (** EXERCISE

    Prove the following lemma.
    You will replace Admitted with Qed once it is done.
    What Admitted does should be obvious: it admits a lemma without proof or
    with a partial proof, it can be used in subsequent proofs as if it were
    proven.

  **)
  Lemma add_0 :
    forall n,
      add n O = n.
  Proof.
    induction n as [|n IHn]. 1:reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  (** EXERCISE **)
  Lemma add_S :
    forall n m,
      add n (S m) = S (add n m).
  Proof.
    intros n m. induction n as [|n IHn]. 1:reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  (** With the following commands we declare notations for add and sub. **)
  Infix "+" := add.
  Infix "-" := sub.

  (** EXERCISE **)
  Lemma add_sub :
    forall n m,
      (n + m) - m = n.
  Proof.
    intros n m. induction m as [|m IHm].
    - rewrite add_0. destruct n; reflexivity.
    - rewrite add_S. simpl. apply IHm.
  Qed. 

End define_nat.

(** EXERCISE

  Define a boolean predicate deciding equality of natural numbers.

**)
Fixpoint eq_nat (x y : nat) : bool := match x,y with 
  | O, O => true
  | O, S _ | S _, O => false
  | S x', S y' => eq_nat x' y'
end.

(** EXERCISE **)
Lemma eq_nat_spec :
  forall n m,
    eq_nat n m = true <-> n = m.
Proof.
Admitted.

(** EXERCISE **)
Definition cur {X Y Z} (f : X * Y -> Z) : X -> Y -> Z :=
fun (x:X) (y:Y) => f (x,y).

(** EXERCISE **)
Definition car {X Y Z} (f : X -> Y -> Z) : X * Y -> Z :=
fun (c: X * Y) => let '(x,y) := c in f x y.

(** EXERCISE **)
Lemma car_cur :
  forall {X Y Z} (f : X * Y -> Z) p,
    car (cur f) p = f p.
Proof.
  intros X Y Z f p. destruct p as [x y]. reflexivity.
Qed.

(** EXERCISE **)
Lemma cur_car :
  forall {X Y Z} (f : X -> Y -> Z) x y,
    cur (car f) x y = f x y.
Proof.
  intros X Y Z f x y. reflexivity.
Qed.

(** EXERCISE **)
Definition swap {X Y} (p : X * Y) : Y * X :=
  let '(x,y) := p in (y,x).


(** EXERCISE **)
Lemma swap_invol :
  forall {X Y} (p : X * Y),
    swap (swap p) = p.
Proof.
intros X Y p. destruct p as [ x y]. reflexivity.
Qed.

(** EXERCISE

  Prove true <> false without the tactics inversion or discriminate.

  Note: a <> b is a notation for a ≠ b, meaning a = b -> False.

**)
Lemma true_false :
  true <> false.
Proof.
intro h.
change ()
Qed.
Print
Show Proof.

Require Import List.
Import ListNotations.

(** EXERCISE

  Prove the following. You will need lemmas, prove them yourself by induction
  and do not use lemmas from the standard library.

**)

Lemma concat_null : forall {A} (l: list A), l ++ [] = l.
intros A l. induction l as [|a l IHl].
- reflexivity.
- simpl. f_equal. exact IHl.
Qed.

Lemma concat_assoc : forall {A} (l1 l2 l3:list A), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
intros A l1 l2 l3. induction l1. 1: reflexivity.
simpl. rewrite IHl1. reflexivity.
Qed.

Lemma rev_app_distr :
  forall {A} (l1 l2 : list A),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros A l1.
  induction l1 as [| a l1 IHl].
  - simpl. symmetry. apply concat_null.
  - intro l2. simpl. rewrite IHl. rewrite concat_assoc. reflexivity.
Qed.

(** EXERCISE **)
Theorem rev_rev {X} (l : list X) :
  rev (rev l) = l.
Proof.
  induction l as [|a l IHl]. 1:reflexivity.
  simpl. rewrite rev_app_distr, IHl. simpl. reflexivity.
Qed.

Fixpoint fast_rev {A} (l : list A) (acc : list A) :=
  match l with
  | nil => acc
  | x :: l => fast_rev l (x :: acc)
  end.

(** EXERCISE **)
Lemma fast_rev_eq :
  forall A (l : list A),
    fast_rev l nil = rev l.
Proof.
  intros A l.
  generalize @nil as acc.
  induction l.
Admitted.
