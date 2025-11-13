From Stdlib Require Import List.
Import ListNotations.
Require Import ex1.
Require Import ex2.
Require Import ex3.

(* Q 4.1.a *)
(* We use K for the constant function and S as thoses are the relevent SKI model terminology *)
Reserved Notation "A ⊢H s" (at level 70).

Inductive hil {A:list form} : form -> Prop :=
  | h_ax s: In s A -> hil s
  | h_app s t: hil (s ~> t) -> hil s -> hil t
  | h_K s t: hil (s ~> t ~> s)
  | h_S s t u: hil ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u)
.

Notation "A ⊢H s" := (@hil A s) (at level 70).

(* Q 2.1.b *)
Lemma hil_ndm {A} s : A ⊢H s -> A ⊢m s.
Proof.
    intro h. induction h as [| s t| |].
    - apply ndm_ax. assumption.
    - apply ndm_imp_e with (s:= s); assumption.
    - apply ndm_imp_i.
      apply ndm_imp_i.
      apply ndm_ax; firstorder.
    - repeat apply ndm_imp_i.
      apply ndm_imp_e with (s:= t).
      + apply ndm_imp_e with (s:= s); apply ndm_ax; firstorder.
      + apply ndm_imp_e with (s := s); apply ndm_ax; firstorder.
Qed.

(* Q 4.1.c *)

(* Fact 1*)
Lemma hil_ex_K {A} s t : A ⊢H s -> A ⊢H t ~> s.
Proof.
  intros Hs.
  apply h_app with (s:= s).
  - apply h_K.
  - apply Hs.
Qed.

(* Fact 2*)
Lemma hil_ex_S {A} s t u : A ⊢H s ~> t ~> u -> A ⊢H s ~> t -> A ⊢H s ~> u.
Proof.
  intros Hstu Hst.
  apply h_app with (s:= (s ~> t)).
  2: apply Hst.
  apply h_app with (s:= (s ~> t ~> u)).
  2: apply Hstu.
  apply h_S.
Qed.

(* Fact 3 *)
Lemma hil_I {A} s : A ⊢H s ~> s.
Proof.
  apply hil_ex_S with (t := s ~> s).
  - apply h_K.
  - apply h_K.
Qed.

(* Q 4.1.d *)
(* A must be a parameter to make sure it is fixed during the proof and the induction *)
(* Doesn't generalise it under a A' or A0 *)
Lemma hil_impl {A} s t : (s::A) ⊢H t -> A ⊢H s ~> t.
Proof.
  intros Hs.
  induction Hs as [s' Hs'| s' t Hst Hs IHst IHs | |].
  - destruct Hs' as [Heq | Hin].
    + rewrite Heq. apply hil_I.
    + apply hil_ex_K. apply h_ax. firstorder.
  - apply hil_ex_S with (t:= s'); assumption.
  - apply hil_ex_K. apply h_K.
  - apply hil_ex_K. apply h_S.
Qed.

(* Q 4.1.e *)
Fact ndm_hil A s : A ⊢m s -> A ⊢H s.
Proof.
  intros Hs.
  induction Hs as [ | | ].
  - apply h_ax. assumption.
  - apply hil_impl. assumption.
  - apply h_app with (s := s); assumption.
Qed.

(* END OF THE PROJECT *)