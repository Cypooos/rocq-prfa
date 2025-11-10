From Stdlib Require Import List.
Import ListNotations.
Require Import ex1.

Reserved Notation "A ⊢m s" (at level 70).

(* Q 2.1.a *)
Inductive ndm : list form -> form -> Prop := 
 | ndm_ax : forall l:list form, forall a:form, In a l -> ndm l a
 | ndm_imp_i : forall l:list form, forall s t:form, ndm (s::l) t -> ndm l (imp s t)
 | ndm_imp_e : forall l:list form, forall s t:form, ndm l s -> ndm l (imp s t) -> ndm l t.

Notation "A ⊢m t" := (ndm A t).

(* Q 2.1.b : we copy the proof for ndc without a case *)
Lemma Weakm A B s : A ⊢m s -> incl A B -> B ⊢m s.
Proof.
    intros h. generalize B as B'. induction h as [l a H | l s t H Hind| l s t h1 IH1 h2 IH2].
    - intros B' Hincl. apply ndm_ax. apply Hincl. apply H.
    - intros B' Hincl. apply ndm_imp_i. apply Hind. apply incl_app_app with (l1 := [s]) (m1 := [s]).
      + apply incl_refl.
      + apply Hincl.
    - intros B' Hincl. apply ndm_imp_e with (s := s).
      + apply IH1. apply Hincl.
      + apply IH2. apply Hincl.
Qed.

(* Q 2.1.c *)
Lemma Implication A s : A ⊢m s -> A ⊢c s.
Proof.
    intros h. induction h as [ | |].
    - apply ndc_ax. assumption.
    - apply ndc_imp_i. assumption.
    - apply ndc_imp_e with (s := s); assumption.
Qed.

(* Q 2.1.d *)
Fixpoint trans (t s:form) := match s with 
 | var k => (var k ~> t) ~> t
 | bot => t
 | imp x y => imp (trans t x) (trans t y)
end.


(* Q 2.1.e *)
Lemma ndm_imp_comm_dbl A a b t : ((a ~> b) ~> t) ~>t :: A ⊢m ((a ~> t) ~> t) ~> ((b ~> t) ~> t).
Proof.
  apply ndm_imp_i.
  apply ndm_imp_i.
  apply ndm_imp_e with (s:= ((a ~> b) ~> t)). 2:apply ndm_ax; firstorder.
  apply ndm_imp_i. 
  apply ndm_imp_e with (s := (a ~> t)). 2:apply ndm_ax; firstorder.
  apply ndm_imp_i.
  apply ndm_imp_e with (s := b). 2:apply ndm_ax; firstorder.
  apply ndm_imp_e with (s := a); apply ndm_ax; firstorder.
Qed.


Lemma DNE_Friedman A s t : A ⊢m (( trans t s ~> t) ~> t) ~> (trans t s).
Proof.
    apply ndm_imp_i.
    induction s as [k | | x Hx y Hy].
    - simpl. apply ndm_imp_i. apply ndm_imp_e with (s := (((var k ~> t) ~> t) ~> t)). 
      + apply ndm_imp_i. apply ndm_imp_e with (s := (var k ~> t)); apply ndm_ax; firstorder.
      + apply ndm_ax; firstorder.
    - simpl. apply ndm_imp_e with (s := (t ~> t)).
      + apply ndm_imp_i. apply ndm_ax. firstorder.
      + apply ndm_ax. firstorder.
    - simpl. apply ndm_imp_i. apply ndm_imp_e with (s := ((trans t y ~> t) ~> t)).
      + apply ndm_imp_i.
        apply ndm_imp_e with (s:= trans t y). 2: apply ndm_ax; firstorder.
        apply ndm_imp_e with (s:= ((trans t x ~> t) ~> t) ~> ((trans t y ~> t) ~> t)).
        * apply Weakm with (A:= [((trans t x ~> trans t y) ~> t) ~> t]).
          1: apply ndm_imp_comm_dbl.
          firstorder.
        * apply ndm_imp_i.
          apply ndm_imp_e with (s:= ((trans t y ~> t) ~> t)).
          ** apply ndm_imp_e with (s:= ((trans t x ~> t) ~> t)).
             2:apply ndm_ax; firstorder.
             apply ndm_imp_i.
             apply ndm_imp_e with (s:= trans t x).
             2: apply ndm_ax; firstorder.
             apply ndm_ax; firstorder.
          ** apply ndm_imp_i.
             apply Weakm with (A:= ((trans t y) ~> t) ~> t :: A).
             2:firstorder.
             exact Hy.
      + apply ndm_imp_i.
        apply Weakm with (A:= ((trans t y) ~> t) ~> t :: A).
        2:firstorder.
        exact Hy.
Qed.

(* Q 2.1.f*)
Lemma Friedman A s t : A ⊢c s -> map (trans t) A ⊢m trans t s.
Proof.
    intro h. induction h as [l a H | l x y H Hind| l x y h1 IH1 h2 IH2|l x H IH ].
    - apply ndm_ax. apply in_map. apply H.
    - simpl. simpl in Hind. apply ndm_imp_i. exact Hind.
    - simpl. apply ndm_imp_e with (s := (trans t x)); assumption.
    - simpl in IH.
      apply ndm_imp_e with (s:= (( trans t x ~> t) ~> t)).
      2: apply DNE_Friedman.
      apply ndm_imp_i. exact IH.
Qed.

(* Q 2.1.g*)
Lemma ground_trans_bot s : ground s -> trans bot s = s. 
Proof.
  intros Hground.
  induction s as [x | | x IHx y IHy].
  - destruct Hground.
  - reflexivity.
  - simpl. destruct Hground as [Hgx Hgy].
    rewrite (IHy Hgy).
    rewrite (IHx Hgx).
    reflexivity.
Qed.
    

Lemma ground_truths s : ground s -> ([] ⊢m s <-> [] ⊢c s).
Proof.
  intro Hground.
  split.
  1:apply Implication.
  intro h.
  rewrite <- (ground_trans_bot s Hground).
  apply Friedman with (A := []).
  exact h.
Qed.

(* Q 2.1.h *)
(*
  This lemma is kind of stupid as we already have proven the consistency of classical logic in constructive_consistency.
  "To be equivalent" just means to show it:
*)
Lemma dne_consistency : ~ ([] ⊢m bot).
Proof.
  intros h.
  apply constructive_consistency.
  apply (ground_truths bot).
  - constructor.
  - exact h.
Qed.

(* Q 2.1.i *)
Definition dne s := (( s ~> bot) ~> bot) ~> s.



Lemma consistency_of_dne s : ~( [ ] ⊢m dne s ~> bot).
Proof.
Admitted.

(* Q 2.2.a *)
(* Notice how "bot" just act as a specific variable. With this in mind, let var 0 = bot, and other var will be interpreted as S x *)

Record WModel := {
  ty : Type ;
  rel : ty -> ty -> Prop;
  interp : ty -> nat -> Prop;
  w_refl : forall x:ty, rel x x;
  w_trans : forall x y z:ty, rel x y -> rel y z -> rel x z;
  w_incl : forall w w':ty, forall i:nat, rel w w' -> interp w i -> interp w' i; 
}.

Notation "w '≤(' M ) w'" := (M.(rel) w w') ( at level 40, w' at next level).

(* Q 2.2.b *)
Fixpoint winterp (M: WModel) (w:M.(ty)) (s:form) : Prop := match s with
  | bot => M.(interp) w 0
  | var x => M.(interp) w (S x)
  | x ~> y => forall w':M.(ty), M.(rel) w w' -> winterp M w' x -> winterp M w' y 
end.

(* Q 2.2.c *)
Fixpoint ctx_winterp (M : WModel) (w: M.(ty)) (l:list form) : Prop := match l with 
 | [] => True
 | s::l' => winterp M w s /\ ctx_winterp M w l'
end.

(* Q 2.2.d *)
Lemma monotonicity M s w w' : w ≤(M) w' -> winterp M w s -> winterp M w' s.
Proof.
  intros Hrel Hw.
  induction s as [k | | x IHx y IHy].
  - apply M.(w_incl) with (w := w); assumption.
  - apply M.(w_incl) with (w := w); assumption.
  - intros w3 Hrel3 Hw3. apply Hw.
    + apply M.(w_trans) with (y:= w'); assumption.
    + assumption.
Qed.

(* Q 2.2.e *)
Lemma ctx_monotonicity M A w w' : w ≤(M) w' -> ctx_winterp M w A -> ctx_winterp M w' A.
Proof.
  induction A as [ | x l IHl].
  - firstorder.
  - simpl. intros Hrel [Hx Hl]. split.
    + apply monotonicity with (w := w); firstorder.
    + tauto.
Qed.

(* Q 2.2.f *)
Lemma in_whyp (M: WModel) (w:M.(ty)) (a : form) (l:list form) : In a l -> ctx_winterp M w l -> winterp M w a.
Proof.
    intros Hin Hctx. induction l as [|x l' IH].
    - exfalso. eapply in_nil. apply Hin.
    - simpl in Hin, Hctx. destruct Hctx as [HinterM Hctx]. destruct Hin as [ Hin | Hin].
      + rewrite <- Hin. apply HinterM.
      + apply IH; assumption.
Qed.

Lemma wsoundness M A s : A ⊢m s -> forall w, ctx_winterp M w A -> winterp M w s.
Proof.
  intros Hm.
  induction Hm as [l a Hin | l s t Hm IH | l s t Hs Hst IHs IHst].
  - intro w'. apply in_whyp. assumption.
  - intros w Hctx w' Hrel Hsw'. apply IH.
    split. 1: assumption.
    apply ctx_monotonicity with (w:= w); assumption.
  - intros w Hctx.
    apply IHst with (w' := w) (w := w).
    + apply Hctx.
    + apply M.(w_refl).
    + apply Hst. apply Hctx.
Qed.

(* Q 2.2.g *)
Definition neq0 (n:nat) : Prop :=
  match n with 0 => False | S _ => True end.

Definition consistency_model : WModel.
Proof. 
  refine {|
    ty := unit;
    rel := eq;
    interp := fun (tt:unit) => neq0;
  |}.
  - firstorder.
  - apply eq_trans.
  - firstorder.
Defined.

(* Q 2.2.h *)
Lemma consistency : ~ ([] ⊢m bot).
Proof.
  intros h.
  apply wsoundness with (M := consistency_model) (w := tt) in h; firstorder.
Qed.

(* Q 2.2.i *)
Definition wdne_rel (b1 b2:bool) : Prop := match b1,b2 with
  | true, false => False
  | _,_ => True
end.
Definition wdne_interp (b:bool) (n:nat) : Prop := match b,n with
  | true, S _ => True
  | _,_ => False
end.

Definition notdne_model : WModel.
Proof. 
  refine {|
    ty := bool;
    rel := wdne_rel;
    interp := wdne_interp;
  |}.
  - intros [|]; constructor.
  - intros [|][|][|] h1 h2; assumption. 
  - intros [|][|][|k]; tauto. 
Defined.

(* Q 2.2.j *)
Lemma dne_independant : ~(forall s, [] ⊢m dne s).
Proof.
Abort.

(* Q 2.3.a *)
Definition syntatic_model : WModel.
Proof.
  refine {|
    ty := list form;
    rel := @incl form;
    interp := fun (x:list form) => fun (n:nat) => match n with | 0 => x ⊢m bot | S k => x ⊢m (var k) end;
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros w w' [|k] Hincl Hw; apply Weakm with (A:=w); assumption.
Defined.


(* Q 2.3.b *)
Lemma correctness A s : winterp syntatic_model A s <-> A ⊢m s.
Proof.
  generalize A. induction s as [k| | x IHx y IHy ].
  - intros A'. firstorder.
  - intros A'. firstorder.
  - intros A'. split.
    + intros Hxy'.
      apply ndm_imp_i.
      apply IHy.
      apply Hxy'.
      1: firstorder.
      fold winterp.
      apply IHx.
      apply ndm_ax. firstorder.
    + intros Hm A2 H2incl H2x.
      apply IHy.
      apply ndm_imp_e with (s:= x).
      * apply IHx. apply H2x.
      * apply Weakm with A'; assumption.
Qed.


(* Q 2.3.c *)
Lemma completness A s : (forall M w, ctx_winterp M w A -> winterp M w s) -> A ⊢m s.
Proof.