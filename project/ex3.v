From Stdlib Require Import List.
Import ListNotations.
Require Import ex1.
Require Import ex2.


Reserved Notation "A ⊢cf s" (at level 70).
Reserved Notation "A ⊢ae s" (at level 70).

(* Definition *)
Inductive cf : list form -> form -> Prop :=
  | cf_imp s A t: cf (s :: A) t -> cf A (s ~> t)
  | ae_cf s t: ae s t -> cf s t
with ae : list form -> form -> Prop :=
  | ae_cut s t A: ae A (s ~> t) -> cf A s -> ae A t
  | ae_ax s A: In s A -> ae A s
.

Notation "A ⊢cf t" := (cf A t) (at level 70).
Notation "A ⊢ae t" := (ae A t)  (at level 70).

(* Definition of the very large complete induction principle *)
Scheme cf_ind_mut := Induction for cf Sort Prop
with ae_ind_mut := Induction for ae Sort Prop.
Combined Scheme cf_ae_ind from cf_ind_mut, ae_ind_mut.

(* Not dependant easier to use induction principle *)
Lemma cfae_ind :
  forall (Pcf: list form -> form -> Prop) (Pae: list form -> form -> Prop),

    (forall (s : form) (A : list form) (t : form), cf (s::A) t -> Pcf (s::A) t -> Pcf A (s ~> t)) ->
    (forall (A : list form) (s : form), ae A s -> Pae A s -> Pcf A s) ->
    (forall (s t : form) (A : list form), ae A (s ~> t) -> Pae A (s ~> t) -> cf A s -> Pcf A s -> Pae A t) ->
    (forall (s : form) (A : list form), In s A -> Pae A s) ->
  forall A s, (cf A s -> Pcf A s) /\ (ae A s -> Pae A s).
Proof.
  intros.
  assert (Hgoal :
    (forall (l : list form) (f : form), cf l f -> Pcf l f) /\
    (forall (l : list form) (f : form), ae l f -> Pae l f) ).
  apply cf_ae_ind with
    (P := fun A s => fun (_:cf A s) => Pcf A s)
    (P0 := fun A s => fun (_:ae A s) => Pae A s); firstorder.
  destruct Hgoal. firstorder.
Qed. 

Lemma ae_ind_better : forall (P : list form -> form -> Prop),
 (forall s t A, ae A (s ~> t) -> P A (s ~> t) -> cf A s -> P A t) ->
 (forall s A, In s A -> P A s) ->
 forall A s, ae A s -> P A s.
Admitted.

(* Lemma 1: weakening *)
Lemma cfae_weak A s : (A ⊢cf s -> forall B, incl A B -> B ⊢cf s) /\ (A ⊢ae s -> forall B, incl A B -> B ⊢ae s).
Proof.
  apply cfae_ind with
    (Pcf := fun A s => forall B, incl A B -> cf B s)
    (Pae := fun A s => forall B, incl A B -> ae B s); intro s'; intros.
  - apply cf_imp. firstorder.
  - apply ae_cf. firstorder.
  - apply ae_cut with (s:= s'); firstorder.
  - apply ae_ax. firstorder.
Qed.

Lemma cf_weak A A' s : incl A A' -> A ⊢cf s -> A' ⊢cf s.
Proof.
  intros Hinc Acf. 
  destruct (cfae_weak A s) as [H ?].
  apply H;assumption.
Qed.

Lemma ae_weak A A' s : incl A A' -> A ⊢ae s -> A' ⊢ae s.
Proof.
  intros Hinc Acf. 
  destruct (cfae_weak A s) as [? H].
  apply H;assumption.
Qed.

(* cut-free syntatic model *)
Definition cf_syntatic_model : WModel.
Proof.
  refine {|
    ty := list form;
    rel := @incl form;
    interp := fun (x:list form) => fun (n:nat) => match n with | 0 => x ⊢cf bot | S k => x ⊢cf (var k) end;
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros w w' [|k] Hincl Hw; apply cfae_weak with (A:=w); assumption.
Defined.

(* Lemma 2 : correctness *)
Lemma correctness A s : (winterp cf_syntatic_model A s -> A ⊢cf s) /\ (A ⊢ae s -> winterp cf_syntatic_model A s).
Proof.
  generalize A. induction s as [k | | s IHs t IHt].
  - split.
    + firstorder.
    + intro h. apply ae_cf. assumption.
  - split.
    + firstorder.
    + intro h. apply ae_cf. assumption.
  - intro A0. split.
    + intros Ass1.
      apply cf_imp.
      apply IHt.
      apply Ass1. 1:firstorder.
      apply IHs.
      apply ae_ax. firstorder.
    + intros Hst A' Hincl HA'.
      apply IHt.
      apply ae_cut with (s := s).
      * apply ae_weak with (A := A0) (s := s ~> t); assumption.
      * apply IHs; assumption.
Qed.

(* Lemma 3 : reflexivity *)
(* We prove a generalization to all variable A' that contains A *)
Lemma cf_incl A A': incl A A' -> ctx_winterp cf_syntatic_model A' A.
Proof.
  induction A as [| x l Hl].
  - constructor.
  - split.
    + apply correctness. apply ae_ax. firstorder.
    + apply Hl. firstorder.
Qed.  

Lemma cf_refl A : ctx_winterp cf_syntatic_model A A.
Proof.
  apply cf_incl.
  firstorder.
Qed.

(* Theorem 4: cut elimination. We proove the real one, not the one as stated (which doesn't need soundness) *)
Theorem cut_elimination A s: A ⊢m s -> A ⊢cf s.
Proof.
  intros H.
  apply wsoundness with (M := cf_syntatic_model) (w := A) in H.
  - apply correctness. exact H.
  - apply cf_refl.
Qed.

(* Lemma 5: We need to use 'remember' and revert to be sure to have the shape *)
(* of the goal accesible. *)
Lemma no_ae s : ~ ([] ⊢ae s).
Proof.
  intros h.
  remember [] as A eqn: Heq.
  revert Heq.
  induction h as [| s A H].
  - tauto.
  - intro Heq. rewrite Heq in H. exact H.
Qed.

(* The recursive function: *)
Fixpoint long_arrow A s := match A with 
 | [] => s
 | t::A' => t ~> (long_arrow A' s) 
end.

Notation "A '-->' s" := (long_arrow A s) (at level 60).

(* Lemma 6 *)
Lemma nns_A_la_s A : ~([neg (neg (var 0))] ⊢ae A --> (var 0)).
Proof.
  intros h.
  remember [neg (neg (var 0))] as AL eqn: HeqAL.
  remember (A --> var 0) as Avar eqn: HeqAvar.
  revert HeqAL.
  revert HeqAvar.
  induction h as [s t A' Hst Hs IH | ] in A |-*. 
  - 
Admitted.

Theorem dne_consistency : ~(forall s, [] ⊢m neg (neg s) ~> s).
Proof.
  intros h.
  specialize h with (var 0).
  apply cut_elimination in h.
  inversion h as [s A t h' | s t H ].
  - inversion h' as [|Idc Idc2 Useful].
    apply (nns_A_la_s []). exact Useful.
  - apply no_ae in H. assumption.
Qed.