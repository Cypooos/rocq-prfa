From Stdlib Require Import List.
Import ListNotations.

Inductive form : Type :=
| var ( x : nat) | bot | imp ( s t : form).

Print In.
Print incl.
Notation "s ~> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := (s ~> bot).
Reserved Notation "A ⊢c s" (at level 70).

(* Q 1.1.a *)
Inductive ndc : list form -> form -> Prop := 
 | ndc_ax : forall l:list form, forall a:form, In a l -> ndc l a
 | ndc_imp_i : forall l:list form, forall s t:form, ndc (s::l) t -> ndc l (imp s t)
 | ndc_imp_e : forall l:list form, forall s t:form, ndc l s -> ndc l (imp s t) -> ndc l t
 | ndc_abs : forall l:list form, forall s:form, ndc ((neg s)::l) bot -> ndc l s.

Notation "A ⊢c t" := (ndc A t).

(* Q 1.1.b *)
Lemma id {A:list form} {s:form} : A ⊢c s ~> s.
Proof.
    apply ndc_imp_i.
    apply ndc_ax.
    left. reflexivity.
Qed.

Lemma dbl_neg {A:list form} {s:form} : s::A ⊢c neg (neg s).
Proof.
    apply ndc_imp_i.
    apply ndc_imp_e with (s := s).
    1-2: apply ndc_ax; simpl; tauto.
Qed.

(* without a proof by contradiction: *)
Lemma dbl_neg_bot {A:list form} : neg (neg bot) :: A ⊢c bot.
Proof.
    apply ndc_imp_e with (s := neg bot).
    2: apply ndc_ax; simpl; tauto.
    apply id.
Qed.

(* Q 1.1.c *)
Fact Weakc A B s : A ⊢c s -> incl A B -> B ⊢c s.
Proof.
    intros h. generalize B as B'. induction h as [l a H | l s t H Hind| l s t h1 IH1 h2 IH2|l s H IH ].
    - intros B' Hincl. apply ndc_ax. apply Hincl. apply H.
    - intros B' Hincl. apply ndc_imp_i. apply Hind. apply incl_app_app with (l1 := [s]) (m1 := [s]).
      + apply incl_refl.
      + apply Hincl.
    - intros B' Hincl. apply ndc_imp_e with (s := s).
      + apply IH1. apply Hincl.
      + apply IH2. apply Hincl.
    - intros B' Hincl. apply ndc_abs. apply IH. apply incl_app_app with (l1 := [neg s]) (m1 := [neg s]).
      + apply incl_refl.
      + apply Hincl.
Qed.

(* Q 1.1.d *)
Fixpoint ground (s:form) : Prop := match s with (* Why a predicate? It's very decidable :eyes: *)
 | var _ => False
 | bot => True
 | imp x y => ground x /\ ground y
 end.


(* Part 1.2 *)

Definition model := nat -> Prop.

(* Q 1.2.a *)
Fixpoint interp (m:model) (x:form) : Prop := match x with 
 | bot => False
 | var k => m k
 | imp s t => interp m s -> interp m t
end.

(* Q 1.2.b *)
Fixpoint ctx_interp (m:model) (l:list form) : Prop := match l with 
 | [] => True
 | s::l' => interp m s /\ ctx_interp m l'
end.

(* Q 1.2.c : we do a small lemma for the first case (it's more of a list lemma) *)
Lemma in_hyp (M: model) (a : form) (l:list form) : In a l -> ctx_interp M l -> interp M a.
Proof.
    intros Hin Hctx. induction l as [|x l' IH].
    - exfalso. eapply in_nil. apply Hin.
    - simpl in Hin, Hctx. destruct Hctx as [HinterM Hctx]. destruct Hin as [ Hin | Hin].
      + rewrite <- Hin. apply HinterM.
      + apply IH; assumption.
Qed.

Lemma soundness M A ( s : form) : (forall P, ~~P -> P) -> A ⊢c s -> ctx_interp M A -> interp M s.
Proof.
    intros DNE h. induction h as [l a H | l s t H Hind| l s t h1 IH1 h2 IH2|l s H IH ].
    - apply in_hyp. apply H.
    - intros Hctx HM. apply Hind. split;assumption.
    - intros Hctx. simpl in IH2. apply IH2. 1: exact Hctx. apply IH1. exact Hctx.
    - intros Hctx. simpl in IH. apply DNE. intro nM. apply IH. split; assumption.
Qed.

(* Q 1.2.d *)
Lemma classical_consistency : ( forall P, ~~P -> P) -> ~([] ⊢c bot).
Proof.
    intros DNE Hcont.
    assert (M := fun (n:nat) => True).
    change (interp M bot).
    apply (soundness M [] bot DNE Hcont).
    constructor.
Qed.

(* Q 1.2.e *)
Lemma constructive_soundness M A (s : form) : A ⊢c s -> ctx_interp M A -> ~~interp M s.
    intros h. induction h as [l a H | | | ].
    - intros Hctx HM. apply HM. apply in_hyp with (l := l); assumption.
    - firstorder.
    - firstorder.
    - firstorder.
Qed.

(* Q 1.2.f *)
Lemma constructive_consistency : ~ ( [ ] ⊢c bot).
Proof.
    intros Hcont.
    assert (M := fun (n:nat) => True).
    change (interp M bot).
    apply (constructive_soundness M [] bot Hcont).
    - constructor.
    - tauto. 
Qed.

