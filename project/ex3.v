From Stdlib Require Import List.
Import ListNotations.
Require Import ex1.
Require Import ex2.



Scheme cf_ind_mut := Induction for cf Sort Prop
with ae_ind_mut := Induction for ae Sort Prop.
Combined Scheme cf_ae_ind from cf_ind_mut, ae_ind_mut.
Check cf_ae_ind.