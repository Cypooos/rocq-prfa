Inductive ens: Type := | inn : forall (A:Type), (A -> ens) -> ens.

Definition pair : ens -> ens -> ens :=
  fun (e1 e2:ens) => inn bool (fun (x:bool) =>
    match x with 
        | true => e1
        | false => e2
    end
  ).

Definition empty : ens := inn False (fun (x:False) => match x with end).


Definition subset: ens -> ens -> Prop :=
    fun '(inn A f:ens) '(inn B g:ens) => forall (x:A), exists (y:B), g y.


Definition eq : ens -> ens -> Prop := 
    fun (x:ens) (y:ens) => let '(inn A f) := x in let '(inn B g) := y in 
    () /\ ().