Require Import structures.DCPOSLs.

Require Import comobj.SilLTS.
Require Import comobj.VisLTS.
Require Import comobj.Traces.

Local Open Scope set_scope.

Definition refines {E}
  {Sα : Type} `{DCPO Sα} `{!Finitary (R := lce (P := Sα))} 
  {Sβ : Type} `{DCPO Sβ} `{!Finitary (R := lce (P := Sβ))}      
  (α : SilLTS E Sα) (β : SilLTS E Sβ) :=
  traces (louden α) ⊆ traces (louden β).

Lemma refines_refl {E} {Sα : Type} `{DCPO Sα} `{!Finitary (R := lce (P := Sα))}  
  (α : SilLTS E Sα) : refines α α.
Proof.
  intros t Ht. exact Ht.
Qed.

Lemma refines_trans {E}
  {Sα : Type} `{DCPO Sα} `{!Finitary (R := lce (P := Sα))} 
  {Sβ : Type} `{DCPO Sβ} `{!Finitary (R := lce (P := Sβ))}
  {Sγ : Type} `{DCPO Sγ} `{!Finitary (R := lce (P := Sγ))}  
  (α : SilLTS E Sα) (β : SilLTS E Sβ) (γ : SilLTS E Sγ) : 
  refines α β -> refines β γ -> refines α γ.
Proof.
  intros Hab Hbc. unfold refines. 
  transitivity (traces (louden β)); assumption.
Qed.

