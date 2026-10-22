Require Import structures.DCPOSLs.

Require Import comobj.SilLTS.
Require Import comobj.VisLTS.
Require Import comobj.Traces.

Section REFINES.
  Context {E Sα : Type}
    `{DCPO Sα} `{!Finitary (R := lce (P := Sα))}.
  Local Open Scope set_scope.

  Section DEF.
    Context {Sβ : Type}
      `{DCPO Sβ} `{!Finitary (R := lce (P := Sβ))}.

    Definition refines (α : SilLTS E Sα) (β : SilLTS E Sβ) :=
      traces (louden α) ⊆ traces (louden β).
  End DEF.

  Lemma refines_refl (α : SilLTS E Sα) : refines α α.
  Proof.
    intros t Ht. exact Ht.
  Qed.

End REFINES.
