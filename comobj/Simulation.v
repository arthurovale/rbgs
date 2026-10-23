Require Import coqrel.LogicalRelations.

Require Import comobj.SilLTS.

Local Open Scope em_scope.

Reserved Notation "α ⊢ s -ɛ*-> t" (at level 70, s at level 35, t at level 35).

Inductive sil_star {E : Type} {Sα : Type} {Sα_po : PPoset Sα}
  (α : Sα -> convex_set (Tsil E Sα)) : Sα -> Sα -> Prop :=
| sil_star_nil s : α ⊢ s -ɛ*-> s
| sil_star_cons s s_mid s' : 
  α ⊢ s -ɛ-> s_mid -> α ⊢ s_mid -ɛ*-> s' -> α ⊢ s -ɛ*-> s'
  where "α ⊢ s -ɛ*-> t" := (sil_star α s t) : tsil_scope.

Definition sil_plus {E : Type} {Sα : Type} {Sα_po : PPoset Sα}
  (α : Sα -> convex_set (Tsil E Sα)) : Sα -> Sα -> Prop := 
  fun s s' => exists s_mid, α ⊢ s -ɛ-> s_mid /\ α ⊢ s_mid -ɛ*-> s'.

Notation "α ⊢ s -ɛ+-> t" := (sil_plus α s t) (at level 70, s at level 35, t at level 35).

Section SIMF.
  Context {E : Type} {Sα Sβ : Type} {Sα_po : PPoset Sα} {Sβ_po : PPoset Sβ}.

  Definition simF 
    (α : Sα -> convex_set (Tsil E Sα)) (β : Sβ -> convex_set (Tsil E Sβ))
    (R : rel Sα Sβ) (Rdiv : rel Sα Sβ) (sα : Sα) (sβ : Sβ) : Prop :=
      (forall e sα', α ⊢ sα -'e-> sα' -> 
        exists sβ', exists sβ_mid, 
          β ⊢ sβ -ɛ*-> sβ_mid /\ β ⊢ sβ_mid -'e-> sβ' /\ R sα' sβ') 
      /\ 
      (forall sα', α ⊢ sα -ɛ-> sα' -> 
        ((exists sβ', β ⊢ sβ -ɛ+-> sβ' /\ R sα' sβ') 
        \/ 
        (R sα' sβ /\ Rdiv sα' sβ))).

    (* need to define R_div, divpresF, etc *)
End SIMF.