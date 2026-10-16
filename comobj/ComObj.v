Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import comobj.AsyncEvents.
Import AsyncEvents.

Definition Tsil (E S : Type) : Type :=
  lift (Async E * lift S eq) (eq * lce)%rel.

Declare Scope teps_scope.
Delimit Scope teps_scope with teps.

Notation "↺" := lift_bot : teps_scope.
Notation "↑ s" := (lift_el s) (at level 9, s at next level) : teps_scope.
Notation "⊥" := lift_bot : teps_scope.
Notation "- a -> t" := (lift_el (a, t))
  (at level 35, a at level 35, t at level 35) : teps_scope.

Open Scope teps_scope.

Section TSIL.
  Context {E S : Type}.

  Definition sil_div : Tsil E S := -ɛ-> ↺.
  Definition sil (s : S) : Tsil E S := -ɛ-> ↑s.
  Definition div (e : E) : Tsil E S := -'e-> ↺.
  Definition vis (e : E) (s : S) : Tsil E S := -'e-> ↑s.

  Global Instance Tsil_dcpo : DCPO (Tsil E S) := lift_dcpo.

  Global Instance Tsil_finitary : Finitary (R := lce (P := Tsil E S)).
  Proof.
    intros x. destruct x.
    - exists [⊥]. intros t. split.
      + intros. constructor. rewrite <- lift_bot_eq in *.
        symmetry. apply lce_bot_eq. assumption.
      + intros H. inversion H. 
        subst. reflexivity.
        contradiction.
    - destruct x as [e' [ | s]].
      + exists [⊥ ; - e' -> ⊥]. intros t. split.
        * intros H. inversion H; subst. constructor; reflexivity.
          right. constructor. apply antisymmetry. 
          constructor. constructor; simpl. inversion H2. simpl in *.
          symmetry. assumption. constructor. assumption.
        * intros H. inversion H; subst.
          constructor. inversion H0; subst. reflexivity. contradiction.
      + exists [⊥ ; - e' -> ⊥; - e' -> ↑ s]. intros t. split.
        * intros H. inversion H; subst. constructor; reflexivity.
          right. destruct x as [e [ | s']].
          constructor. inversion H2; simpl in *; subst; reflexivity. 
          right. inversion H2; simpl in *; subst; left. inversion H1; subst.
          reflexivity.
        * intros H. inversion H; subst. constructor. inversion H0; subst.
          constructor. constructor. reflexivity. constructor. inversion H1; subst.
          reflexivity. contradiction.
  Qed.
End TSIL.

Definition comobj E S := S -> convex_set (Tsil E S).

(** The extension of any communicating object to the lifted
  state space is strict Scott-continuous by definition. *)
Example comobj_ext_sc {E S} (f : comobj E S) :
  ScottContinuous true (DCPOExtra.ext (R := eq) f) := _.

Definition Tvis (E S : Type) : Type := lift (E * lift S eq) (eq * lce)%rel.

