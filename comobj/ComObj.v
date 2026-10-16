Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import Stdlib.Logic.FunctionalExtensionality.

Require Import comobj.AsyncEvents.
Import AsyncEvents.

Definition Tsil (E S : Type) : Type :=
  lift (Async E * lift S eq) (eq * lce)%rel.

Declare Scope tsil_scope.
Delimit Scope tsil_scope with tsil.

Notation "↺" := lift_bot : tsil_scope.
Notation "↑ s" := (lift_el s) (at level 9, s at next level) : tsil_scope.
Notation "⊥" := lift_bot : tsil_scope.
Notation "- a -> t" := (lift_el (a, t))
  (at level 35, a at level 35, t at level 35) : tsil_scope.

Open Scope tsil_scope.

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

Section TVIS.
  Context {E S : Type}.

  Global Instance Tvis_dcpo : DCPO (Tvis E S) := lift_dcpo.

  Global Instance Tvis_finitary : Finitary (R := lce (P := Tvis E S)).
  Proof.
    intros d. destruct d as [| [e [| s]]].
    - exists [⊥]. intros x. split.
      + intros H. inversion H; subst. left. reflexivity.
      + intros [<- | []]. constructor.
    - exists [⊥; - e -> ↺]. intros x. split.
      + intros H. inversion H; subst; [left; reflexivity |].
        destruct x0 as [e' t']. destruct H2 as [He Ht]. cbn in He, Ht. subst e'.
        change (lift_lce t' lift_bot) in Ht. inversion Ht; subst.
        right. left. reflexivity.
      + intros [<- | [<- | []]]; constructor. split; [reflexivity | constructor].
    - exists [⊥; - e -> ↺; - e -> ↑s]. intros x. split.
      + intros H. inversion H; subst; [left; reflexivity |].
        destruct x0 as [e' t']. destruct H2 as [He Ht]. cbn in He, Ht. subst e'.
        change (lift_lce t' (lift_el s)) in Ht. inversion Ht; subst.
        * right. left. reflexivity.
        * right. right. left. reflexivity.
      + intros [<- | [<- | [<- | []]]]; constructor; split; try reflexivity; constructor.
  Qed.

  (** [Tvis] sits inside [Tsil] as the visible transitions. *)
  Definition tvis_tsil (t : Tvis E S) : Tsil E S :=
    match t with
    | ⊥ => ⊥
    | -e-> c => -'e-> c
    end.

    (** the injection [tvis_tsil] has a retract forming and embedding-projection pair *)
    Definition tsil_tvis (t : Tsil E S) : Tvis E S :=
    match t with
    | ⊥ => ⊥
    | -'e-> s => -e-> s
    | -ɛ-> s => ⊥
    end.

  Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
  Local Abbreviation id := (fun x => x).

  Lemma tivs_tsil_retract : tvis_tsil ;; tsil_tvis = id.
  Proof.
    apply functional_extensionality. intros [ | [e s]]; reflexivity.
  Qed.

  Lemma tivs_tsil_proj (t : Tsil E S) : lce ((tsil_tvis ;; tvis_tsil) t) t.
  Proof.
    destruct t as [| [[e |] s]]; cbn.
    - constructor.
    - constructor. split; reflexivity.
    - constructor.
  Qed.

End TVIS.
  