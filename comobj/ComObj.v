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

  Lemma tvis_tsil_retract : tvis_tsil ;; tsil_tvis = id.
  Proof.
    apply functional_extensionality. intros [ | [e s]]; reflexivity.
  Qed.

  Lemma tvis_tsil_proj (t : Tsil E S) : lce ((tsil_tvis ;; tvis_tsil) t) t.
  Proof.
    destruct t as [| [[e |] s]]; cbn.
    - constructor.
    - constructor. split; reflexivity.
    - constructor.
  Qed.

  (** Both maps of the embedding-projection pair are strict Scott-continuous:
    they are monotonic and strict, and both domains are finitary. *)

  Lemma tvis_tsil_mon : Monotonic tvis_tsil (lce ++> lce).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [e c], y as [e' c']; destruct H0 as [He Hc]; cbn in *; subst.
    constructor. split; [reflexivity | exact Hc].
  Qed.

  Lemma tsil_tvis_mon : Monotonic tsil_tvis (lce ++> lce).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [[e |] c], y as [[e' |] c']; destruct H0 as [He Hc]; cbn in *;
      try discriminate He; try constructor.
    injection He as <-. split; [reflexivity | exact Hc].
  Qed.

  (** The abstract [bot] of each domain is the constructor. *)
  Lemma Tvis_bot : (bot : Tvis E S) = ⊥.
  Proof. apply lift_bot_eq. Qed.

  Lemma Tsil_bot : (bot : Tsil E S) = ⊥.
  Proof. apply lift_bot_eq. Qed.

  Global Instance tvis_tsil_sc : ScottContinuous true tvis_tsil.
  Proof.
    apply finitary_sc; [exact tvis_tsil_mon |].
    rewrite Tvis_bot, Tsil_bot. reflexivity.
  Qed.

  Global Instance tsil_tvis_sc : ScottContinuous true tsil_tvis.
  Proof.
    apply finitary_sc; [exact tsil_tvis_mon |].
    rewrite Tsil_bot, Tvis_bot. reflexivity.
  Qed.

  Definition behobj := S -> convex_set (Tvis E S).

  Definition loud (α : comobj E S) : 
    exists (α_vis : behobj), α_vis ;; convex_map tvis_tsil = α.

  Lemma loud_unique {α : comobj E S} {α_vis : behobj} {α_vis' : behobj} : 
    α_vis ;; convex_map tvis_tsil = α -> α_vis' ;; convex_map tvis_tsil = α
      -> α_vis = α_vis'.
  Proof.
    intros H H'.  apply (f_equal (fun x => x ;; convex_map tsil_tvis)) in H, H'.
    change (α_vis ;; (convex_map tvis_tsil ;; convex_map tsil_tvis) = α ;; convex_map tsil_tvis) in H.
    change (α_vis' ;; (convex_map tvis_tsil ;; convex_map tsil_tvis) = α ;; convex_map tsil_tvis) in H'.
    rewrite <- (convex_map_compose tsil_tvis tvis_tsil (Hg := tsil_tvis_mon)) in H, H'.
    rewrite tvis_tsil_retract, convex_map_id in H, H'.
    change (α_vis = α ;; convex_map tsil_tvis) in H.
    change (α_vis' = α ;; convex_map tsil_tvis) in H'.
    rewrite H, H'. reflexivity.
  Qed.
End TVIS.