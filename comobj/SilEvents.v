Require Import interfaces.Category.
Require Import interfaces.Functor.
Require Import interfaces.MonoidalCategory.

Require Import Stdlib.Logic.FunctionalExtensionality.

(** * Silent Events *)

(** Silent events are either a visible event or an invisible event. *)

(** ** First, we model silence by implicitly considering epsilon moves
  this is nicely achieved by using the lift monad *)

Module SilentEventsBase <: Category.

  Definition t : Type := Type.

  Inductive Sil (T : Type) : Type :=
  | vis (x : T)
  | ɛ.
  Arguments vis {T} x.
  Arguments ɛ {T}.

  Notation "⇑ A" := (Sil A) (at level 35).
  Notation "' x" := (vis x) (at level 9, x at next level).

  Definition m : t -> t -> Type :=
      fun A => fun B => A -> Sil B.

  Program Definition id (A : t) : m A A := fun ev => 'ev.

  Program Definition compose {A B C : t} (g : m B C) (f : m A B)  :=
    fun ev =>
      match f ev with
      | 'ev' => g ev'
      | ɛ => ɛ
      end.

  Proposition compose_id_left :
    forall {A B} (f : m A B), compose (id B) f = f.
  Proof.
    intros; extensionality ev; unfold compose;
    destruct (f ev) as [ev' | ];
    easy.
  Qed.

  Proposition compose_id_right :
    forall {A B} (f : m A B), compose f (id A) = f.
  Proof.
    intros; extensionality ev; unfold compose; reflexivity.
  Qed.

  Proposition compose_assoc :
    forall {A B C D} (f : m A B) (g : m B C) (h : m C D),
    compose (compose h g) f = compose h (compose g f).
  Proof.
    intros; extensionality ev; unfold compose;
    destruct (f ev) as [ev' | ]; reflexivity.
  Qed.

  Include CategoryTheory.
End SilentEventsBase.

(** ** Bicartesian structure for SilentEvents
    We show that SilentEvents has both products and coproducts. *)
Module SilentEventsBicartesian <: BicartesianCategory.
  Include SilentEventsBase.

  (** First we establish the cartesian (product) structure *)
  Module Prod <: CartesianStructure SilentEventsBase.

    (** Terminal object: Empty_set (any morphism to it must be ɛ) *)
    Definition unit : t := Empty_set : Type.

    Definition ter (X : t) : m X unit := fun ev => ɛ.

    Proposition ter_uni : forall {X} (x y : m X unit), x = y.
    Proof.
      intros; extensionality ev.
      destruct (x ev) as [[] | ], (y ev) as [[] | ]; reflexivity.
    Qed.

    Inductive silProd {A B : Type} : Type :=
    | sync (a : A) (b : B)
    | sill (a : A)
    | silr (b : B).

    (** Binary products: A × B *)
    Definition omap (A B : Type) : Type := @silProd A B.

    Notation "⟨ a | b ⟩" := (sync a b) (at level 0).
    Notation "⟨ a | ⟩" := (sill a) (at level 0).
    Notation "⟨ | b ⟩" := (silr b) (at level 0).

    Definition p1 {A B : t} : m (omap A B) A :=
      fun obs =>
        match obs with
        | ⟨a | b⟩ => 'a
        | ⟨a | ⟩ => 'a
        | ⟨ | b⟩ => ɛ
        end.

    Definition p2 {A B : t} : m (omap A B) B :=
      fun obs =>
        match obs with
        | ⟨a | b⟩ => 'b
        | ⟨a | ⟩ => ɛ
        | ⟨ | b⟩ => 'b
        end.

    Definition pair {X A B : t} (f : m X A) (g : m X B) : m X (omap A B) :=
      fun x =>
        match f x, g x with
        | 'a, 'b => '⟨a | b⟩
        | 'a, ɛ => '⟨a | ⟩
        | ɛ, 'b => '⟨ | b⟩
        | ɛ, ɛ => ɛ
        end.

    Proposition p1_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p1 (pair f g) = f.
    Proof.
      intros; extensionality x; unfold compose, pair, p1.
      destruct (f x) as [a | ], (g x) as [b | ]; reflexivity.
    Qed.

    Proposition p2_pair : forall {X A B} (f : m X A) (g : m X B),
      compose p2 (pair f g) = g.
    Proof.
      intros; extensionality x; unfold compose, pair, p2.
      destruct (f x) as [a | ], (g x) as [b | ]; reflexivity.
    Qed.

    Proposition pair_pi_compose : forall {X A B} f,
      @pair X A B (compose p1 f) (compose p2 f) = f.
    Proof.
      intros; extensionality ev. unfold compose, pair, p1, p2.
      destruct (f ev) as [[a b | a | b] | ]. all: reflexivity.
    Qed.

    Include CartesianStructureTheory SilentEventsBase.
    Include BifunctorTheory SilentEventsBase SilentEventsBase SilentEventsBase.
    Include SymmetricMonoidalStructureTheory SilentEventsBase.
  End Prod.

  Include CartesianTheory SilentEventsBase.

  (** Then we add the cocartesian (coproduct) structure *)
  Module Plus <: CocartesianStructure SilentEventsBase.

    (** Initial object: Empty_set *)
    Definition unit : t := Empty_set : Type.

    Definition ini (X : t) : m unit X := fun e => match e with end.

    Proposition ini_uni : forall {X} (x y : m unit X), x = y.
    Proof.
      intros; extensionality e; destruct e.
    Qed.

    (** Binary coproducts: A + B *)
    Definition omap (A B : t) : t := (A + B)%type.

    Definition i1 {A B : t} : m A (A + B)%type :=
      fun a => '(inl a).

    Definition i2 {A B : t} : m B (A + B)%type :=
      fun b => '(inr b).

    Definition copair {X A B : t} (f : m A X) (g : m B X) : m (A + B)%type X :=
      fun ab =>
        match ab with
        | inl a => f a
        | inr b => g b
        end.

    Proposition copair_i1 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i1 = f.
    Proof.
      intros; extensionality a; unfold compose, copair, i1; reflexivity.
    Qed.

    Proposition copair_i2 : forall {X A B} (f : m A X) (g : m B X),
      compose (copair f g) i2 = g.
    Proof.
      intros; extensionality b; unfold compose, copair, i2; reflexivity.
    Qed.

    Proposition copair_iota_compose : forall {X A B} x,
      @copair X A B (compose x i1) (compose x i2) = x.
    Proof.
      intros; extensionality ab; unfold compose, copair, i1, i2.
      destruct ab as [a | b]; reflexivity.
    Qed.

    Include CocartesianStructureTheory SilentEventsBase.
    Include BifunctorTheory SilentEventsBase SilentEventsBase SilentEventsBase.
    Include SymmetricMonoidalStructureTheory SilentEventsBase.
  End Plus.

  Include CocartesianTheory SilentEventsBase.

End SilentEventsBicartesian.

Module SilEvents <: BicartesianCategory.
  Include SilentEventsBicartesian.

  Notation "⟨ a | b ⟩" := (Prod.sync a b) (at level 0).
  Notation "⟨ a | ⟩" := (Prod.sill a) (at level 0).
  Notation "⟨ | b ⟩" := (Prod.silr b) (at level 0).

  Definition SilF {A B : Type} (f : A -> B) : ⇑A -> ⇑B :=
    fun ev => 
      match ev with
      | 'a => '(f a)
      | ɛ => ɛ
      end.

  Module SilF <: Functor SET SET.
    
    Definition omap : Type -> Type := Sil.

    Definition fmap {A B : Type} : (A -> B) -> ⇑A -> ⇑B := SilF.
    
    Definition fmap_id :
      forall A, fmap (SET.id A) = SET.id (⇑A).
    Proof.
      intros. unfold fmap. extensionality ev.
      destruct ev; reflexivity.
    Qed.

    Definition fmap_compose : 
      forall {A B C} (g : B -> C) (f : A -> B),
        fmap (SET.compose g f) = SET.compose (fmap g) (fmap f).
    Proof.
      intros. unfold fmap. extensionality ev.
      destruct ev; reflexivity.
    Qed.

    Include FunctorTheory SET SET.
  End SilF.

  Definition ext {A B : Type} (f : A -> ⇑B) : ⇑A -> ⇑B :=
  fun ev =>
    match ev with
    | 'a => f a
    | ɛ => ɛ
    end.

  Module Ext <: FaithfulFunctor SilentEventsBase SET.
      Definition omap : Type -> Type := Sil.

      Definition fmap {A B : Type} : 
        (A -> ⇑B) -> ⇑A -> ⇑B := ext.

      Definition fmap_id :
        forall A, fmap (id A) = SET.id (⇑A).
      Proof.
        intros. unfold fmap, ext. extensionality ev.
        destruct ev; reflexivity.
      Qed.

      Definition fmap_compose : 
        forall {A B C} (g : B -> ⇑C) (f : A -> ⇑B),
          fmap (compose g f) = SET.compose (fmap g) (fmap f).
      Proof.
        intros. unfold fmap, ext, compose, SET.compose. extensionality ev.
        destruct ev as [a | ]; try reflexivity.
        destruct (f a) as [b | ]; reflexivity.
      Qed.

      Include FunctorTheory SilentEventsBase SET.

      Proposition faithful : forall {A B} 
        (f g : A -> ⇑B), ext f = ext g -> f = g. 
      Proof.
        intros. extensionality ev. unfold ext in H.
        apply (f_equal (fun h => h ('ev))) in H.
        exact H.
      Qed.

      Proposition ext_vis_eq : forall {A B}
        {f : A -> ⇑B} {a : A}, ext f 'a = f a.
      Proof.
        reflexivity.
      Qed.
    End Ext.

    Proposition unit_unique : forall x y : unit, x = y.
    Proof.
      destruct x; destruct y; reflexivity.
    Qed.

End SilEvents.