Require Import LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.SemiLattices.

Require Import PropExtensionality.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import ClassicalChoice.
Require Import ChoiceFacts.


(** * Dcpo-lattices *)

Class KDirected `{PartialOrder} (K : Type) {I} (x : I -> P) :=
  kdirected : forall (k : K -> I), exists u, forall i, R (x (k i)) (x u).

(** *** Basic instances *)

Global Instance Empty_set_kdirected `{PartialOrder} {K : Type} {inK : inhabited K} (x : Empty_set -> P) :
  KDirected K x.
Proof.
  intros k. destruct inK as [i]. destruct (k i).
Qed.

Global Hint Extern 1 (inhabited _) => repeat constructor : typeclass_instances.

Global Instance unit_set_kdirected `{PartialOrder} {K : Type} (x : unit -> P) :
  KDirected K x.
Proof.
  intros k. exists tt. intros i. destruct (k i). reflexivity.
Qed.

Lemma pair_kdirected `{PartialOrder} {K : Type} (x y : P) :
  R x y ->
  KDirected K (bool_rect _ y x).
Proof.
  intros Hxy k. exists true. cbn. intros i. 
  destruct (k i); cbn. reflexivity. assumption.
Qed.

Global Hint Extern 1 (KDirected _) =>
  eapply @pair_kdirected; assumption : typeclass_instances.

(** *** Image through a monotonic function *)

Lemma kdirected_apply {P Q R S} {K} (f : P -> Q) {I} (x : I -> P) :
  forall HR : @PartialOrder P R,
  forall HQ : @PartialOrder Q S,
  Monotonic f (R ++> S) ->
  KDirected K x ->
  KDirected K (fun i => f (x i)).
Proof.
  intros HR HQ Hf Hx k. red in Hf.
  specialize (Hx k). destruct Hx as [u Hu].
  exists u. intros i. specialize (Hu i).
  rauto.
Qed.

Global Hint Extern 5 (KDirected _ (fun i => ?f (?x i))) =>
  eapply @kdirected_apply : typeclass_instances.

Class KContinuous (K : Type) {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f: A -> B) :=
  {
    kc_lce :> Monotonic f (lce ++> lce);
    kc_lub {I} (x: I -> A) `{Dx: !Directed x} `{Kx: !KDirected (R := lce) K x} y:
      (forall i, lce (f (x i)) y) -> lce (f (dsup x)) y;
  }.

(** A dcpo-semilattice is a set equipped independently with
  both the structure of a dcpo and that of a semilattice.
  Structures of this kind are mentioned for example
  in §6.2 of Abramsky and Jung's domain theory textbook,
  which discusses various forms of powerdomains.

  For our purposes, the specific structures we combine are:
  - pointed dcpos and strict Scott-continuous functions between them,
    representing spaces of potentially non-terminating computations, and
  - semilattices lattices, representing computation spaces
    with different kinds of nondeterministic choices.

  Note that both structures involve a partial order, least element and
  supremum operations. In fact, every semilattice is a dcpo, and
  every sup-preserving function is strict Scott-continuous.
  However, a dcpo-semilattice provides two distinct partial orderings
  of its carrier set, which may or may not have anything to do with
  each other. *)

Class DCPOSL (L : Type) :=
  {
    dcposl_dcpo :> DCPO L;
    dcposl_sl :> SemiLattice L;
    (** 
      Naively, one might expect that the join be a Scott-continuous function:
      `
        sup_dsup {I} :> ScottContinuous true (lsup (L := L) (I := I));
      `
      However, while this is reasonable to expect from finitary joins, it 
      is no longer true once we want to compute countable joins.
      
      One approach would be to require that if we want to have λ-joins, for a 
      regular ordinal λ, then we ask continuity only for λ-directed sets D 
      (every subset of size less than λ has an upper bound in D) of size at 
      most λ. While a theory of ordinals is already available in DCPOs.v, 
      we would constantly need to worry about sizes.

      An alternative approach that is more focused on fixpoints would be to
      require that joins for λ-non-determinism preserve λ-chains, essentially
      working with λ-CPOS.
      
      Instead, we request that λ-joins be λ-continuous.
    **)
    sup_kcont {K} :> KContinuous K (lsup (L := L) (I := K));
  }.

Class DCPOSLMorphism {A B} `{Adcposl: DCPOSL A} `{Bdcposl: DCPOSL B} (f : A -> B) :=
  {
    dcposl_mor_sc :> DCPO.Morphism f;
    dcposl_mor_sup :> SLat.Morphism f;
  }.

Module DCPOSL <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_dcposl : DCPOSL P.

  Global Hint Immediate structure_dcposl : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Adcposl: DCPOSL A} `{Bdcposl: DCPOSL B} (f : A -> B) :=
    morphism_dcposl : DCPOSLMorphism f.

  Global Hint Immediate morphism_dcposl : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor `{DCPOSL} :
    Morphism (fun x => x).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{DCPOSL A} `{DCPOSL B} `{DCPOSL C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    intros; split; typeclasses eauto. 
  Qed.

  Include ConcreteCategoryTheory.

End DCPOSL.
