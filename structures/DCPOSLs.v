Require Import LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.SemiLattices.
Require Import interfaces.Functor.

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
    dcposl_mor_sc :> ScottContinuous true f;
    dcposl_mor_sup :> SupContinuous f;
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

(* I could define the forgetful functor and use the derived Universal class from 
  Functor.v but that seems like adding more layers to the onion *)

Class IsFDCPOSL (P F : Type) `{Pdcpo : DCPO P} `{Fdcposl : DCPOSL F} :=
  {
    emb : P -> F;
    emb_sc :> ScottContinuous true emb;
    ext {D} `{Ddcposl : DCPOSL D} : (P -> D) -> F -> D;

    ext_mor {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f} :>
      DCPOSLMorphism (ext f);
    ext_ana {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f} :
      forall p, ext f (emb p) = f p;
    ext_unique {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f}
      (g : F -> D) `{Hg : !DCPOSLMorphism g} :
      (forall p, g (emb p) = f p) -> forall x, g x = ext f x;
  }.

Section EGLI_MILNER_DOMAIN.
  Context `{DCPO}.

  Definition set := P -> Prop.

  Record le (x y : set) :=
    {
      le_fw : forall (a : P), x a -> a <> bot -> exists (b : P) , y b /\ lce a b;
      le_bw : forall (b : P) , (y b) -> exists (a : P) , (x a) /\ lce a b
    }.

  Lemma le_div (x y : set) :
    le x y -> y bot -> x bot.
  Proof.
    intros Hle Hybot. destruct Hle as [Hfw Hbw].
    specialize (Hbw bot Hybot). destruct Hbw as [a [in_x lcea]].
    pose lce_bot_eq as Heq. specialize (Heq a lcea). rewrite <- Heq. exact in_x.
  Qed.

  Definition div_set x := x = bot.

  Lemma div_set_bot (x : set) : le div_set x.
  Proof.
    split.
    - intros a in_div_set neq_bot. 
      unfold div_set in in_div_set. rewrite in_div_set in *.
      contradiction neq_bot. reflexivity.
    - intros b in_x. exists bot. split. reflexivity. apply bot_lb.
  Qed.

  Global Instance le_preo :
    PreOrder le.
  Proof.
    split; split; firstorder.
    - exists a. split. assumption. reflexivity.
    - exists b. split. assumption. reflexivity.
    - specialize (le_fw1 a H2 H3). destruct le_fw1 as [b [in_y lce_a_b]].
      assert (b_neq_bot: b <> bot). 
        { intros b_eq_bot. rewrite b_eq_bot in lce_a_b. 
          apply lce_bot_eq in lce_a_b. contradiction lce_a_b. }
      specialize (le_fw0 b in_y b_neq_bot). destruct le_fw0 as [c [in_z lce_b_c]].
      exists c; split. assumption. etransitivity. exact lce_a_b. exact lce_b_c.
    - specialize (le_bw0 b H2). destruct le_bw0 as [a [in_y lce_a_b]].
      specialize (le_bw1 a in_y). destruct le_bw1 as [c [in_x lce_c_a]].
      exists c. split. assumption. etransitivity. apply lce_c_a. apply lce_a_b.
  Qed.