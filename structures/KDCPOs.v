Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import interfaces.Functor.

Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalChoice.

(** ** KContinuity *)

(** 
  One might expect that joins, or choice operators in programming languages
  are Scott-continuous. 
  
  [sup_dsup {I} :: ScottContinuous true (lsup (L := L) (I := I));]
  
  It turns out there are subtle size issues that arise.
  The reality is that while finitary choice is Scott-continuous, contuinity 
  of non-deterministic choice will be relative to its size.
  
  One approach would be to require that if we want to have λ-joins, for a 
  regular ordinal λ, then we ask continuity only for λ-directed sets D 
  (every subset of size less than λ has an upper bound in D) of size at 
  most λ. While a theory of ordinals is already available in DCPOs.v, 
  we would constantly need to worry about sizes.

  An alternative approach that is more focused on fixpoints would be to
  require that joins for λ-non-determinism preserve λ-chains, essentially
  working with λ-CPOS.
  
  Instead, we postulate that our domains for non-determinism support 
  all cardinalities for choice. While this is a strong requirement, 
  we only ask for continuity conditions matching the cardinality of the join.
  As a result, we can take an index set as its own measure of size in 
  defining λ-directed sets.
**)

Class KDirected `{PartialOrder} (K : Type) {I} (x : I -> P) :=
  kdirected : forall (k : K -> I), exists u, forall i, R (x (k i)) (x u).

(** if [K] surjects onto [K'], every [K]-directed family is [K']-directed. *)
Lemma kdirected_surj `{PartialOrder} {K K'} (r : K -> K') (Hsurj : forall k', exists k, r k = k')
    {I} (x : I -> P) :
  KDirected K x -> KDirected K' x.
Proof.
  intros HK sel. destruct (HK (fun k => sel (r k))) as [u Hu].
  exists u. intros k'. destruct (Hsurj k') as [k <-]. exact (Hu k).
Qed.

(** Note that directedness is exactly bool-directedness *)

Global Instance kdirected_directed `{KDirected (K := bool)} : Directed x.
Proof.
  intros i j. pose (fun b : bool => if b then i else j) as f.
  destruct (kdirected f) as [u Hu].
  exists u.  split.
  apply (Hu true). apply (Hu false).
Qed.

(** Classically, as soon as [K] has two distinct elements, K-directedness
  implies directedness. *)

Lemma k_large_directed `{KDirected} (t s : K) :
  t <> s -> Directed x.
Proof.
  intros distinct i j.
  assert (Hsel : forall k : K, exists y : I0, (k = t /\ y = i) \/ (k <> t /\ y = j)).
  { intros k. destruct (classic (k = t)) as [-> | Hk].
    - exists i. left. auto.
    - exists j. right. auto. }
  destruct (choice _ Hsel) as [f Hf].
  destruct (kdirected f) as [u Hu].
  exists u. split.
  - specialize (Hu t). destruct (Hf t) as [[_ <-] | [Ht _]]; [exact Hu | contradiction].
  - specialize (Hu s). destruct (Hf s) as [[Hs _] | [_ <-]]; [congruence | exact Hu].
Qed.

(** *** Basic instances *)

(** We see a subtlety already with K-directedness. 
  When [K] is empty it turns out we are asking that for any empty subset of the 
  directed set, there must be an upper bound. Which makes the condition 
  [forall i, R (x (k i)) (x u)] vacuous. 
  Therefore the only requirement becomes the existence of [u], i.e. non-emptiness of [I]. *)
(** Because of this, the follow instance must first ensure that [K] is non-empty, so to 
  obtain the standard case of the empty set being directed. *)
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

(** Image through a monotonic function *)

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

(** K-Continuity is then analogous to Scott Continuity: we ask that the function 
be monotonic and that the image of a directed sup of a K-directed set must be
the directed sup of the image of the K-directed set. *)
(** A technicality in the definition below comes from the need to state that [x] is both
directed and K-directed. One issue is that [dsup] requires [x] to be directed. For any 
non-trivial K (i.e. with at least 2 elements) this follows from K-directedness. 
But rather than stating this condition, it is easier to state directedness directly, 
as such an instance can be derived in such cases. *)
Class KContinuous (K : Type) {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f: A -> B) :=
  {
    kc_lce :: Monotonic f (lce ++> lce);
    kc_lub {I} (x: I -> A) `{Dx: !Directed x} `{Kx: !KDirected (R := lce) K x} y:
      (forall i, lce (f (x i)) y) -> lce (f (dsup x)) y;
  }.

Global Instance kcont_id {K} {A} `{Adcpo : DCPO A} :
  KContinuous K (fun a => a).
Proof.
  split.
  - rauto.
  - intros. apply sup_lub. assumption.
Qed.

Global Instance kcont_compose {K} {A B C} `{DCPO A} `{DCPO B} `{DCPO C} :
  forall (g : B -> C) (f : A -> B),
    KContinuous K g ->
    KContinuous K f ->
    KContinuous K (fun a => g (f a)).
Proof.
  intros g f Hg Hf. split.
  - rauto.
  - intros I x Dx Kx y Hy.
    transitivity (g (dsup (fun i => f (x i)))).
    + apply kc_lce. apply kc_lub. assumption.
      intros i. apply (dsup_ub (fun i => f (x i))).
    + apply kc_lub. typeclasses eauto. assumption.
Qed.

Global Instance sc_kcont {K} {A B} `{DCPO A} `{DCPO B} (f : A -> B)
    `{Hf : !ScottContinuous true f} :
  KContinuous K f.
Proof.
  split.
  - apply sc_lce.
  - intros I x Dx Kx y Hy. apply sc_lub. assumption.
Qed.

(** ** K-DCPOS *)

(** It is easy to check that DCPOs and K-continuous functions assemble into a 
  category. *)

Module Type KArity.
  Parameter K : Type.
End KArity.

Module KDCPO (Ar : KArity) <: ConcreteCategory.
  Definition K := Ar.K.

  Class Structure (P : Type) : Type :=
    structure_dcpo : DCPO P.

  #[global] Typeclasses Transparent Structure.    

  Global Hint Immediate structure_dcpo : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f : A -> B) :=
    morphism_kcont : KContinuous K f.

  Global Hint Immediate morphism_kcont : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor `{DCPO} :
    Morphism (fun x => x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{DCPO A} `{DCPO B} `{DCPO C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.

End KDCPO.

(** ** Well-Sized DCPOS *)

(** A close relative of the notion of a K-DCPO that will be useful for us 
  is that of a well-sized DCPO *)
(** It consists of a DCPO [P] together with a index set [K] of size equal or 
  larger than [K] *)

Class WSDCPO (K : Type) (P : Type) :=
  {
    wsdcpo_dcpo :: DCPO P;
    wsdcpo_emb : K -> P; 
    wsdcpo_surj : forall p, exists k, wsdcpo_emb k = p;
  }.

(** These form a full subcategory of the category of DCPOs *)

Module WSDCPO (Ar : KArity) <: ConcreteCategory.
  Definition K := Ar.K.

  Class Structure (P : Type) : Type :=
    structure_wsdcpo : WSDCPO K P.

  Global Hint Immediate structure_wsdcpo : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Adcpo: WSDCPO K A} `{Bdcpo: WSDCPO K B} (f : A -> B) :=
    morphism_sc : ScottContinuous true f.

  Global Hint Immediate morphism_sc : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor {A} `{WSDCPO K A} :
    Morphism (fun x => x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{WSDCPO K A} `{WSDCPO K B} `{WSDCPO K C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.

End WSDCPO.

Module WSDCPO_KDCPO_Inclusion (Ar : KArity).

  Module C := WSDCPO Ar.
  Module D := KDCPO Ar.

  Module J <: Functor C D.

    Definition omap (X : C.t) : D.t :=
      D.mkt (C.carrier X).

    Definition fmap {A B} (f : C.m A B) : D.m (omap A) (omap B) :=
      D.mkm (A := omap A) (B := omap B) (C.apply _ _ f).

    Proposition fmap_id (X : C.t) :
      fmap (C.id X) = D.id (omap X).
    Proof.
      apply D.meq. reflexivity.
    Qed.

    Proposition fmap_compose {X Y Z} (g : C.m Y Z) (f : C.m X Y) :
      fmap (C.compose g f) = D.compose (fmap g) (fmap f).
    Proof.
      apply D.meq. reflexivity.
    Qed.

    Include FunctorTheory C D.

  End J.

  Module JFaithful <: Faithful C D J.
    Proposition faithful {A B} (f g : C.m A B) :
      J.fmap f = J.fmap g -> f = g.
    Proof.
      intros Hfg. apply C.meq. intros x.
      change (D.apply _ _ (J.fmap f) x = D.apply _ _ (J.fmap g) x).
      rewrite Hfg. reflexivity.
    Qed.
  End JFaithful.

End WSDCPO_KDCPO_Inclusion.

