Require Export coqrel.LogicalRelations.
Require Import interfaces.ConcreteCategory.


(** * Partially ordered sets *)

(** ** Unbundled definitions *)

(** We use posets for multiple purposes which we want to keep
  separated as much as possible. For example, specification refinement
  orderings and the dcpos used to compute the semantics of iteration
  will sometime be separate orders although they are defined on the
  same carrier set. In order to still share definitions between these
  two applications, we first provide an unbundled version of
  order-delated definitions where the relation [R] involved is
  an unbundled parameter. *)

Class PartialOrder {P} (R : relation P) :=
  {
    po_preorder :: PreOrder R;
    po_antisym :: Antisymmetric P eq R;
  }.

Global Hint Mode PartialOrder ! - : typeclass_instances.

(** *** Suprema *)

Class IsSup `{PartialOrder} {I} (x : I -> P) (u : P) :=
  {
    sup_ub i : R (x i) u;
    sup_lub y : (forall i, R (x i) y) -> R u y;
  }.

Section SUP_PROPERTIES.
  Context `{Ppo : PartialOrder}.

  Lemma sup_unique {I} {x : I -> P} (u v : P) `{!IsSup x u} `{!IsSup x v} :
    u = v.
  Proof.
    apply antisymmetry.
    - apply sup_lub. intro. apply sup_ub.
    - apply sup_lub. intro. apply sup_ub.
  Qed.

  Lemma sup_at {I y u} `{Hu : !IsSup y u} (i : I) (x : P) :
    R x (y i) -> R x u.
  Proof.
    intros; etransitivity; eauto; apply sup_ub.
  Qed.

  Lemma sup_iff {I} (x : I -> P) {u : P} `{Hz : !IsSup x u} (y : P) :
    R u y <-> forall i, R (x i) y.
  Proof.
    split.
    - intros H i. etransitivity; eauto. apply sup_ub.
    - apply sup_lub.
  Qed.
End SUP_PROPERTIES.

(** *** Infima *)

Class IsInf `{PartialOrder} {I} (y : I -> P) (u : P) :=
  {
    inf_lb i : R u (y i);
    inf_glb x : (forall i, R x (y i)) -> R x u;
  }.

Section INF_PROPERTIES.
  Context `{Rpo : PartialOrder}.

  Lemma inf_unique {I} (x : I -> P) (u v : P) :
    IsInf x u ->
    IsInf x v ->
    u = v.
  Proof.
    intros Hu Hv.
    apply antisymmetry.
    - apply inf_glb. intro. apply inf_lb.
    - apply inf_glb. intro. apply inf_lb.
  Qed.

  Lemma inf_at {I x u} `{Hu : !IsInf x u} (i : I) (y : P) :
    R (x i) y -> R u y.
  Proof.
    intros; etransitivity; eauto. apply inf_lb.
  Qed.

  Lemma inf_iff {I} (y : I -> P) {u : P} `{Hu : !IsInf y u} (x : P) :
    R x u <-> forall i, R x (y i).
  Proof.
    split.
    - intros H i. etransitivity; eauto. apply inf_lb.
    - apply inf_glb.
  Qed.
End INF_PROPERTIES.

(** ** As extra structure for sets *)

(** The main role of posets in our development is as the core
  structure of refinement spaces. The name used in the semi-bundled
  version below for the ordering relation reflects this use. *)

Class Poset (P : Type) :=
  {
    ref : relation P;
    ref_po :: PartialOrder ref;
  }.

Module Poset <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_poset : Poset P.

  Global Hint Immediate structure_poset : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Apos: Poset A} `{Bpos: Poset B} (f : A -> B) :=
    morphism_monotonic :> Monotonic f (ref ++> ref).

  Global Instance id_mor `{Poset} :
    Morphism (fun x => x).
  Proof.
    firstorder.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{Poset A} `{Poset B} `{Poset C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    firstorder.
  Qed.

  Include ConcreteCategoryTheory.

End Poset.

Abbreviation poset := Poset.structured_set.

Declare Scope poset_scope.
Delimit Scope poset_scope with poset.
Bind Scope poset_scope with poset.

Declare Scope poselt_scope.
Delimit Scope poselt_scope with poselt.
Bind Scope poselt_scope with Poset.carrier.

Infix "<=" := ref.

(** * Pointed partial orders *)

(** A partial order with a least element. The [bot] of a DCPO and the
  [lbot] of a semilattice are instances, indexed by their respective
  orders. *)

Class Pointed {P} (R : relation P) `{!PartialOrder R} :=
  {
    bot : P;
    bot_lb : forall x, R bot x;
  }.

Global Hint Mode Pointed ! - - : typeclass_instances.

(** [bot] is a projection; keep [simpl] and [cbn] from unfolding it to the
  underlying supremum, so that lemmas stated with [bot] keep matching. *)
Arguments bot : simpl never.

Lemma bot_eq `{Pointed} (x : P) :
  R x bot -> x = bot.
Proof.
  intros Hx. apply antisymmetry; [exact Hx | apply bot_lb].
Qed.

(** * Strict maps *)

(** A map between pointed orders is strict when it preserves the least
  element. The orders are implicit; name them with [(RA := ...)] or
  [(RB := ...)] when a carrier has more than one pointed order. *)

Class Strict {A B} {RA : relation A} {RB : relation B}
    `{POA : !PartialOrder RA} `{POB : !PartialOrder RB}
    `{PA : !Pointed RA} `{PB : !Pointed RB} (f : A -> B) :=
  strict_bot : f bot = bot.

Lemma strict_lb {A B} {RA : relation A} {RB : relation B}
    `{!PartialOrder RA} `{!PartialOrder RB} `{!Pointed RA} `{!Pointed RB}
    (f : A -> B) `{!Strict (RA := RA) (RB := RB) f} (y : B) :
  RB (f bot) y.
Proof.
  rewrite (strict_bot (f := f)). apply bot_lb.
Qed.

Class PreContinuous {A B} {RA : relation A} {RB : relation B}
    `{POA : !PartialOrder RA} `{POB : !PartialOrder RB}
    `{PA : !Pointed RA} `{PB : !Pointed RB} (f : A -> B) :=
  {
    pc_mon :: Monotonic f (RA ++> RB);
    pc_strict :: Strict (RA := RA) (RB := RB) f;
  }.

Global Hint Mode PreContinuous - - - - - - - - ! : typeclass_instances.

Global Instance pc_id {A} {RA : relation A} `{!PartialOrder RA} `{!Pointed RA} :
  PreContinuous (RA := RA) (RB := RA) (fun a => a).
Proof.
  split.
  - intros x y Hxy. exact Hxy.
  - reflexivity.
Qed.

Global Instance pc_compose {A B C} {RA : relation A} {RB : relation B} {RC : relation C}
    `{!PartialOrder RA} `{!PartialOrder RB} `{!PartialOrder RC}
    `{!Pointed RA} `{!Pointed RB} `{!Pointed RC} (g : B -> C) (f : A -> B)
    `{!PreContinuous (RA := RB) (RB := RC) g} `{!PreContinuous (RA := RA) (RB := RB) f} :
  PreContinuous (RA := RA) (RB := RC) (fun a => g (f a)).
Proof.
  split.
  - intros x y Hxy. apply (pc_mon (f := g)), (pc_mon (f := f)), Hxy.
  - unfold Strict. rewrite (strict_bot (f := f)). apply (strict_bot (f := g)).
Qed.

Class PPoset (P : Type) :=
  {
    pref : relation P;
    pref_po : PartialOrder pref;
    pref_pointed : Pointed pref;
  }.

Global Existing Instance pref_po | 5.
Global Existing Instance pref_pointed | 12.

Module PPoset <: ConcreteCategory.

  Class Structure (P : Type) : Type :=
    structure_pposet : PPoset P.

  #[global] Typeclasses Transparent Structure.

  Global Hint Immediate structure_pposet : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Appo: PPoset A} `{Bppo: PPoset B} (f : A -> B) :=
    morphism_precont : PreContinuous (RA := pref) (RB := pref) f.

  Global Hint Immediate morphism_precont : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor `{PPoset} :
    Morphism (fun x => x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{PPoset A} `{PPoset B} `{PPoset C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.

End PPoset.
