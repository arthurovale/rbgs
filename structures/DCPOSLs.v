Require Import coqrel.LogicalRelations.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.SemiLattices.
Require Import structures.KDCPOs.
Require Import structures.DCPOExtra.

Require Import Stdlib.Program.Program.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalChoice.

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.

(** * DCPO-Semilattices for Non-Determinism *)

(** ** DCPO-Semilattice Deifinition *)

(** A dcpo-semilattice is a set equipped independently with
  both the structure of a dcpo and that of a semilattice.
  Structures of this kind are mentioned for example
  in §6.2 of Abramsky and Jung's domain theory textbook,
  which discusses various forms of powerdomains.

  For our purposes, the specific structures we combine are:
  - pointed dcpos and strict Scott-continuous functions between them,
    representing spaces of potentially non-terminating computations, and
  - semilattices, representing computation spaces
    with different kinds of nondeterministic choices.

  Note that both structures involve a partial order, least element and
  supremum operations. In fact, every semilattice is a dcpo, and
  every sup-preserving function is strict Scott-continuous.
  However, a dcpo-semilattice provides two distinct partial orderings
  of its carrier set, which may or may not have anything to do with
  each other. *)

Class DCPOSL (L : Type) :=
  {
    dcposl_dcpo :: DCPO L;
    dcposl_sl :: SemiLattice L;
    sup_kcont {K} :: KContinuous K (lsup (L := L) (I := K));
  }.

(** The join order of a semilattice is pointed by [lbot]. It gets a low
  priority so that an unannotated [bot] on a DCPOSL means the [lce] bottom. *)
Global Instance sl_pointed `{SemiLattice} : Pointed ref | 10 :=
  {| bot := lbot; bot_lb := lbot_lb |}.

(** The [kc_lce] component of [sup_kcont] in pointwise form *)
Lemma lsup_mon `{DCPOSL} {K} (u v : K -> L) :
  (forall k, lce (u k) (v k)) -> lce (lsup u) (lsup v).
Proof.
  intros Huv. apply (kc_lce (f := lsup (I := K))). exact Huv.
Qed.

(** Joins in a DCPOSL are convex with respect to [lce]. An element lying
  [u] and [w], w.r.t. [lce], is below, w.r.t. [ref], any common upper bound of [u] and [w]. *)
Lemma lsup_lce_between `{DCPOSL} (u v w y : L) :
  lce u v -> lce v w -> ref u y -> ref w y -> ref v y.
Proof.
  intros Huv Hvw Huy Hwy.
  pose (g := fun o : option bool =>
    match o with None => u | Some true => v | Some false => w end).
  pose (g' := fun o : option bool =>
    match o with None => u | Some true => w | Some false => w end).
  pose (g'' := fun o : option bool =>
    match o with None => u | Some true => u | Some false => w end).
  assert (Hg'g'' : lsup g' = lsup g'').
  { apply (antisymmetry (R := ref)); apply sup_lub; intros [[|]|]; unfold g', g''; cbn.
    - apply (sup_at (Some false)). reflexivity.
    - apply (sup_at (Some false)). reflexivity.
    - apply (sup_at None). reflexivity.
    - apply (sup_at None). reflexivity.
    - apply (sup_at (Some false)). reflexivity.
    - apply (sup_at None). reflexivity. }
  assert (Hg : lsup g = lsup g').
  { apply (antisymmetry (R := lce)).
    - apply lsup_mon. intros [[|]|]; unfold g, g'; cbn; [assumption | reflexivity | reflexivity].
    - rewrite Hg'g''. apply lsup_mon. intros [[|]|]; unfold g, g''; cbn; [assumption | reflexivity | reflexivity]. }
  transitivity (lsup g).
  - apply (sup_at (Some true)). reflexivity.
  - rewrite Hg. apply sup_lub. intros [[|]|]; unfold g'; cbn; assumption.
Qed.

(** ** Dependent products of DCPOSLs *)

Section FORALL_DCPOSL.
  Context {I} {L : I -> Type} `{Ldcposl : forall i : I, DCPOSL (L i)}.

  Local Instance forall_ref_po :
    @PartialOrder (forall i, L i) (forallr - @ i, ref).
  Proof.
    split.
    - split.
      + intros x i. reflexivity.
      + intros x y z Hxy Hyz i. etransitivity; eauto.
    - intros x y Hxy Hyx.
      apply functional_extensionality_dep. intros i.
      apply (antisymmetry (R := ref)); [apply Hxy | apply Hyx].
  Qed.

  Local Instance forall_poset : Poset (forall i, L i) :=
    {
      ref := forallr - @ i, ref;
    }.

  Local Obligation Tactic := idtac.

  Global Program Instance forall_sl : SemiLattice (forall i, L i) :=
    {
      cdl_poset := forall_poset;
      lsup J x := fun i => lsup (fun j => x j i);
    }.
  Next Obligation.
    intros J u. split.
    - intros j i. apply (sup_ub (IsSup := lsup_sup (fun j => u j i)) j).
    - intros y Hy i. apply (sup_lub (IsSup := lsup_sup (fun j => u j i))). intros j. apply (Hy j i).
  Qed.

  (** Projecting a family of functions at a point preserves directedness. *)

  Lemma forall_directed_at {J} (x : J -> forall i, L i) `{Dx : !Directed (R := lce) x} (i : I) :
    Directed (R := lce) (fun j => x j i).
  Proof.
    intros j j'. destruct (Dx j j') as [u [H1 H2]]. exists u. split; [apply H1 | apply H2].
  Qed.

  Lemma forall_kdirected_at {K J} (x : J -> forall i, L i) `{Kx : !KDirected (R := lce) K x} (i : I) :
    KDirected (R := lce) K (fun j => x j i).
  Proof.
    intros sel. destruct (Kx sel) as [u Hu]. exists u. intros k. apply (Hu k).
  Qed.

  Global Program Instance forall_dcposl : DCPOSL (forall i, L i) :=
    {
      dcposl_dcpo := _;
      dcposl_sl := forall_sl;
    }.
  Next Obligation.
    intros K. split.
    - intros x y Hxy i. apply lsup_mon. intros k. apply (Hxy k i).
    - intros J x Dx Kx y Hy i.
      (* the family of components at [i] *)
      assert (Dx' : Directed (R := lce) (fun j k => x j k i)).
      { intros j j'. destruct (Dx j j') as [u [H1 H2]]. exists u.
        split; intros k; [apply (H1 k i) | apply (H2 k i)]. }
      assert (Kx' : KDirected (R := lce) K (fun j k => x j k i)).
      { intros sel. destruct (Kx sel) as [u Hu]. exists u. intros k k'. apply (Hu k k' i). }
      (* the two sides agree up to the directedness proof inside [dsup] *)
      replace (lsup (dsup x) i) with (lsup (dsup (fun j k => x j k i))).
      + apply (kc_lub (f := lsup (I := K)) (fun j k => x j k i)). intros j. apply (Hy j i).
      + cbn. f_equal. apply functional_extensionality. intros k.
        f_equal. apply proof_irrelevance.
  Qed.
End FORALL_DCPOSL.

(** As for [forall_dcpo], the goal must syntactically be a product. The
  instances registered automatically by [Global Instance] are removed, since
  they would unify an unknown carrier with a product. *)
#[global] Remove Hints forall_sl forall_dcposl : typeclass_instances.
Global Hint Extern 1 (SemiLattice (forall i, _)) =>
  lazymatch goal with |- SemiLattice (forall _, _) => eapply @forall_sl end : typeclass_instances.
Global Hint Extern 1 (DCPOSL (forall i, _)) =>
  lazymatch goal with |- DCPOSL (forall _, _) => eapply @forall_dcposl end : typeclass_instances.

(** A morphism of DCPOSLs is then a function that is simultaneously
  (strict) Scott cotinuous on the DCPO structure and a semilattice homomorphism 
  on the semilattice structure *)

Class DCPOSLMorphism K {A B} `{Adcposl: DCPOSL A} `{Bdcposl: DCPOSL B} (f : A -> B) :=
  {
    dcposl_mor_kcont :: KContinuous K f;
    dcposl_mor_sup :: SupContinuous f;
  }.

(** It is easy to check this does assemble into a category *)

Module DCPOSL (Ar : KArity) <: ConcreteCategory.

  Definition K := Ar.K.

  Class Structure (P : Type) : Type :=
    structure_dcposl : DCPOSL P.

  Global Hint Immediate structure_dcposl : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Adcposl: DCPOSL A} `{Bdcposl: DCPOSL B} (f : A -> B) :=
    morphism_dcposl : DCPOSLMorphism K f.

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

(** ** The Egli-Milner Power Domain *)

(** We define a generalization of the usual Egli-Milner powerdomain *)
(** It generalizes it in that it allows for the empty set *)
(** This results in small modifications around checking for the presence of [bot] *)

(** Note that typically, the Egli-Milner construction below will not be a DCPOSL.
For an arbitrary [DCPO P] it is necessary to perform some kind of completion over
the structure defined below. Our hope is to work with simple enough DCPOs where
the structure below will in fact not only be a DCPOSL but also a free DCPOSL. *)

(** The EM order is not even a partial order for arbitrary subsets of P,
  as it fails to satisfy antisymmetry *)
(** It is easy to check that the class of subsets for which EM becomes
  a partial order is exactly the convex sets. *)

Record convex_set (P : Type) {R : relation P} `{!PartialOrder R} :=
  {
    mem :> P -> Prop;
    convexity : forall a b c, mem a -> mem c -> R a b -> R b c -> mem b;
  }.

Arguments mem {_ _ _} _ _.
Arguments convexity {_ _ _} _ _ _ _.

Section CONVEX_SETS.
  Context `{PartialOrder}.

  (** Extensional equality for convex sets *)
  Lemma convex_set_ext (x y : convex_set P) :
    (forall a, x a <-> y a) -> x = y.
  Proof.
    intros Hxy. destruct x as [x Hx], y as [y Hy]. cbn in *.
    cut (x = y). { intro. subst. f_equal. apply proof_irrelevance. }
    apply functional_extensionality. intro a.
    apply propositional_extensionality. apply Hxy.
  Qed.

  (** *** Semilattice Structure *)

  (** The order is just set inclusion *)
  Definition incl (x y : convex_set P) := forall a, x a -> y a. 

  Global Instance incl_po : PartialOrder incl.
  Proof.
    split. split; firstorder.
    intros x y incl_x_y incl_y_x. apply convex_set_ext.
    firstorder.
  Qed.

  Global Instance convex_poset : Poset (convex_set P) :=
  {
    ref := incl;
  }.

  (** Joins are given by convex unions, so first we define the usual union *)
  Definition union {I} (x : I -> (P -> Prop)) (a : P) := exists i, x i a.

  (** **** Convex Hull *)

  (** A key operation for the EM powerdomain is the convex hull operation. *)
  (** The convex hull operator is the smallest convex set including the original set *)

  Definition chull_mem (x : P -> Prop) (b : P) :=
    exists a c , x a /\ x c /\ R a b /\ R b c.

  Lemma chull_convexity (x : P -> Prop) :
    forall a b c, chull_mem x a -> chull_mem x c -> R a b -> R b c -> chull_mem x b.
  Proof.
    intros a b c mem_a mem_c lce_a_b lce_b_c.
    destruct mem_a as [a' [a'' [in_x_a' [in_x_a'' [lce_a'_a lce_a_a'']]]]].
    destruct mem_c as [c' [c'' [in_x_c' [in_x_c'' [lce_c'_c lce_c_c'']]]]].
    exists a'. exists c''. repeat (try split); try assumption.
    transitivity a; assumption. transitivity c; assumption.
  Qed.

  Definition chull (x : P -> Prop) : convex_set P := 
  {|
    mem := chull_mem x;
    convexity := chull_convexity x;
  |}.

  (** The convex hull is a closure operator *)

  Lemma chull_extensive (x : P -> Prop) : forall a, x a -> chull x a.
  Proof.
    intros a in_x. 
    exists a. exists a. repeat (try split); try assumption; try reflexivity.
  Qed.

  Lemma chull_convex_id (x : convex_set P) : chull x = x.
  Proof.
    apply convex_set_ext. intros b. split.
    - intros [a [c [ax [cx [ab bc]]]]]. apply (convexity x a b c); assumption.
    - intros. apply chull_extensive. assumption.
  Qed.

  Lemma chull_idem (x : P -> Prop) : chull (chull x) = chull x.
  Proof.
    apply convex_set_ext. intros b; split.
    - intros Hchull. 
      destruct Hchull as [a [c [chull_a [chull_c [lce_a_b lce_b_c]]]]].
      destruct chull_a as [a' [a'' [chull_a' [chull_a'' [lce_a'_a lce_a_a'']]]]].
      destruct chull_c as [c' [c'' [chull_c' [chull_c'' [lce_c'_a lce_a_c'']]]]].
      exists a'. exists c''.  repeat (try split); try assumption.
      transitivity a; assumption. transitivity c; assumption.
    - intros Hchull.
      destruct Hchull as [a [c [chull_a [chull_c [lce_a_b lce_b_c]]]]].
      exists a. exists c. repeat (try split); try assumption.
      all: apply chull_extensive; assumption.
  Qed.

  Lemma chull_mon (x : P -> Prop) (y : P -> Prop) : 
    (forall a, x a -> y a) -> incl (chull x) (chull y).
  Proof.
    intros incl_x_y. intros b [a [c [in_x_a [in_x_c [lce_a_b lce_b_c]]]]]. 
    exists a. exists c. repeat (try split); try assumption.
    all: apply incl_x_y; assumption.
  Qed.

  (** **** Joins *)

  (** Joins are given by the convex union *)
  
  Definition convex_sup {I} (x : I -> convex_set P) : convex_set P := chull (union x).

  (** Note that no assumption on the DCPO is required for the semilattice structure *)

  Global Program Instance convex_sl : SemiLattice (convex_set P) :=
    {
      lsup I x := convex_sup x;
    }.
  Next Obligation.
    split.
    - intros i a in_u_i. apply chull_extensive. exists i. assumption.
    - intros y incl_u_y b in_csup. 
      destruct in_csup as [a [c [in_union_a [in_union_c [lce_a_b lce_b_c]]]]].
      apply (convexity y a b c); auto.
      destruct in_union_a as [i in_u]. apply (incl_u_y i). assumption.
      destruct in_union_c as [i in_u]. apply (incl_u_y i). assumption.
  Qed.

End CONVEX_SETS.


Section EGLI_MILNER_DOMAIN.
  Context `{DCPO}.

  (** *** Candidate DCPO Structure *)

  Record em_le (x y : convex_set P) :=
    {
      (** fw: no information is dropped, if a in x then it evolves to some b in y *)
      (** different from standard EM, we consider bot and do not enforce fw for it *)
      em_le_fw : forall (a : P), x a -> a <> bot -> exists (b : P) , y b /\ lce a b;
      (** anything in y needs to be justified by something in x *)
      em_le_bw : forall (b : P) , y b -> exists (a : P) , x a /\ lce a b
    }.

  (** bot can only be removed forwardly *)
  Lemma le_div (x y : convex_set P) :
    em_le x y -> y bot -> x bot.
  Proof.
    intros Hle Hybot. destruct Hle as [Hfw Hbw].
    specialize (Hbw bot Hybot). destruct Hbw as [a [in_x lcea]].
    pose lce_bot_eq as Heq. specialize (Heq a lcea). rewrite <- Heq. exact in_x.
  Qed.

  (** the bottom element for em_le is {div} *)
  Program Definition div_set : convex_set P :=
  {|
    mem x := x = bot;
  |}.
  Next Obligation.
    apply lce_bot_eq; assumption.
  Defined.

  Lemma div_set_bot (x : convex_set P) : em_le div_set x.
  Proof.
    split.
    - intros a in_div_set neq_bot. 
      unfold div_set in in_div_set. rewrite in_div_set in *.
      contradiction neq_bot. reflexivity.
    - intros b in_x. exists bot. split. reflexivity. apply bot_lb.
  Qed.

  (** For convex sets, [em_le] is a partial order *)

  Global Instance le_preo :
    PreOrder em_le.
  Proof.
    split; split.
    - intros a ? ?. exists a. split. assumption. reflexivity.
    - intros a ?. exists a. split. assumption. reflexivity.
    - intros a in_x neq_bot. destruct H0 as [fw_x_y _]. destruct H1 as [fw_y_z _].
      specialize (fw_x_y a in_x neq_bot). destruct fw_x_y as [b [in_y lce_a_b]].
      pose proof (lce_bot_neq a b lce_a_b neq_bot) as b_neq_bot.
      specialize (fw_y_z b in_y b_neq_bot). destruct fw_y_z as [c [in_z lce_b_c]].
      exists c; split. assumption. etransitivity. exact lce_a_b. exact lce_b_c.
    - intros c in_z. destruct H0 as [_ bw_x_y]. destruct H1 as [_ bw_y_z]. 
      specialize (bw_y_z c in_z). destruct bw_y_z as [b [in_y lce_b_c]].
      specialize (bw_x_y b in_y). destruct bw_x_y as [a [in_x lce_a_b]].
      exists a. split. assumption. transitivity b; assumption.
  Qed.

  Lemma em_le_incl (x y : convex_set P) :
    em_le x y -> em_le y x -> incl x y.
  Proof.
    intros Hxy Hyx a Hxa.
    destruct (classic (a = bot)) as [-> | Ha].
    - apply (le_div y x Hyx Hxa).
    - destruct Hxy as [fw_xy _], Hyx as [_ bw_yx].
      destruct (fw_xy a Hxa Ha) as [b [Hyb Hab]].
      destruct (bw_yx a Hxa) as [c [Hyc Hca]].
      apply (convexity y c a b); assumption.
  Qed.

  Global Instance em_le_antisym :
    Antisymmetric _ eq em_le.
  Proof.
    intros x y le_x_y le_y_x. 
    apply convex_set_ext. 
    intros a; split; apply em_le_incl; assumption.
  Qed.

  Global Instance em_le_po :
    PartialOrder em_le.
  Proof.
    split; typeclasses eauto.
  Qed.

  (** The EM order is pointed by [div_set], with no further assumption on [P]. *)
  Global Instance em_pointed : Pointed em_le :=
    {| bot := div_set; bot_lb := div_set_bot |}.

  (** the supremum is the set of all elements that are eventually always present *)
  (** bot is only present if it never gets removed *)
  Definition dsup_em_mem {I} (x : I -> convex_set P) `{Hx: !Directed x} : P -> Prop :=
    fun a => (a = bot -> forall i, x i bot) /\
             (a <> bot -> exists i, forall j, em_le (x i) (x j) -> x j a).

  (** A technicality is that the bot case follows from the non-bot condition 
    as long as [I] is non-empty. *)
  Lemma dsup_em_mem_inhabited {I} (x : I -> convex_set P) `{Hx: !Directed x} `{inhabited I} : 
    forall a, dsup_em_mem x a <-> exists i, forall j, em_le (x i) (x j) -> x j a.
  Proof.
    intros a. split. 
    - destruct (classic (a = bot)) as [-> | Ha]; firstorder.
    - intros [i0 mem]. split. 2: firstorder.
      intros -> i. destruct (Hx i0 i) as [j [em_le_i0_j em_le_i_j]].
      specialize (mem _ em_le_i0_j). eapply le_div. apply em_le_i_j. assumption.
  Qed.

  (** Convexity follows straight-forwardly *)
  Lemma dsup_em_convexity {I} (x : I -> convex_set P) `{Hx: !Directed x} : 
    forall a b c, dsup_em_mem x a -> dsup_em_mem x c -> lce a b -> lce b c -> dsup_em_mem x b.
  Proof.
    intros a b c [Ha_bot Ha] [Hc_bot Hc] lce_a_b lce_b_c.
    split. 
    - intros ->. apply Ha_bot. apply lce_bot_eq. assumption.
    - intros b_neq_bot.
      pose proof (lce_bot_neq b c lce_b_c b_neq_bot) as c_neq_bot.
      destruct (Hc c_neq_bot) as [j Hj].
      destruct (classic (a = bot)) as [-> | a_neq_bot].
      + (* bot is in every x i *)
        exists j. intros k em_le_j_k.
        apply (convexity (x k) bot b c); auto.
      + destruct (Ha a_neq_bot) as [i Hi].
        destruct (Hx i j) as [k [em_le_i_k em_le_j_k]].
        exists k. intros k' em_le_k_k'.
        apply (convexity (x k') a b c); auto.
        apply Hi. transitivity (x k); assumption.
        apply Hj. transitivity (x k); assumption.
  Qed.

  Definition dsup_em {I} (x : I -> convex_set P) `{Hx: !Directed x} : convex_set P := 
  {|
    mem := dsup_em_mem x;
    convexity := dsup_em_convexity x;
  |}.

  (** Now, some helpful lemmas about em_le *)

  (** If a finite set of elements are all eventually always absent, then there is 
  a stage when they are all simultaneously absent. *)
  Lemma eventually_absent_all {I} (x : I -> convex_set P) `{Hx : !Directed x} `{inhabited I} (b : P) (l : list P) :
    (forall a, In a l -> lce a b -> exists i, forall j, em_le (x i) (x j) -> ~ x j a) ->
    exists i, forall j, em_le (x i) (x j) -> forall a, In a l -> lce a b -> ~ x j a.
  Proof.
    destruct inhabited0 as [i0].
    induction l as [| a l IH]; intros Habs.
    - exists i0. intros j _ a [].
    - destruct (IH (fun a' Hin Hab => Habs a' (or_intror Hin) Hab)) as [i1 Hi1].
      destruct (classic (lce a b)) as [Hab | Hab].
      + destruct (Habs a (or_introl eq_refl) Hab) as [ia Hia].
        destruct (Hx i1 ia) as [k [Hk1 Hka]].
        exists k. intros j Hkj a' [<- | Hin] Ha'b.
        * apply Hia. transitivity (x k); assumption.
        * exact (Hi1 j (transitivity Hk1 Hkj) a' Hin Ha'b).
      + exists i1. intros j Hj a' [<- | Hin] Ha'b.
        * contradiction.
        * exact (Hi1 j Hj a' Hin Ha'b).
  Qed.

  Lemma cofinal_always_eventually_present {I} (x : I -> convex_set P) 
   `{!Directed x} `{inhabited I} (a : P) :
    (forall i, exists j, em_le (x i) (x j) /\ x j a) ->
    exists i, forall j, em_le (x i) (x j) -> x j a.
  Proof.
    intros Hcof. destruct inhabited0 as [i0].
    destruct (classic (a = bot)) as [-> | H_neq_bot].
    - (* bot propagates backward, so it is present at every stage *)
      exists i0. intros j _. destruct (Hcof j) as [k [Hjk Hk]]. exact (le_div _ _ Hjk Hk).
    - destruct (Hcof i0) as [i [em_le_i0_i  a_in_i]].
      exists i. intros j Hij.
      destruct (Hcof j) as [k [Hjk Hk]].
      destruct (em_le_fw _ _ Hij a a_in_i H_neq_bot) as [e [Hje Hae]].
      destruct (em_le_bw _ _ Hjk a Hk) as [d [Hjd Hda]].
      apply (convexity (x j) d a e); assumption.
  Qed.

  (** *** Attained suprema *)

  (** Once an element has appeared in a directed family and then disappeared,
    it never comes back *)
  Lemma em_absent_forever {J} (x : J -> convex_set P) (p : P) j0 j1 :
    em_le (x j0) (x j1) -> x j0 p -> ~ x j1 p ->
    forall j, em_le (x j1) (x j) -> ~ x j p.
  Proof.
    intros H01 Hp0 Hp1 j H1j Hpj.
    destruct (classic (p = bot)) as [-> | Hp].
    - apply Hp1. exact (le_div _ _ H1j Hpj).
    - destruct (em_le_fw _ _ H01 p Hp0 Hp) as [p' [Hp' Hpp']].
      destruct (em_le_bw _ _ H1j p Hpj) as [q [Hq Hqp]].
      apply Hp1. apply (convexity (x j1) q p p'); assumption.
  Qed.

  (** Membership of every element eventually settles, to its value in [dsup_em]. *)
  Lemma em_settles {J} (x : J -> convex_set P) `{Hx : !Directed x} `{inhabited J} (p : P) :
    exists i, forall j, em_le (x i) (x j) -> (x j p <-> dsup_em_mem x p).
  Proof.
    destruct inhabited0 as [j0].
    destruct (classic (dsup_em_mem x p)) as [Hin | Hout].
    - (* eventually always present *)
      pose proof Hin as [Hbot Hnbot].
      destruct (classic (p = bot)) as [-> | Hp].
      + exists j0. intros j _. split; [intros _; exact Hin | intros _; apply Hbot; reflexivity].
      + destruct (Hnbot Hp) as [i Hi]. exists i. intros j Hij.
        split; [intros _; exact Hin | intros _; exact (Hi j Hij)].
    - (* eventually always absent *)
      destruct (classic (exists j, x j p)) as [[j1 Hj1] | Hnever].
      + destruct (classic (p = bot)) as [-> | Hp].
        * assert (exists i, ~ x i bot) as [i Hi].
          { apply NNPP. intros Hno. apply Hout. split.
            - intros _ i. apply NNPP. intros Hn. apply Hno. exists i. exact Hn.
            - intros Hc. contradiction Hc. reflexivity. }
          exists i. intros j Hij. split.
          -- intros Hj. exfalso. apply Hi. exact (le_div _ _ Hij Hj).
          -- intros Hd. contradiction.
        * assert (exists j2, em_le (x j1) (x j2) /\ ~ x j2 p) as [j2 [H12 Hj2]].
          { apply NNPP. intros Hno. apply Hout. split.
            - intros Hc. contradiction.
            - intros _. exists j1. intros j Hj. apply NNPP. intros Hn. apply Hno. exists j. auto. }
          exists j2. intros j H2j. split.
          -- intros Hj. exfalso. exact (em_absent_forever x p j1 j2 H12 Hj1 Hj2 j H2j Hj).
          -- intros Hd. contradiction.
      + exists j0. intros j _. split.
        * intros Hj. exfalso. apply Hnever. exists j. exact Hj.
        * intros Hd. contradiction.
  Qed.

  (** A [P]-directed family in the EM domain attains its supremum. *)
  Lemma dsup_em_attained {J} (x : J -> convex_set P) `{Hx : !Directed x} `{inhabited J}
      `{Kx : !KDirected (R := em_le) P x} :
    exists u, x u = dsup_em x.
  Proof.
    destruct (choice (fun p i => forall j, em_le (x i) (x j) -> (x j p <-> dsup_em_mem x p))
                     (em_settles x (inhabited0 := inhabited0))) as [k Hk].
    destruct (Kx k) as [u Hu].
    exists u. apply convex_set_ext. intros p. cbn.
    exact (Hk p u (Hu p)).
  Qed.

  Lemma dsup_em_empty {J} (x : J -> convex_set P) `{Hx : !Directed x} :
    ~ inhabited J -> dsup_em x = div_set.
  Proof.
    intros Hemp. apply convex_set_ext. intros a. cbn. split.
    - intros [_ Hnbot]. apply NNPP. intros Ha.
      destruct (Hnbot Ha) as [i _]. apply Hemp. exact (inhabits i).
    - intros ->. split.
      + intros _ i. exfalso. apply Hemp. exact (inhabits i).
      + intros Hc. contradiction Hc. reflexivity.
  Qed.

  Lemma dsup_em_kdirected_issup {J} (x : J -> convex_set P) `{Hx : !Directed x}
      `{Kx : !KDirected (R := em_le) P x} :
    IsSup (R := em_le) x (dsup_em x).
  Proof.
    destruct (classic (inhabited J)) as [Hinh | Hemp].
    - destruct (choice (fun p i => forall j, em_le (x i) (x j) -> (x j p <-> dsup_em_mem x p))
                       (em_settles x (inhabited0 := Hinh))) as [k Hk].
      destruct (Kx k) as [u Hu].
      assert (Hstable : forall v, em_le (x u) (x v) -> x v = x u).
      { intros v Huv. apply convex_set_ext. intros p.
        assert (Hv : em_le (x (k p)) (x v)) by (transitivity (x u); [apply Hu | exact Huv]).
        split; intros Hp.
        - apply (Hk p u (Hu p)), (Hk p v Hv), Hp.
        - apply (Hk p v Hv), (Hk p u (Hu p)), Hp. }
      assert (Hdsup : dsup_em x = x u).
      { apply convex_set_ext. intros p. cbn. symmetry. exact (Hk p u (Hu p)). }
      rewrite Hdsup. split.
      + intros i. destruct (directed i u) as [v [Hiv Huv]].
        rewrite <- (Hstable v Huv). exact Hiv.
      + intros y Hy. apply Hy.
    - rewrite (dsup_em_empty x Hemp). split.
      + intros i. exfalso. apply Hemp. exact (inhabits i).
      + intros y _. apply div_set_bot.
  Qed.

  (* Unfortunately, whether this notion of powerdomain 
    is in fact a DCPOSL is quite subtle *)
  (* So instead, we show that under the condtion that the DCPO is finitary 
    it is so. *)
  
  Global Program Instance em_dcpo `{!Finitary (R := lce)} : DCPO (convex_set P) := 
  {|
    lce := em_le;
    dsup := @dsup_em;
  |}.
  Next Obligation.
    split.
    (* upper bound *)
    - split.
      (* fw *)
      intros a in_x_i_a neq_bot.
      (* we define a set S of all elements in stages after i such that a <= b *)
      pose (S := fun b => (exists j, em_le (x i) (x j) /\ x j b /\ lce a b)).
      (* S is non-empty as a is in S *)
      assert (inS: S a).
      { exists i. split. reflexivity. split. assumption. reflexivity. }
      (* since the DCPO is finitary this set has a maximal element *)
      assert (Smax: exists b, S b /\ forall b', S b' -> lce b b' -> b = b').
      { apply finitary_DCPO_maximal. exists a. apply inS. }
      destruct Smax as [b [binS Hbmax]].
      destruct binS as [ib [em_le_i_ib [in_x_ib lce_a_b]]].
      exists b. split.
      (* since b is above a which is assumed not bot b must not be bot *)
      pose proof (lce_bot_neq a b lce_a_b neq_bot) as b_neq_bot.
      (* The key part of the proof is now showing that for any stage after ib
         b will be ther. This can be shown by the forward condition em_le (x ib) (x j)
         since any b' given by it satisfies the definition of S and by maximality
         must be equal to b.
      *)
      apply (dsup_em_mem_inhabited _ (inhabited0 := inhabits i)).
      exists ib. intros j em_le_ib_j.
      destruct (em_le_fw _ _ em_le_ib_j b in_x_ib b_neq_bot) as [b' [in_x_j_b' lce_b_b']].
      assert (b = b') as <-.
      { apply Hbmax. 
        exists j. split. transitivity (x ib); assumption. split.
        assumption. transitivity b; assumption.
        assumption.
      }
      assumption. 
      (* By definition of S, a <= b *)
      assumption.
      (* bw *)
      intros b Hb. apply (dsup_em_mem_inhabited _ (inhabited0 := inhabits i)) in Hb.
      destruct Hb as [j Hdsup].
      destruct (directed i j) as [k [[_ le_i_k_bw] le_j_k]].
      apply le_i_k_bw, Hdsup, le_j_k.
  (* least *)
  - intros y y_ub.
    split.
    (* fw *)
    + intros a [_ in_dsup_em] a_neq_bot.
      destruct (in_dsup_em a_neq_bot) as [i Hdsup].
      specialize (y_ub i).
      destruct y_ub as [y_ub_fw _].
      (* the forward case follows straight-forwardly by using fw in the assumption *)
      apply (y_ub_fw a).
      apply Hdsup. reflexivity. assumption.
    (* bw *)
    (* the backward direction is the meat of the proof *)
    + intros b in_y.
      (* we consider the empty directed sup separately *)
      destruct (classic (inhabited I)) as [Hinh | Hempty].
        (* I not empty *)
        (* First, we find the list of elements ↓b *)
        destruct (finitary b) as [l Hl].
        (* From the backward direction we can show that there is an a that is always eventually present *)
        (* Here we prove by contradiction since otherwise it is always eventually absent. *)
        assert (Hcof : exists a, lce a b /\ forall i, exists j, em_le (x i) (x j) /\ x j a).
        { apply NNPP. intros Hno.
          destruct (eventually_absent_all (inhabited0 := Hinh) x b l) as [i Hi].
          { intros a Hin Hab. apply NNPP. intros Hn. apply Hno. exists a. split; auto.
            intros i. apply NNPP. intros Hn'. apply Hn.
            exists i. intros j Hij Hja. apply Hn'. exists j. auto. }
          destruct (y_ub i) as [_ y_bw].
          destruct (y_bw b in_y) as [a [Hia Hab]].
          exact (Hi i (reflexivity _) a (proj1 (Hl a) Hab) Hab Hia). }
        destruct Hcof as [a [Hab Hcof]].
        (* This a is the a we need, as can be shown using convexity *)
        exists a. split; [| assumption].
        apply (dsup_em_mem_inhabited _ (inhabited0 := Hinh)).
        apply cofinal_always_eventually_present; assumption.
        (* If I is empty then the sup is just bot *)
        exists bot. split; [split | apply bot_lb].
        intros _ i. exfalso. apply Hempty. exact (inhabits i).
        contradiction.
  Qed.

  Global Program Instance em_dcposl `{!Finitary (R := lce)} : DCPOSL (convex_set P) :=
  {|
    dcposl_dcpo := em_dcpo;
    dcposl_sl := convex_sl;
  |}.
  Next Obligation.
    split.
    (* Montonic Join *)
    {
    intros s s' s_lce. split.
    (* forward *)
    - intros b csup_s_b neq_bot.
      (* given b in convex_sup s it follows 
        it is between a and c in the union of all s*)
      destruct csup_s_b as [a [c [a_in_union [c_in_union [lce_a_b lce_b_c]]]]].
      (* in particular c is in s at some kc *)
      destruct c_in_union as [kc c_in_s].
      (* since c is above b which is non-bot it follows c is non-bot *)
      pose proof (lce_bot_neq b c lce_b_c neq_bot) as c_neq_bot.
      (* now we can take the forward direction of lce s s' at kc *)
      destruct (s_lce kc) as [s_lce_fw s_lce_bw].
      destruct (s_lce_fw c c_in_s c_neq_bot) as [c' [c'_in_s lce_c_c']].
      (* which gives our witness c' in convex_sup s' *)
      exists c'. split.
      apply chull_extensive. exists kc. assumption.
      transitivity c; assumption.
    (* backward *)
    - intros b' csup_s_b'.
      (* again, for b' in convex_sup s' it lies between a' and c' in union s' *)
      destruct csup_s_b' as [a' [c' [a'_in_union [c'_in_union [lce_a'_b' lce_b'_c']]]]].
      (* we find ka' such that a' is in s' at ka' *)
      destruct a'_in_union as [ka' a'_in_s'].
      (* we can then use the backward direction of lce s s' to find our witness a' *)
      destruct (s_lce ka') as [lce_fw lce_bw].
      destruct (lce_bw a' a'_in_s') as [a [a_in_s lce_a_a']].
      exists a. split.
      apply chull_extensive. exists ka'. assumption.
      transitivity a'; assumption.
    }
    (* Continuity *)
    intros I x Dx KDx y lce_x_y. split.
    (* forward *)
    - intros b csup_dsup_x_b b_neq_bot.
      (* since b is in the convex sup it lies between a and c in the union of the dsup *)
      destruct csup_dsup_x_b as [a [c [a_in_union [c_in_union [lce_a_b lce_b_c]]]]].
      (* so c must be in dsup at some kc *)
      destruct c_in_union as [kc c_in_x].
      (* since c is above b <> bot it is itself not bot *)
      pose proof (lce_bot_neq b c lce_b_c b_neq_bot) as c_neq_bot.
      (* by definition of dsup there is a an ic that witnesses the membership 
        of c x kc at ic *)
      destruct c_in_x as [_ c_in_x]. specialize (c_in_x c_neq_bot). 
      destruct c_in_x as [ic c_in_x]. 
      assert (c_in_csup: convex_sup (x ic) c).
      { apply chull_extensive. exists kc. apply c_in_x. reflexivity. }
      (* note that in particular `c` is the convex union of `x ic` *)      
      specialize (lce_x_y ic).
      (* we take the foward direction at stage `ic` which gives us our witness *)
      destruct lce_x_y as [lce_x_y_fw _].
      specialize (lce_x_y_fw c c_in_csup c_neq_bot).
      destruct lce_x_y_fw as [c' [c'_in_y lce_c_c']].
      exists c'. split. assumption. transitivity c; assumption.
    - (* backward *)
      (* this the meat of the proof *)
      (* we first split into whether I is inhabited *)
      destruct (classic (inhabited I)) as [Hinh | Hemp].
      + (* This is the non-degenerate case and the complex one *)
        intros b b_in_y. destruct (finitary b) as [l Hl].
        (* First a trivial fact, if x is directed as a collection on two variables
          then it is directed as a collection on a single variable *)
        assert (Dxk : forall k, Directed (fun i => x i k)).
        { 
          intros k i1 i2. destruct (Dx i1 i2) as [i3 [H1 H2]].
          exists i3. split; [exact (H1 k) | exact (H2 k)].
        }
        (* We follow the template from monotonicity and start with the proof 
          of cofinality . It follows roughly the outline of monotonicity but 
          now involving quantification over k. *)
        assert (Hcof : exists k a, lce a b /\
          forall i, exists j, em_le (x i k) (x j k) /\ x j k a).
        {
          apply NNPP. intros Hno.
          (* We start by showing the premise to all_eventually_absent *)
          assert (Hev_abs: forall k, forall a : P, In a l -> lce a b -> exists i : I, forall j : I, em_le (x i k) (x j k) -> ~ x j k a).
          {
            intros k a a_in_l lce_a_b. apply NNPP. intros Hno'.
            apply Hno. exists k. exists a. split. assumption.
            intros i. apply NNPP. intros Hno''. apply Hno'.
            exists i. intros j Hij Hja. apply Hno''.
            exists j. split; assumption.
          }
          (* this is a verson of the concluson of all_eventually_absent quantified over k *)
          assert (Hthr : forall k, exists i, forall j, em_le (x i k) (x j k) ->
                          forall a, In a l -> lce a b -> ~ x j k a).
          {
            intros k.
            apply (eventually_absent_all (fun i => x i k) (inhabited0 := Hinh) b l).
            apply Hev_abs. 
          }
          (* then we use choice to get a function f : K -> I from Hthr *)
          (* this allows us to use the KDirectness assumption to get an upper bound *)
          destruct (choice _ Hthr) as [f Hf]. destruct (KDx f) as [u Hu].
          (* we then use the backward direction of lce x y to get an element b' in the convex union *)
          destruct (lce_x_y u) as [_ lce_x_y_bw].
          destruct (lce_x_y_bw b b_in_y) as [b' [b'_in_csup lce_b'_b]].
          destruct b'_in_csup as [a [c [a_in_union [_ [lce_a_b' _]]]]].
          (* we take the lower endpoint of b' in the convex union *)
          destruct a_in_union as [k a_in_x].
          (* and then the choice property of f gives us our contradiction *)
          specialize (Hf k u (Hu k k) a). apply Hf.
          apply Hl. 1, 2: transitivity b'; assumption. assumption.
        }
        (* cofinality then gives us our witness a at k *)
        destruct Hcof as [k [a [lce_a_b Hcof]]].
        exists a. split; [| assumption]. apply chull_extensive.
        exists k. apply (dsup_em_mem_inhabited _ (inhabited0 := Hinh)).
        apply cofinal_always_eventually_present; try assumption. apply (Dxk k).
      + (* if it is empty we further consider whether K is inhabited *)
        intros b b_in_y. destruct (classic (inhabited K)) as [[k] | Kempt].
        * (* if it is then the convex union is not degenerate *)
          (* so the dsup is empty and evaluates to div_set at every stage *)
          (* hence every stage has bot *)
          exists bot. split. apply chull_extensive.
          exists k. simpl. unfold dsup_em_mem.
          split. intros. contradiction Hemp. split. exact i.
          contradiction. apply bot_lb.
        * (* otherwise every convex union is the empty set so we derive a 
          contradiction from directedness. *)
          exfalso.
          (* indeed, we construct the empty family in x *)
          destruct (KDx (fun k => False_rect I (Kempt (inhabits k)))) as [u _].
          (* directedness guarantees an upper bound over I which contradicts 
          that i is uninhabited *)
          apply Hemp. exact (inhabits u).
  Qed.
End EGLI_MILNER_DOMAIN.

(** The Egli-Milner instances are only tried on goals that are syntactically
  about a [convex_set]. As plain instances they would also apply to a goal
  with an unknown carrier, producing ever larger domains [convex_set ?Q] and
  sending instance search into a loop. *)
#[global] Remove Hints em_dcpo em_dcposl : typeclass_instances.
Global Hint Extern 1 (DCPO (convex_set _)) => simple eapply @em_dcpo : typeclass_instances.
Global Hint Extern 1 (DCPOSL (convex_set _)) => simple eapply @em_dcposl : typeclass_instances.

(** ** Free DCPOSL *)

(* I could define the forgetful functor and use the derived Universal class from 
  Functor.v but that seems like adding more layers to the onion *)

Class IsFDCPOSL (K : Type) (P F : Type) `{Pdcpo : DCPO P} `{Fdcposl : DCPOSL F} :=
  {
    emb : P -> F;
    emb_sc :: ScottContinuous true emb;
    ext {D} `{Ddcposl : DCPOSL D} : (P -> D) -> F -> D;

    ext_mor {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !Monotonic f (lce ++> lce)} `{Hf_strict : !Strict f} ::
      DCPOSLMorphism K (ext f);
    ext_ana {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !Monotonic f (lce ++> lce)} `{Hf_strict : !Strict f} :
      forall p, ext f (emb p) = f p;
    ext_unique {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !Monotonic f (lce ++> lce)} `{Hf_strict : !Strict f}
      (g : F -> D) `{Hg : !DCPOSLMorphism K g} :
      (forall p, g (emb p) = f p) -> forall x, g x = ext f x;
  }.

(** The embedding and the extension operator, together with the universal
  property of the extension with respect to sup-continuous maps, only use the
  partial order on [P]. The DCPO structure is needed later to show that they
  are Scott-continuous. *)

Section EM_EMB_EXT.
  Context `{PartialOrder}.

  (** We define the embedding map into the EM domain, which is just the singleton map *)
  Program Definition em_emb a : convex_set P :=
  {|
    mem := (fun b => b = a)
  |}.
  Next Obligation.
    apply antisymmetry; assumption.
  Qed.

  (** The universal extension is just the join of the image of the convex set *)
  Definition em_ext {D} `{SemiLattice D} (f : P -> D) (x : convex_set P) : D :=
    lsup (fun (p : {p : P | x p}) => f (`p)).

  Lemma em_ext_ana {D} `{Ddcposl : SemiLattice D} (f : P -> D) :
    forall p, em_ext f (em_emb p) = f p.
  Proof.
    intros p. unfold em_emb, em_ext. simpl.
    apply antisymmetry.
    - apply sup_lub. intros i. destruct i. subst. reflexivity.
    - exact (sup_ub (exist (fun q => q = p) p eq_refl)).
  Qed.

  Lemma emb_join_eq (x : convex_set P) :
    lsup (fun (p : {p : P | x p}) => em_emb (`p)) = x.
  Proof.
    apply (antisymmetry (R := incl)).
    - intros p Hsup. destruct Hsup as [a [c [ua [uc [ap pc]]]]].
      destruct ua as [[a' xa'] emba']. destruct uc as [[c' xc'] embc'].
      simpl in emba', embc'; subst. apply (convexity x a' p c'); assumption.
    - intros p xp. apply chull_extensive.
      exists (exist _ p xp). reflexivity.
  Qed.

  Lemma em_ext_unique {D} `{Ddcposl : SemiLattice D} (f : P -> D)
      (g : convex_set P -> D) `{!SupContinuous g}  :
      (forall p, g (em_emb p) = f p) -> forall x, g x = em_ext f x.
  Proof.
    intros Hemb x.
    transitivity (g (lsup (fun p : {p : P | x p} => em_emb (`p)))).
    - f_equal. symmetry. apply emb_join_eq.
    - rewrite sup_cont. unfold em_ext. f_equal.
      apply functional_extensionality.
      intros [p Hp]. apply Hemb.
  Qed.

  (** Sup-continuity of the extension only requires [f] to be monotonic
    from the order on [P] to the [lce] order of a DCPOSL. *)
  Global Instance em_ext_sup_cont {D} `{Ddcposl : DCPOSL D} (f : P -> D)
      `{Hf : !Monotonic f (R ++> lce)} :
    SupContinuous (em_ext f).
  Proof.
    split. intros I x. unfold em_ext. cbn.
    apply (antisymmetry (R := ref)).
    - (* an element of the convex union lies between two elements [a] and [c]
         of the union, so by [lce]-convexity of joins its image is bounded by
         the join of [f a] and [f c], both of which are below the right-hand side *)
      apply sup_lub. intros [p Hp]. cbn.
      destruct Hp as [a [c [[i xa] [[j xc] [ap pc]]]]].
      apply (lsup_lce_between (f a) (f p) (f c)).
      + apply Hf. exact ap.
      + apply Hf. exact pc.
      + apply (sup_at i). apply (sup_at (exist (fun q => x i q) a xa)). reflexivity.
      + apply (sup_at j). apply (sup_at (exist (fun q => x j q) c xc)). reflexivity.
    - (* conversely every element of some [x i] is in the convex union *)
      apply sup_lub. intros i. apply sup_lub. intros [p xp]. cbn.
      apply (sup_at (exist (fun q => convex_sup x q) p
                       (chull_extensive _ _ (ex_intro _ i xp)))).
      reflexivity.
  Qed.
End EM_EMB_EXT.

(** *** Set notations for convex sets *)

Notation "{{-}}" := em_emb.
Notation "{{ x }}" := (em_emb x) (at level 0, x at level 99, format "{{ x }}").
Notation "x ⊆ y" := (incl x y) (at level 70, no associativity).
Notation "x ≤ y" := (em_le x y) (at level 70, no associativity).
(** Membership is the underlying predicate of a convex set. The notation is
  attached to the projection [mem] rather than to a bare application, so
  that it only ever prints convex-set membership. *)
Notation "x ∈ S" := (mem S x) (at level 70, no associativity).

(** Membership is also inclusion of the singleton. *)
Lemma em_in_iff `{PartialOrder} (x : P) (S : convex_set P) :
  {{x}} ⊆ S <-> x ∈ S.
Proof.
  split.
  - intros Hx. apply Hx. reflexivity.
  - intros Hx a <-. exact Hx.
Qed.

(** Finite sets and comprehensions are joins of singletons. *)

Definition em_fin `{PartialOrder} (l : list P) : convex_set P :=
  fsup (fun a => In a l) {{-}}.

Notation "{{ x , y , .. , z }}" := (em_fin (cons x (cons y .. (cons z nil) ..)))
  (at level 0, format "{{ x , y , .. , z }}").

Notation "{{ x | P }}" := (fsup (fun x => P) {{-}})
  (at level 0, x at level 99, format "{{ x | P }}").

Lemma em_comp_in `{PartialOrder} (Q : P -> Prop) (a : P) :
  Q a -> a ∈ {{ x | Q x }}.
Proof.
  intros Ha. exact (fsup_ub a (fun x => Q x) {{-}} Ha a eq_refl).
Qed.

Lemma em_fin_in `{PartialOrder} (l : list P) (a : P) :
  In a l -> a ∈ em_fin l.
Proof.
  intros Ha. exact (fsup_ub a (fun x => In x l) {{-}} Ha a eq_refl).
Qed.

(** On a DCPO, the embedding and the extension are moreover Scott-continuous. *)

Section EM_DOMAIN_FREE.
  Context `{DCPO}.

  Lemma em_emb_bot : {{ (bot : P) }} = div_set.
  Proof.
    apply convex_set_ext. reflexivity.
  Qed.

  (** It is Scott-continuous with no extra assumptions on the DCPO *)
  Lemma em_emb_mon : Monotonic {{-}} (lce ++> em_le).
  Proof.
    split.
    - intros a <- a_neq_bot.
      exists y. split; [reflexivity | assumption].
    - intros b <-. exists x; split; [reflexivity | assumption].
  Qed.

  Lemma em_emb_sc {J} (x: J -> P) `{Dx: !Directed x} y : 
    (forall j, em_le {{ x j }} y) -> em_le {{ dsup x }} y.
  Proof.
    intros em_le_y.
    assert (Hub: forall b, y b -> lce (dsup x) b).
    {
      intros b in_y. apply dsup_lub. intros i.
      destruct (em_le_y i) as [fw bw]. destruct (bw b in_y) as [a [<- lce_a_b]].
      assumption.
    }
    split.
    - intros a Heq dsup_neq_bot. cbn in Heq. subst a.
      assert (Hex: exists j, x j <> bot).
      {
        apply NNPP. intros Hno. apply dsup_neq_bot.
        apply lce_bot_eq. apply dsup_lub. intros i.
        destruct (classic ((x i) = bot)) as [<- |]; [reflexivity|].
        exfalso. apply Hno. exists i. assumption.
      }
      destruct Hex as [j neq_bot]. destruct (em_le_y j) as [fw bw].
      destruct (fw (x j) eq_refl neq_bot) as [b [in_y ?]].
      exists b. split; [assumption|]. apply Hub; assumption.
    - intros b in_y. exists (dsup x). split; [reflexivity|].
      apply Hub. assumption.
  Qed.

  Section EM_EXT_MOR.
    Context {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !Monotonic f (lce ++> lce)} `{Hf_strict : !Strict f}.

    Lemma em_ext_mon : Monotonic (em_ext f) (em_le ++> lce).
    Proof.
      intros x y [fw bw]. unfold em_ext.
      destruct (classic (exists b0, y b0)) as [[b0 yb0] | Hyemp].
      - pose (K := {ab : P * P | x (fst ab) /\ y (snd ab) /\ lce (fst ab) (snd ab)}).
        pose (u := fun k : K => f (fst (`k))).
        pose (v := fun k : K => f (snd (`k))).
        (* the x-join is the join of u *)
        assert (Hu : lsup (fun p : {p : P | x p} => f (`p)) = lsup u).
        { apply (antisymmetry (R := ref)); apply sup_lub.
          - intros [a xa]. cbn.
            destruct (classic (a = bot)) as [-> | Ha].
            + exact (sup_ub (x := u) (exist _ (bot, b0) (conj xa (conj yb0 (bot_lb b0))))).
            + destruct (fw a xa Ha) as [b [yb ab]].
              exact (sup_ub (x := u) (exist _ (a, b) (conj xa (conj yb ab)))).
          - intros [[a b] [xa [yb ab]]]. cbn.
            exact (sup_ub (exist (fun p => x p) a xa)). }
        (* the y-join is the join of v *)
        assert (Hv : lsup (fun q : {q : P | y q} => f (`q)) = lsup v).
        { apply (antisymmetry (R := ref)); apply sup_lub.
          - intros [b yb]. cbn.
            destruct (bw b yb) as [a [xa ab]].
            exact (sup_ub (x := v) (exist _ (a, b) (conj xa (conj yb ab)))).
          - intros [[a b] [xa [yb ab]]]. cbn.
            exact (sup_ub (exist (fun q => y q) b yb)). }
        rewrite Hu, Hv.
        (* now both joins are over K, and K-continuity applies *)
        apply lsup_mon. intros [[a b] [xa [yb ab]]]. unfold u, v. cbn.
        apply Hf. exact ab.
      - (* y is empty, so x is contained in {bot} *)
        transitivity (lsup (fun _ : {p : P | x p} => lsup (fun q : {q : P | y q} => f (`q)))).
        + apply lsup_mon. intros [a xa]. cbn.
          destruct (classic (a = bot)) as [-> | Ha].
          * apply (strict_lb f).
          * destruct (fw a xa Ha) as [b [yb _]]. exfalso. apply Hyemp. exists b. exact yb.
        + (* a constant join equals the constant when the constant least *)
          replace (lsup (fun _ : {p : P | x p} => lsup (fun q : {q : P | y q} => f (`q))))
            with (lsup (fun q : {q : P | y q} => f (`q))); [reflexivity |].
          apply (antisymmetry (R := ref)); apply sup_lub.
          * intros [b yb]. exfalso. apply Hyemp. exists b. exact yb.
          * intros k. reflexivity.
    Qed.

    Lemma em_ext_kcont {J} (x : J -> convex_set P) `{Dx : !Directed (R := em_le) x}
        `{Kx : !KDirected (R := em_le) P x} y :
      (forall j, lce (em_ext f (x j)) y) -> lce (em_ext f (dsup_em x)) y.
    Proof.
      intros Hy. destruct (classic (inhabited J)) as [Hinh | Hemp].
      - (* the supremum is attained at some stage *)
        destruct (dsup_em_attained x (inhabited0 := Hinh)) as [u <-]. apply Hy.
      - (* empty family: the supremum is {bot}, and f is strict *)
        rewrite (dsup_em_empty x Hemp), <- em_emb_bot, em_ext_ana. apply (strict_lb f).
    Qed.

    (** The same for any arity [K] at least as large as [P]. *)
    Lemma em_ext_kcont_large {K} (r : K -> P) (Hsurj : forall p, exists c, r c = p)
        {J} (x : J -> convex_set P) `{Dx : !Directed (R := em_le) x}
        `{Kx : !KDirected (R := em_le) K x} y :
      (forall j, lce (em_ext f (x j)) y) -> lce (em_ext f (dsup_em x)) y.
    Proof.
      apply em_ext_kcont. exact (kdirected_surj r Hsurj x Kx).
    Qed.

    Global Instance em_ext_sup_sc_cont : SupContinuous (em_ext f) :=
      em_ext_sup_cont f (Hf := Hf).
  End EM_EXT_MOR.
End EM_DOMAIN_FREE.

(** ** The EM domain is a free DCPOSL *)

(** We parametrize by the two facts that are are required to make the EM domain a 
  DCPOSL: [dsup_em] is the supremum for [em_le], and the join
  is [K]-continuous. Contingent on [convex_set P] satisfying these two properties,
  and therfore assembling into a DCPOSL, it follows that the EM domain is in fact the
  free K-DCPOSL for any [K] of size bigger than [P] *)

Section EM_FREE.
  Context `{DCPO}.

  Context (em_issup : forall {I} (x : I -> convex_set P) `{!Directed (R := em_le) x},
              IsSup (R := em_le) x (dsup_em x)).

  Local Instance em_dcpo_gen : DCPO (convex_set P) :=
    {|
      lce := em_le;
      lce_po := em_le_po;
      dsup := @dsup_em P H;
      dsup_is_sup := em_issup;
    |}.

  Context (em_kcont : forall K, KContinuous K (lsup (L := convex_set P) (I := K))).

  Local Instance em_dcposl_gen : DCPOSL (convex_set P) :=
    {|
      dcposl_dcpo := em_dcpo_gen;
      dcposl_sl := convex_sl;
      sup_kcont := em_kcont;
    |}.

  (** The arity [K] of the morphisms must be at least as large as [P]. *)
  Context {K} (r : K -> P) (Hsurj : forall p, exists c, r c = p).

  Global Program Instance em_fdcposl : IsFDCPOSL K P (convex_set P) :=
    {|
      emb := {{-}};
      ext D _ f := em_ext f;
    |}.
  Next Obligation.
    split.
    - exact em_emb_mon.
    - intros J HJ x Dx y Hy. apply em_emb_sc. exact Hy.
  Qed.
  Next Obligation.
    split.
    - split.
      + apply (em_ext_mon (Hf_strict := Hf_strict) f).
      + intros J x Dx Kx y Hy. 
        apply (em_ext_kcont_large (Hf_strict := Hf_strict) f r Hsurj); assumption.
    - exact (em_ext_sup_sc_cont f).
  Qed.
  Next Obligation.
    apply em_ext_ana.
  Qed.
  Next Obligation.
    apply em_ext_unique; [destruct Hg; assumption | assumption].
  Qed.
End EM_FREE.

(** For finitary [P], the components come from [em_dcpo] and [em_dcposl]. *)
Section EM_FREE_FINITARY.
  Context `{DCPO} `{!Finitary (R := lce)}.

  Definition em_fdcposl_finitary {K} (r : K -> P) (Hsurj : forall p, exists c, r c = p) :
    IsFDCPOSL K P (convex_set P) :=
    em_fdcposl (@dsup_is_sup _ em_dcpo) (@sup_kcont _ em_dcposl) r Hsurj.
End EM_FREE_FINITARY.

(** ** The EM Powerdomain Relative Monad *)

Section EM_RELATIVE_MONAD.
  Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
  Local Abbreviation id := (fun x => x).

  (** The Free(ish) structure defined above defines a monad relative to 
    the inclusion functor [J K : WSDCPO -> KDCPO] defined in KDCPO.v.
    The mapping on objects takes [X] to [convex_set X]. *)
  (** It satisfies the three relative monad laws. *)

  Lemma em_monad_runital {X Y} {lceX : relation X} {Xpo : PartialOrder lceX}
      {lceY : relation Y} {Ypo : PartialOrder lceY} (f : X -> convex_set Y) :
    f = {{-}} ;; em_ext f.
  Proof.
    apply functional_extensionality. intros x. apply convex_set_ext.
    intros y. split.
    - intros Hfxy. apply chull_extensive.
      exists (exist (fun p => p = x) x eq_refl). assumption.
    - intros [a [c [a_in [c_in [lce_a_y lce_y_c]]]]].
      destruct a_in as [[x' Heqx'] fa]. destruct c_in as [[x'' Heqx''] fc].
      simpl in Heqx', Heqx''. subst. apply (convexity (f x) a y c); assumption.
  Qed.

  Lemma em_monad_lunital {X} {lceX : relation X} {Xpo : PartialOrder lceX} :
    em_ext (em_emb (P := X)) = id.
  Proof.
    apply functional_extensionality. intros x.
    apply convex_set_ext. intros b. split.
    - intros [a [c [a_in [c_in [lce_a_y lce_y_c]]]]].
      destruct a_in as [[a' Ha'] Heqa']. destruct c_in as [[c' Hc'] Heqc'].
      simpl in Heqa', Heqc'. subst. apply (convexity x a' b c'); assumption.
    - intros in_x. apply chull_extensive.
      exists (exist _ b in_x). reflexivity.
  Qed.

  Lemma em_monad_assoc {X Y Z} {lceX : relation X} {Xpo : PartialOrder lceX}
      {lceY : relation Y} {Ypo : PartialOrder lceY} {Zdcpo : DCPO Z}
      (g : Y -> convex_set Z) (f :  X -> convex_set Y)
      {Hg : Monotonic g (lceY ++> em_le)} :
      em_ext (f ;; em_ext g) = em_ext f ;; em_ext g.
  Proof.
    apply functional_extensionality. intros x.
    apply convex_set_ext. intros zb. split.
    - intros [a [c [a_in [c_in [lce_a_y lce_y_c]]]]].
      destruct a_in as [[a' Ha'] Hexta']. destruct c_in as [[c' Hc'] Hextc'].
      destruct Hexta' as [alo' [ahi' [in_alo' [in_ahi' [lcealo' lceahi']]]]].
      destruct Hextc' as [clo' [chi' [in_clo' [in_chi' [lceclo' lcechi']]]]].
      exists alo'. exists chi'. split; [|split;[|split]].
      + destruct in_alo' as [[p Hp] Hfp].
        assert (H: em_ext f x p).
        {
          apply chull_extensive. exists (exist _ a' Ha'). assumption.
        }
        exists (exist _ p H). assumption.
      + destruct in_chi' as [[p Hp] Hfp]. 
        assert (H: em_ext f x p).
        {
          apply chull_extensive. exists (exist _ c' Hc'). assumption.
        }
        exists (exist _ p H). assumption.
      + transitivity a; assumption.
      + transitivity c; assumption.
    - intros [za [zc [za_in [zc_in [lce_za_zb lce_zb_zc]]]]].
      assert (Hbr : forall p, em_ext f x p -> forall z, g p z ->
        (exists a, union (fun q : {q : X | x q} => em_ext g (f (`q))) a /\ lce a z) /\
        (exists c, union (fun q : {q : X | x q} => em_ext g (f (`q))) c /\ lce z c)).
      {
        intros p [ay [cy [[qa Hay] [[qc Hcy] [lce_ay_p lce_p_cy]]]]] z Hz.
        assert (Hlo : exists a, union (fun q : {q : X | x q} => em_ext g (f (`q))) a /\ lce a z).
        {
          destruct (Hg ay p lce_ay_p) as [_ bw].
          destruct (bw z Hz) as [a [Ha lce_a_z]].
          exists a. split; [| exact lce_a_z].
          exists qa. apply chull_extensive. exists (exist _ ay Hay). exact Ha.
        }
        split; [exact Hlo |].
        destruct (classic (z = bot)) as [-> | Hz_bot].
        - destruct Hlo as [a [Ha _]]. exists a. split; [exact Ha | apply bot_lb].
        - destruct (Hg p cy lce_p_cy) as [fw _].
          destruct (fw z Hz Hz_bot) as [c [Hc lce_z_c]].
          exists c. split; [| exact lce_z_c].
          exists qc. apply chull_extensive. exists (exist _ cy Hcy). exact Hc.
      }
      destruct za_in as [[pa Hpa] Hza]. destruct zc_in as [[pc Hpc] Hzc].
      destruct (Hbr pa Hpa za Hza) as [[a [Ha lce_a_za]] _].
      destruct (Hbr pc Hpc zc Hzc) as [_ [c [Hc lce_zc_c]]].
      exists a, c. split; [exact Ha | split; [exact Hc | split]].
      + transitivity za; assumption.
      + transitivity zc; assumption.
  Qed.

  (** The laws are enough to define a functor mapping monotonic functions 
    [f : X -> Y] to functions [convex_map f : convex_set X -> convex_set Y] *)
  Definition convex_map {X Y} {lceX : relation X} {Xpo : PartialOrder lceX} 
    {lceY : relation Y} {Ypo : PartialOrder lceY} 
    (f : X -> Y) := em_ext (f ;; {{-}}).

  Lemma convex_map_id {X} {lceX : relation X} {Xpo : PartialOrder lceX} :
    convex_map id = id.
  Proof.
    unfold convex_map. rewrite em_monad_lunital. reflexivity.
  Qed.

  Lemma convex_map_compose {X Y Z}  {lceX : relation X} {Xpo : PartialOrder lceX}
    {lceY : relation Y} {Ypo : PartialOrder lceY}  {Zdcpo : DCPO Z}
    (g : Y -> Z) (f : X -> Y) {Hg : Monotonic g (lceY ++> lce)} :
    convex_map (f ;; g) = convex_map f ;; convex_map g.
  Proof.
    unfold convex_map.
    rewrite <- (em_monad_assoc (g ;; {{-}}) (f ;; {{-}})
                  (Hg := fun a b Hab => em_emb_mon _ _ (Hg _ _ Hab))).
    apply f_equal. 
    change (f ;; (g ;; {{-}}) = f ;; ({{-}} ;; em_ext (g ;; {{-}}))).
    rewrite <- (em_monad_runital (g ;; {{-}})). reflexivity.
  Qed.

  (** *** Continuity of [convex_map] *)

  (** When [f] is strict Scott-continuous and [X] is well-sized with respect
    to [K], [convex_map f] is monotonic for the EM order and preserves the
    [dsup_em] of K-directed families: such a family is X-directed and hence
    attains its supremum, while the empty family is handled by strictness of
    [f]. *)

  Section CONVEX_MAP_KCONT.
    Context {K X Y} `{Xws : WSDCPO K X} `{Ydcpo : DCPO Y}.
    Context (f : X -> Y) `{Hf : !ScottContinuous true f}.

    Lemma convex_map_mon : Monotonic (convex_map f) (em_le ++> em_le).
    Proof.
      unfold convex_map. intros x x' [fw bw]. split.
      - (* fw: [a] lies between [f p] and [f q] with [p, q] in [x]; since [a]
           is not [bot], neither is [q], so it evolves to some [q'] in [x'] *)
        intros a Ha Ha_nbot.
        destruct Ha as [lo [hi [[[p Hp] Hlo] [[[q Hq] Hhi] [lce_lo_a lce_a_hi]]]]].
        cbn in Hlo, Hhi. subst lo hi.
        assert (Hq_nbot : q <> bot).
        { intros ->. apply Ha_nbot, lce_bot_eq.
          transitivity (f bot); [exact lce_a_hi | apply sc_bot_lb]. }
        destruct (fw q Hq Hq_nbot) as [q' [Hq' lce_q_q']].
        exists (f q'). split.
        + apply chull_extensive. exists (exist _ q' Hq'). reflexivity.
        + transitivity (f q); [exact lce_a_hi | apply sc_lce; exact lce_q_q'].
      - (* bw: [b] is above some [f p'] with [p'] in [x'], justified by [p] in [x] *)
        intros b Hb.
        destruct Hb as [lo [hi [[[p' Hp'] Hlo] [_ [lce_lo_b _]]]]].
        cbn in Hlo. subst lo.
        destruct (bw p' Hp') as [p [Hp lce_p_p']].
        exists (f p). split.
        + apply chull_extensive. exists (exist _ p Hp). reflexivity.
        + transitivity (f p'); [apply sc_lce; exact lce_p_p' | exact lce_lo_b].
    Qed.

    Lemma convex_map_dsup_em {I} (x : I -> convex_set X) `{Dx : !Directed (R := em_le) x}
        `{Kx : !KDirected (R := em_le) K x} y :
      (forall i, em_le (convex_map f (x i)) y) -> em_le (convex_map f (dsup_em x)) y.
    Proof.
      intros Hy. destruct (classic (inhabited I)) as [Hinh | Hemp].
      - (* the supremum is attained at some stage *)
        destruct (dsup_em_attained x (inhabited0 := Hinh)
                    (Kx := kdirected_surj wsdcpo_emb wsdcpo_surj x Kx)) as [u <-].
        apply Hy.
      - (* empty family: the supremum is {bot}, and f is strict *)
        rewrite (dsup_em_empty x Hemp), <- em_emb_bot.
        unfold convex_map. rewrite em_ext_ana. cbn.
        rewrite sc_bot, em_emb_bot. apply div_set_bot.
    Qed.

    (** To state this as K-continuity, the EM domains must be DCPOs, which
      as in [EM_FREE] we assume through [dsup_em] being a supremum. *)

    Section CONVEX_MAP_KCONT_INSTANCE.
      Context (em_issup_X : forall {I} (x : I -> convex_set X) `{!Directed (R := em_le) x},
                  IsSup (R := em_le) x (dsup_em x)).
      Context (em_issup_Y : forall {I} (y : I -> convex_set Y) `{!Directed (R := em_le) y},
                  IsSup (R := em_le) y (dsup_em y)).

      Local Instance em_dcpo_X : DCPO (convex_set X) :=
        {|
          lce := em_le;
          lce_po := em_le_po;
          dsup := @dsup_em X _;
          dsup_is_sup := em_issup_X;
        |}.

      Local Instance em_dcpo_Y : DCPO (convex_set Y) :=
        {|
          lce := em_le;
          lce_po := em_le_po;
          dsup := @dsup_em Y _;
          dsup_is_sup := em_issup_Y;
        |}.

      Lemma convex_map_kcont : KContinuous K (convex_map f).
      Proof.
        split.
        - exact convex_map_mon.
        - intros I x Dx Kx y Hy. apply (convex_map_dsup_em x). exact Hy.
      Qed.
    End CONVEX_MAP_KCONT_INSTANCE.
  End CONVEX_MAP_KCONT.

  (** The unit and extension operators are both natural *)
  Lemma em_emb_nat {X Y}   {lceX : relation X} {Xpo : PartialOrder lceX}
      {lceY : relation Y} {Ypo : PartialOrder lceY} (f : X -> convex_set Y) :
    {{-}} ;; convex_map f = f ;; {{-}}.
  Proof.
    unfold convex_map. rewrite em_monad_runital. reflexivity.
  Qed.

  Lemma em_ext_nat_src {X Y Z} {lceX : relation X} {Xpo : PartialOrder lceX}
      {lceY : relation Y} {Ypo : PartialOrder lceY} {Zdcpo : DCPO Z}
      (f : X -> convex_set Z) {Hf : Monotonic f (lceX ++> em_le)} (g : Y -> X) :
    em_ext (g ;; f) = convex_map g ;; em_ext f.
  Proof.
    unfold convex_map.
    rewrite <- (em_monad_assoc f (g ;; {{-}}) (Hg := Hf)).
    apply f_equal.
    change (g ;; f = g ;; ({{-}} ;; em_ext f)).
    rewrite <- (em_monad_runital f). reflexivity.
  Qed.

  Lemma em_ext_nat_tgt {X Y Y'} {lceX : relation X} {Xpo : PartialOrder lceX}
    {lceY : relation Y} {Ypo : PartialOrder lceY} {Y'dcpo : DCPO Y'}
    (f : X -> convex_set Y) (h : Y -> Y') {Hh : Monotonic h (lceY ++> lce)} :
    em_ext (f ;; convex_map h) = em_ext f ;; convex_map h.
  Proof.
    unfold convex_map.
    exact (em_monad_assoc (h ;; {{-}}) f (Hg := fun a b Hab => em_emb_mon _ _ (Hh _ _ Hab))).
  Qed.

  Section EM_KLEISLI.
    Definition em_kl_compose {X Y Z} {lceY: relation Y} {Ypo : PartialOrder lceY}
      {Zdcpo : DCPO Z}  (g : Y -> convex_set Z) (f : X -> convex_set Y) := 
      f ;; em_ext g.
    
    Lemma kl_em_compose_id_left {X Y} {Ydcpo : DCPO Y} (f : X -> convex_set Y) :
      em_kl_compose {{-}} f = f.
    Proof.
      unfold em_kl_compose. rewrite em_monad_lunital. reflexivity.
    Qed.

    Lemma kl_em_compose_id_right {X Y} {lceX : relation X} {Xpo : PartialOrder lceX}
      {Ydcpo : DCPO Y} (g : X -> convex_set Y) :
      em_kl_compose g {{-}} = g.
    Proof.
      unfold em_kl_compose. rewrite <- em_monad_runital. reflexivity.
    Qed.

    Lemma kl_em_compose_assoc {X Y Z W} {lceY : relation Y} {Ypo : PartialOrder lceY}
        {Zdcpo : DCPO Z} {Wdcpo : DCPO W}
        (h : Z -> convex_set W) (g : Y -> convex_set Z) (f : X -> convex_set Y)
        {Hh : Monotonic h (lce ++> em_le)} :
      em_kl_compose h (em_kl_compose g f) = em_kl_compose (em_kl_compose h g) f.
    Proof.
      unfold em_kl_compose. rewrite em_monad_assoc. reflexivity. assumption.
    Qed.
  End EM_KLEISLI.
End EM_RELATIVE_MONAD.