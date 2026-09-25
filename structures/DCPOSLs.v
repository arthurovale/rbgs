Require Import coqrel.LogicalRelations.
Require Import interfaces.Category.
Require Import interfaces.ConcreteCategory.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.SemiLattices.
Require Import interfaces.Functor.

Require Import Stdlib.Program.Program.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalChoice.
Require Import Stdlib.Logic.ChoiceFacts.

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.


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

Class KContinuous (K : Type) {A B} `{Adcpo: DCPO A} `{Bdcpo: DCPO B} (f: A -> B) :=
  {
    kc_lce :: Monotonic f (lce ++> lce);
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
    dcposl_dcpo :: DCPO L;
    dcposl_sl :: SemiLattice L;
    (** 
      Naively, one might expect that the join be a Scott-continuous function:
      `
        sup_dsup {I} :: ScottContinuous true (lsup (L := L) (I := I));
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
    sup_kcont {K} :: KContinuous K (lsup (L := L) (I := K));
  }.

Class DCPOSLMorphism {A B} `{Adcposl: DCPOSL A} `{Bdcposl: DCPOSL B} (f : A -> B) :=
  {
    dcposl_mor_sc :: ScottContinuous true f;
    dcposl_mor_sup :: SupContinuous f;
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
    emb_sc :: ScottContinuous true emb;
    ext {D} `{Ddcposl : DCPOSL D} : (P -> D) -> F -> D;

    ext_mor {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f} ::
      DCPOSLMorphism (ext f);
    ext_ana {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f} :
      forall p, ext f (emb p) = f p;
    ext_unique {D} `{Ddcposl : DCPOSL D} (f : P -> D) `{Hf : !ScottContinuous true f}
      (g : F -> D) `{Hg : !DCPOSLMorphism g} :
      (forall p, g (emb p) = f p) -> forall x, g x = ext f x;
  }.

Class Finitary `{PartialOrder} := 
  finitary : forall d : P, exists l : list P, forall a, R a d <-> In a l.  

Lemma directed_bounded_in `{DCPO} {I} `{inhabited I} (x : I -> P) `{Dx : !Directed x} (l : list P) :
  exists i, forall j, In (x j) l -> lce (x j) (x i).
Proof.
  destruct inhabited0 as [i0].
  induction l as [| a l IH].
  - exists i0. intros j [].
  - destruct IH as [i Hi].
    destruct (classic (exists j0, x j0 = a)) as [[j0 Hj0] | Hno].
    + destruct (Dx j0 i) as [k [Hj0k Hik]].
      exists k. intros j [Ha | Hl].
      * rewrite <- Ha, <- Hj0. exact Hj0k.
      * transitivity (x i); auto.
    + exists i. intros j [Ha | Hl].
      * destruct Hno. exists j. auto.
      * auto.
Qed.

Lemma finitary_DCPO_acc `{DCPO} `{!Finitary (R := lce)} {I} `{inhabited I} (x : I -> P) `{!Directed x} :
  exists i, forall j, lce (x j) (x i).
Proof.
  destruct (finitary (dsup x)) as [below Hbelow].
  destruct (directed_bounded_in (inhabited0 := inhabited0)  x below) as [i Hi].
  exists i. intros j. apply Hi, Hbelow, dsup_ub.
Qed.

Lemma monotone_seq_directed `{DCPO} (g : nat -> P) :
  (forall n, lce (g n) (g (S n))) -> Directed g.
Proof.
  intros Hg.
  assert (Hmon : forall n m, (n <= m)%nat -> lce (g n) (g m)).
  { intros n m Hnm. induction Hnm. reflexivity. transitivity (g m); auto. }
  intros n m. exists (Nat.max n m).
  split; apply Hmon. apply Nat.le_max_l. apply Nat.le_max_r.
Qed.

Lemma finitary_DCPO_maximal `{DCPO} `{!Finitary (R := lce)} (A : P -> Prop) :
  (exists b, A b) ->
  exists b, A b /\ forall b', A b' -> lce b b' -> b = b'.
Proof.
  intros [b0 Hb0].
  destruct (classic (exists b, A b /\ forall b', A b' -> lce b b' -> b = b'))
    as [Hmax | Hno]; [assumption | exfalso].
  (* every element of A has a strict successor in A *)
  assert (Hstep : forall b, exists b', A b -> A b' /\ lce b b' /\ b <> b').
  { intros b. destruct (classic (A b)) as [Hb | Hb].
    - apply NNPP. intros Hn. apply Hno. exists b. split; auto.
      intros b' Hb' Hle. apply NNPP. intros Hneq. apply Hn. exists b'. auto.
    - exists b. tauto. }
  destruct (choice _ Hstep) as [f Hf].
  pose (g := nat_rect (fun _ => P) b0 (fun _ b => f b)).
  assert (HgS : forall n, A (g n)).
  { induction n; cbn. assumption. apply Hf; assumption. }
  assert (Hg : forall n, lce (g n) (g (S n)) /\ g n <> g (S n)).
  { intros n. apply Hf, HgS. }
  pose proof (monotone_seq_directed g (fun n => proj1 (Hg n))) as Hdir.
  destruct (finitary_DCPO_acc (inhabited0 := inhabits 0) g) as [i Hi].
  destruct (Hg i) as [Hle Hneq].
  apply Hneq, antisymmetry; auto.
Qed.

Section EGLI_MILNER_DOMAIN.
  Context `{DCPO}.    

  Record convex_set :=
    {
      mem :> P -> Prop;
      convexity : forall a b c, mem a -> mem c -> lce a b -> lce b c -> mem b;
    }.

  Lemma convex_set_ext (x y : convex_set) :
    (forall a, x a <-> y a) -> x = y.
  Proof.
    intros Hxy. destruct x as [x Hx], y as [y Hy]. cbn in *.
    cut (x = y). { intro. subst. f_equal. apply proof_irrelevance. }
    apply functional_extensionality. intro a.
    apply propositional_extensionality. apply Hxy.
  Qed.

  Definition incl (x y : convex_set) := forall a, x a -> y a. 

  Definition union {I} (x : I -> (P -> Prop)) (a : P) := exists i, x i a.

  (** *** Convex Hull *)

  (** The convex hull operator is the smallest convex set including the original set *)

  Definition chull_mem (x : P -> Prop) (b : P) := 
    exists a c , x a /\ x c /\ lce a b /\ lce b c.

  Lemma chull_convexity (x : P -> Prop) : 
    forall a b c, chull_mem x a -> chull_mem x c -> lce a b -> lce b c -> chull_mem x b.
  Proof.
    intros a b c mem_a mem_c lce_a_b lce_b_c.
    destruct mem_a as [a' [a'' [in_x_a' [in_x_a'' [lce_a'_a lce_a_a'']]]]].
    destruct mem_c as [c' [c'' [in_x_c' [in_x_c'' [lce_c'_c lce_c_c'']]]]].
    exists a'. exists c''. repeat (try split); try assumption.
    transitivity a; assumption. transitivity c; assumption.
  Qed.

  Definition chull (x : P -> Prop) : convex_set := 
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

  (** *** SemiLattice Structure *)
 
  Global Instance incl_po : PartialOrder incl.
  Proof.
    split. split; firstorder.
    intros x y incl_x_y incl_y_x. apply convex_set_ext.
    firstorder.
  Qed.

  Global Instance convex_poset : Poset convex_set :=
  {
    ref := incl;
  }.

  Definition convex_sup {I} (x : I -> convex_set) : convex_set := chull (union x).

  Global Program Instance convex_sl : SemiLattice convex_set :=
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

  (** *** DCPO Structure *)

  (** *** Candidate DCPO Structure *)

  Record em_le (x y : convex_set) :=
    {
      (** fw: no information is dropped, if a in x then it evolves to some b in y *)
      (** different from standard EM, we consider bot and do not enforce fw for it *)
      em_le_fw : forall (a : P), x a -> a <> bot -> exists (b : P) , y b /\ lce a b;
      (** anything in y needs to be justified by something in x *)
      em_le_bw : forall (b : P) , y b -> exists (a : P) , x a /\ lce a b
    }.

  (** bot can only be removed forwardly *)
  Lemma le_div (x y : convex_set) :
    em_le x y -> y bot -> x bot.
  Proof.
    intros Hle Hybot. destruct Hle as [Hfw Hbw].
    specialize (Hbw bot Hybot). destruct Hbw as [a [in_x lcea]].
    pose lce_bot_eq as Heq. specialize (Heq a lcea). rewrite <- Heq. exact in_x.
  Qed.

  (* the bottom element for em_le is {div} *)
  Program Definition div_set := 
  {|
    mem x := x = bot;
  |}.
  Next Obligation.
    apply lce_bot_eq; assumption.
  Defined.

  Lemma div_set_bot (x : convex_set) : em_le div_set x.
  Proof.
    split.
    - intros a in_div_set neq_bot. 
      unfold div_set in in_div_set. rewrite in_div_set in *.
      contradiction neq_bot. reflexivity.
    - intros b in_x. exists bot. split. reflexivity. apply bot_lb.
  Qed.

  Global Instance le_preo :
    PreOrder em_le.
  Proof.
    split; split.
    - intros a ? ?. exists a. split. assumption. reflexivity.
    - intros a ?. exists a. split. assumption. reflexivity.
    - intros a in_x neq_bot. destruct H0 as [fw_x_y _]. destruct H1 as [fw_y_z _].
      specialize (fw_x_y a in_x neq_bot). destruct fw_x_y as [b [in_y lce_a_b]].
      assert (b_neq_bot: b <> bot). 
        { intros b_eq_bot. rewrite b_eq_bot in lce_a_b. 
          apply lce_bot_eq in lce_a_b. contradiction lce_a_b. }
      specialize (fw_y_z b in_y b_neq_bot). destruct fw_y_z as [c [in_z lce_b_c]].
      exists c; split. assumption. etransitivity. exact lce_a_b. exact lce_b_c.
    - intros c in_z. destruct H0 as [_ bw_x_y]. destruct H1 as [_ bw_y_z]. 
      specialize (bw_y_z c in_z). destruct bw_y_z as [b [in_y lce_b_c]].
      specialize (bw_x_y b in_y). destruct bw_x_y as [a [in_x lce_a_b]].
      exists a. split. assumption. transitivity b; assumption.
  Qed.

  Lemma em_le_incl (x y : convex_set) :
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

  (** the supremum is the set of all elements that are eventually always present *)
  (** bot is only present if it never gets removed *)
  Definition dsup_em_mem {I} (x : I -> convex_set) `{Hx: !Directed x} : P -> Prop :=
    fun a => (a = bot -> forall i, x i bot) /\
             (a <> bot -> exists i, forall j, em_le (x i) (x j) -> x j a).

  (** Convexity follows straight-forwardly *)
  Lemma dsup_em_convexity {I} (x : I -> convex_set) `{Hx: !Directed x} : 
    forall a b c, dsup_em_mem x a -> dsup_em_mem x c -> lce a b -> lce b c -> dsup_em_mem x b.
  Proof.
    intros a b c [Ha_bot Ha] [Hc_bot Hc] lce_a_b lce_b_c.
    split. 
    - intros ->. apply Ha_bot. apply lce_bot_eq. assumption.
    - intros b_neq_bot.
      assert (c_neq_bot : c <> bot).
      { intros ->. apply b_neq_bot, lce_bot_eq. assumption. }
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

  Definition dsup_em {I} (x : I -> convex_set) `{Hx: !Directed x} : convex_set := 
  {|
    mem := dsup_em_mem x;
    convexity := dsup_em_convexity x;
  |}.

  (** If a finite set of elements are all eventually always absent, then there is 
  a stage when they are all simultaneously absent. *)
  Lemma eventually_absent_all {I} (x : I -> convex_set) `{Hx : !Directed x} `{inhabited I} (b : P) (l : list P) :
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

  Global Program Instance em_dcpo `{!Finitary (R := lce)} : DCPO convex_set := 
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
      assert (b_neq_bot: b <> bot).
      { intros Heq. apply neq_bot. apply lce_bot_eq. subst; assumption. }
      (* The key part of the proof is now showing that for any stage after ib
         b will be ther. This can be shown by the forward condition em_le (x ib) (x j)
         since any b' given by it satisfies the definition of S and by maximality
         must be equal to b.
      *)
      split; [intros; contradiction | intros _].
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
      intros b [b_bot_dsup b_neq_bot_dsup].
      destruct (classic (b = bot)) as [b_eq | b_eq].
      * exists bot. split; [apply b_bot_dsup; assumption | apply bot_lb].
      * destruct (b_neq_bot_dsup b_eq) as [j Hdsup].
        destruct (directed i j) as [k [le_i_k le_j_k]].
        destruct le_i_k as [_ le_i_k_bw].
        apply le_i_k_bw. apply Hdsup. assumption.
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
      (* first we handle the bot case, as we then know bot is in all
      stages since bot propagates backward from y *)
      destruct (classic (b = bot)) as [b_eq | b_eq].
      * exists bot. split.
        split. 
          intros. eapply le_div. apply y_ub. subst. assumption.
          contradiction.
        apply bot_lb.
      (* if b is not bot then first we consider the empty directed sup separately *)
      * destruct (classic (inhabited I)) as [Hinh | Hempty].
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
        (* This a is the a we need, as can be shown using convenxity *)
        exists a. split; [split | assumption].
        { intros -> i. destruct (Hcof i) as [j [Hij Hj]]. exact (le_div _ _ Hij Hj). }
        intros Ha. destruct Hinh as [i0]. destruct (Hcof i0) as [i [_ Hi]].
        exists i. intros j Hij.
        destruct (Hcof j) as [k [Hjk Hk]].
        destruct (em_le_fw _ _ Hij a Hi Ha) as [e [Hje Hae]].
        destruct (em_le_bw _ _ Hjk a Hk) as [d [Hjd Hda]].
        apply (convexity (x j) d a e); assumption.
        (* If I is empty then the sup is just bot *)
        exists bot. split; [split | apply bot_lb].
        intros _ i. exfalso. apply Hempty. exact (inhabits i).
        contradiction.
  Qed.

