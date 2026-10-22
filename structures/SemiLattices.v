Require Export structures.Posets.

Require Import interfaces.ConcreteCategory.

Require Import Stdlib.Program.Program.
Require Import Stdlib.Logic.FunctionalExtensionality.
Require Import Stdlib.Logic.PropExtensionality.
Require Import Stdlib.Lists.List.

(* NOTE: This was created by first taking Jérémie's CDLattices and then 
removing all the data about infs. *)

(** * Join semi-lattices *)

(** ** Definition *)

Class SemiLattice (L : Type) :=
  {
    cdl_poset :: Poset L;

    lsup : forall {I}, (I -> L) -> L;

    lsup_sup {I} (u : I -> L) :: IsSup u (lsup u);
  }.

Global Instance lsup_params : Params (@lsup) 1 := { }.

(** The notations below work well in the context of completely
  distributive monads. *)

Notation "'sup' i .. j , M" := (lsup (fun i => .. (lsup (fun j => M)) .. ))
  (at level 65, i binder, j binder, right associativity).

(** It is often convenient to take the [sup] or [inf] by ranging over
  the elements of an index type which satisfy a given predicate. *)

Definition fsup `{SemiLattice} {I} (P : I -> Prop) (f : I -> L) :=
  lsup (I := sig P) (fun x => f (proj1_sig x)).

Notation "'sup' { x | P } , M" :=
  (fsup (fun x => P) (fun x => M))
  (at level 65, x name, right associativity).
Notation "'sup' { x : A | P } , M" :=
  (fsup (fun x : A => P) (fun x : A => M))
  (at level 65, A at next level, x name, right associativity).

Section PREDICATES.
  Context `{Lsl : SemiLattice}.

  Lemma fsup_ub {I} (i : I) (P : I -> Prop) (x : I -> L) :
    P i -> x i <= fsup P x.
  Proof.
    intros Hi. apply (sup_at (exist P i Hi)). reflexivity.
  Qed.

  Lemma fsup_at {I} (i : I) (P : I -> Prop) (x : L) (y : I -> L) :
    P i -> x <= y i -> x <= fsup P y.
  Proof.
    intros Hi Hx. etransitivity; eauto. apply fsup_ub; auto.
  Qed.

  Lemma fsup_lub {I} (P : I -> Prop) (x : I -> L) (y : L) :
    (forall i, P i -> x i <= y) -> fsup P x <= y.
  Proof.
    intros Hy. apply sup_lub. intros [i Hi]. auto.
  Qed.
End PREDICATES.

(** * Derived operations *)

Section OPS.
  Context `{Lsl : SemiLattice}.

  (** Least element *)

  Definition lbot : L :=
    sup i : Empty_set, match i with end.

  Lemma lbot_lb x :
    lbot <= x.
  Proof.
    apply sup_lub. intros [ ].
  Qed.

  (** The join order of a semilattice is pointed by [lbot]. It gets a low
    priority so that an unannotated [bot] on a DCPOSL means the [lce] bottom. *)
  Global Instance sl_pointed : Pointed ref | 20 :=
    {| bot := lbot; bot_lb := lbot_lb |}.

  (** ** Binary joins *)

  Definition join (x y : L) :=
    sup b : bool, if b then x else y.

  Lemma join_ub_l x y :
    x <= (join x y).
  Proof.
    apply (sup_at true). reflexivity.
  Qed.

  Lemma join_ub_r x y :
    y <= (join x y).
  Proof.
    apply (sup_at false). reflexivity.
  Qed.

  Lemma join_lub x y z :
    x <= z -> y <= z -> (join x y) <= z.
  Proof.
    intros. apply sup_lub. destruct i; assumption.
  Qed.

  Lemma join_l x y z :
    x <= y ->
    x <= (join y z).
  Proof.
    intro.
    etransitivity; eauto.
    apply join_ub_l.
  Qed.

  Lemma join_r x y z :
    x <= z ->
    x <= (join y z).
  Proof.
    intro.
    etransitivity; eauto.
    apply join_ub_r.
  Qed.

  Lemma ref_join x y :
    x <= y <-> join x y = y.
  Proof.
    split; intro.
    - apply antisymmetry, join_ub_r.
      apply join_lub; auto. reflexivity.
    - rewrite <- H. apply join_ub_l.
  Qed.

  (** ** Properties *)

  Lemma join_lbot_l x :
    join lbot x = x.
  Proof.
    eapply sup_unique. apply lsup_sup. split.
    destruct i. apply lbot_lb. reflexivity.
    intros. exact (H false).
  Qed.

  Lemma join_comm x y :
    join x y = join y x.
  Proof.
    eapply sup_unique. apply lsup_sup. split.
    destruct i. apply join_ub_r. apply join_ub_l.
    intros. apply join_lub. exact (H false). exact (H true).
  Qed.

  Lemma join_idemp x :
    join x x = x.
  Proof.
    eapply sup_unique. apply lsup_sup. split.
    destruct i; reflexivity.
    intros; exact (H true).
  Qed.

  Lemma join_lsup x y :
    join x y = sup b : bool, if b then x else y.
  Proof.
    reflexivity.
  Qed.

  Lemma lbot_lsup :
    lbot = sup i : Empty_set, match i with end.
  Proof.
    reflexivity.
  Qed.

  (** These properties are more than enough to completely define the
    derived operations, so that relying on their concrete definition
    should not be necessary. *)

  Global Opaque lbot join.

End OPS.

(* Infix "||" := join (at level 50, left associativity). *)


Class SupContinuous {A B} `{Asl: SemiLattice A} `{Bsl: SemiLattice B} (f : A -> B) :=
  {
    sup_cont {I} (x : I -> A) : f (lsup x) = lsup (fun i => f (x i));
  }.

(** Sup-continuous functions are closed under identity and composition. *)

Global Instance supcont_id `{SemiLattice} :
  SupContinuous (fun x => x).
Proof.
  split. intros I x. reflexivity.
Qed.

Global Instance supcont_compose {A B C} `{SemiLattice A} `{SemiLattice B} `{SemiLattice C}
  (g : B -> C) (f : A -> B) :
  SupContinuous g ->
  SupContinuous f ->
  SupContinuous (fun x => g (f x)).
Proof.
  intros Hg Hf. split. intros I x.
  rewrite (sup_cont (f := f)). apply (sup_cont (f := g)).
Qed.

Lemma supcont_mon {A B} `{Asl: SemiLattice A} `{Bsl: SemiLattice B} (f : A -> B) :
  SupContinuous f -> Monotonic f (ref ++> ref).
Proof.
  intros Hf x y Hxy. assert (Hjoin : join x y = y) by (apply ref_join; assumption).
  rewrite <- Hjoin, join_lsup, sup_cont. apply (sup_at true). reflexivity.
Qed.

Lemma supcont_strict {A B} `{Asl: SemiLattice A} `{Bsl: SemiLattice B} (f : A -> B) :
  SupContinuous f -> f lbot = lbot.
Proof.
  intros Hf. rewrite lbot_lsup. rewrite sup_cont. apply antisymmetry.
  apply lsup_sup. intros i. destruct i.
  apply lbot_lb.
Qed.

Section FORALL_SL.
  Context {I} {L : I -> Type} `{Lsl : forall i : I, SemiLattice (L i)}.

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

  Local Program Instance forall_sl : SemiLattice (forall i, L i) :=
    {
      cdl_poset := forall_poset;
      lsup J x := fun i => lsup (fun j => x j i);
    }.
  Next Obligation.
    intros J u. split.
    - intros j i. apply (sup_ub (IsSup := lsup_sup (fun j => u j i)) j).
    - intros y Hy i. apply (sup_lub (IsSup := lsup_sup (fun j => u j i))). intros j. apply (Hy j i).
  Qed.
End FORALL_SL.

Global Hint Extern 1 (SemiLattice (forall i, _)) =>
  lazymatch goal with |- SemiLattice (forall _, _) => eapply @forall_sl end : typeclass_instances.

Module SLat <: ConcreteCategory.

  Class Structure (L : Type) : Type :=
    structure_slattice : SemiLattice L.

  Global Hint Immediate structure_slattice : typeclass_instances.
  Global Hint Extern 1 (Structure _) => red : typeclass_instances.

  Class Morphism {A B} `{Asl: SemiLattice A} `{Bsl: SemiLattice B} (f : A -> B) :=
    morphism_sl : SupContinuous f.

  Global Hint Immediate morphism_sl : typeclass_instances.
  Global Hint Extern 1 (Morphism _) => red : typeclass_instances.

  Global Instance id_mor `{SemiLattice} :
    Morphism (fun x => x).
  Proof.
    typeclasses eauto.
  Qed.

  Global Instance compose_mor :
    forall {A B C} `{SemiLattice A} `{SemiLattice B} `{SemiLattice C} (g: B -> C) (f: A -> B),
      Morphism g ->
      Morphism f ->
      Morphism (fun x => g (f x)).
  Proof.
    typeclasses eauto.
  Qed.

  Include ConcreteCategoryTheory.

End SLat.

(** ** Free Join-Semilattice *)

Section FREE_SL.
  Definition set (P : Type) := P -> Prop.

  Lemma set_eq {P} (x y : set P) :
    (forall p, x p <-> y p) -> x = y.
  Proof.
    intros. apply functional_extensionality. intros p.
    apply propositional_extensionality. apply H.
  Qed.

  Definition subset {P} (x : set P) (y : set P) : Prop :=
    forall p, x p -> y p.

  Global Instance subset_po {P} : PartialOrder (subset (P := P)).
  Proof.
    split. split; firstorder.
    intros x y incl_x_y incl_y_x.
    apply functional_extensionality. intro z.
    apply propositional_extensionality.
    split; [apply incl_x_y | apply incl_y_x].
  Qed.

  Local Instance set_poset {P} : Poset (set P) :=
  {
    ref := subset;
  }.

  (** Joins are given by convex unions, so first we define the usual union *)
  Definition union {P} {I} (x : I -> (P -> Prop)) (a : P) := exists i, x i a.

  Local Program Instance set_sl {P} : SemiLattice (set P) :=
    {
      lsup I x := union x;
    }.
  Next Obligation.
    split.
    - intros i. intros p H. exists i; assumption.
    - intros x H. intros p [j Hu]. exact (H j p Hu).
  Qed.

  Local Instance set_ppo {P} : PPoset (set P) :=
    {| pref := subset; pref_po := subset_po;
       pref_pointed := @sl_pointed (set P) (@set_sl P) |}.

  Definition set_emb {P} (p : P) : set P := fun p' => p' = p.

  Definition set_ext {P D} `{SemiLattice D} (f : P -> D) (x : set P) : D :=
    lsup (fun p : {p : P | x p} => f (`p)).

  Lemma set_ext_ana {P D} `{SemiLattice D} (f : P -> D) :
    forall p, set_ext f (set_emb p) = f p.
  Proof.
    intros p. unfold set_emb, set_ext. simpl.
    apply antisymmetry.
    - apply sup_lub. intros i. destruct i. subst. reflexivity.
    - exact (sup_ub (exist (fun q => q = p) p eq_refl)).
  Qed.
    
  Lemma set_emb_join_eq {P} (x : set P) :
    lsup (fun p : {p : P | x p} => set_emb (`p)) = x.
  Proof.
    apply antisymmetry.
    - intros p Hsup. destruct Hsup as [[p' Hx]  Hemb].
      unfold set_emb in Hemb. simpl in Hemb. subst. assumption.
    - intros p xp. exists (exist _ p xp). reflexivity.
  Qed.

  Lemma set_ext_unique {P D} `{SemiLattice D} (f : P -> D)
      (g : set P -> D) `{!SupContinuous g} :
    (forall p, g (set_emb p) = f p) -> forall x, g x = set_ext f x.
  Proof.
    intros Hemb x.
    transitivity (g (lsup (fun p : {p : P | x p} => set_emb (`p)))).
    - f_equal. symmetry. apply set_emb_join_eq.
    - rewrite sup_cont. unfold set_ext. f_equal.
      apply functional_extensionality.
      intros [p Hp]. apply Hemb.
  Qed.

  Global Instance set_ext_mon_l {P D} `{SemiLattice D} :
    Monotonic (set_ext (P := P) (D := D)) ((- ==> ref) ++> (- ==> ref)).
  Proof.
    intros f g Hfg. intros x. unfold set_ext.
    apply sup_lub. intros p. apply (sup_at p). apply Hfg.
  Qed.

  Global Instance set_ext_mon_r {P D} `{SemiLattice D} (f : P -> D) :
    Monotonic (set_ext f) (subset ++> ref).
  Proof.
    intros x y Hxy. unfold set_ext. apply sup_lub.
    intros [p Hp]. simpl.  specialize (Hxy p Hp).
    apply (sup_at (exist _ p Hxy)). reflexivity.
  Qed.

  Global Instance set_ext_sup_cont {P D} `{SemiLattice D} (f : P -> D) :
    SupContinuous (set_ext f).
  Proof.
    split.
    intros I x. unfold set_ext. simpl. apply antisymmetry.
    - apply sup_lub. intros p. destruct p as [p [i Hx]]. simpl.
      apply (sup_at i). apply (sup_at (exist _ p Hx)). reflexivity.
    - apply sup_lub. intros i. apply sup_lub. intros [p Hx].
      assert (Hu: union x p). { exists i; exact Hx. }
      apply (sup_at (exist _ p Hu)). reflexivity.
  Qed.

  Lemma set_ext_lbot {P D} `{SemiLattice D} (f : P -> D) :
    set_ext f lbot = lbot.
  Proof.
    apply supcont_strict. typeclasses eauto.
  Qed.

  Lemma set_in_iff {P} (p : P) (x : set P) :
    subset (set_emb p) x <-> x p.
  Proof.
    split.
    - intros H. exact (H p eq_refl).
    - intros Hx. unfold subset. intros p'. intros Hemb.
      destruct Hemb. assumption.
  Qed.

  Definition set_fin {P} (l : list P) : set P :=
    fsup (fun p => In p l) set_emb.

  Lemma set_comp_in {P} (x : P -> Prop) (p : P) :
    x p -> fsup x set_emb p.
  Proof.
    intros Hx. simpl. exists (exist _ p Hx). reflexivity.
  Qed.

  Lemma set_fin_in {P} (l : list P) (p : P) :
    In p l -> set_fin l p.
  Proof.
    intros Hin. unfold set_fin.
    simpl. exists (exist _ p Hin). reflexivity.
  Qed.

End FREE_SL.

Global Hint Extern 1 (SemiLattice (set _)) => simple eapply @set_sl : typeclass_instances.
Global Hint Extern 15 (PPoset (set _)) => simple eapply @set_ppo : typeclass_instances.

Declare Scope set_scope.
Delimit Scope set_scope with set.

Notation "{{-}}" := set_emb : set_scope.
Notation "{{ x }}" := (set_emb x) (at level 0, x at level 99, format "{{ x }}") : set_scope.
Notation "x ⊆ y" := (subset x y) (at level 70, no associativity) : set_scope.
Notation "x ∈ S" := (S x) (at level 70, no associativity, only parsing) : set_scope.
Notation "{{ x , y , .. , z }}" := (set_fin (cons x (cons y .. (cons z nil) ..)))
  (at level 0, format "{{ x , y , .. , z }}") : set_scope.
Notation "{{ x | P }}" := (fsup (fun x => P) set_emb)
  (at level 0, x at level 99, format "{{ x | P }}") : set_scope.

Section SET_MONAD.
  Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
  Local Abbreviation id := (fun x => x).

  Lemma set_monad_runital {X Y} (f : X -> set Y) :
    f = set_emb ;; set_ext f.
  Proof.
    apply functional_extensionality. intros x. unfold set_ext, set_emb.
    apply set_eq. intros y. split.
    - intros Hxy. exists (exist (fun p => p = x) x eq_refl). assumption.
    - intros [[x' Hx] Hf]. subst. assumption.
  Qed.

  Lemma set_monad_lunital {P} :
    set_ext (set_emb (P := P)) = id.
  Proof.
    apply functional_extensionality. intros x. unfold set_ext, set_emb.
    apply set_eq. intros p. split.
    - simpl. intros [[p' Hx] Heq]. simpl in Heq. subst. assumption.
    - intros Hx. exists (exist _ p Hx). reflexivity.
  Qed.

  Lemma set_monad_assoc {X Y Z} (g : Y -> set Z) (f : X -> set Y) :
    set_ext (f ;; set_ext g) = set_ext f ;; set_ext g.
  Proof.
    apply functional_extensionality. intros x. symmetry.
    apply (set_ext_unique (f ;; set_ext g) (set_ext f ;; set_ext g)).
    intros p. exact (f_equal (set_ext g) (set_ext_ana f p)).
  Qed.

  Definition set_map {X Y} (f : X -> Y) : set X -> set Y :=
    set_ext (f ;; set_emb).

  Lemma set_map_id {X} :
    set_map (id : X -> X) = id.
  Proof.
    unfold set_map. rewrite set_monad_lunital. reflexivity.
  Qed.

  Lemma set_map_compose {X Y Z} (g : Y -> Z) (f : X -> Y) :
    set_map (f ;; g) = set_map f ;; set_map g.
  Proof.
    unfold set_map.
    rewrite <- (set_monad_assoc (g ;; set_emb) (f ;; set_emb)).
    apply f_equal. 
    change (f ;; (g ;; set_emb) = f ;; (set_emb ;; set_ext (g ;; set_emb))).
    rewrite <- (set_monad_runital (g ;; set_emb)). reflexivity.
  Qed.

  Lemma set_map_mon {X Y} (f : X -> Y) :
    Monotonic (set_map f) (subset ++> subset).
  Proof.
    unfold set_map. exact (set_ext_mon_r (f ;; set_emb)).
  Qed.

  Global Instance set_map_sup_cont {X Y} (f : X -> Y) :
    SupContinuous (set_map f).
  Proof.
    unfold set_map. exact (set_ext_sup_cont (f ;; set_emb)).
  Qed.

  Lemma set_emb_nat {X Y} (f : X -> set Y) :
    set_emb ;; set_map f = f ;; set_emb.
  Proof.
    unfold set_map. rewrite <- (set_monad_runital (f ;; set_emb)). reflexivity.
  Qed.

  Lemma set_ext_nat_src {X Y Z} (f : X -> set Z) (g : Y -> X) :
    set_ext (g ;; f) = set_map g ;; set_ext f.
  Proof.
    unfold set_map.
    rewrite <- (set_monad_assoc f (g ;; set_emb)).
    apply f_equal.
    change (g ;; f = g ;; (set_emb ;; set_ext f)).
    rewrite <- (set_monad_runital f). reflexivity.
  Qed.

  Lemma set_ext_nat_tgt {X Y Y'} (f : X -> set Y) (h : Y -> Y') :
    set_ext (f ;; set_map h) = set_ext f ;; set_map h.
  Proof.
    unfold set_map. exact (set_monad_assoc (h ;; set_emb) f).
  Qed.

  Section SET_KLEISLI.
    Definition set_kl_compose {X Y Z} (g : Y -> set Z) (f : X -> set Y) : X -> set Z :=
      f ;; set_ext g.

    Lemma set_kl_compose_id_left {X Y} (f : X -> set Y) :
      set_kl_compose set_emb f = f.
    Proof.
      unfold set_kl_compose. rewrite set_monad_lunital. reflexivity.
    Qed.

    Lemma set_kl_compose_id_right {X Y} (g : X -> set Y) :
      set_kl_compose g set_emb = g.
    Proof.
      unfold set_kl_compose. rewrite <- (set_monad_runital g). reflexivity.
    Qed.

    Lemma set_kl_compose_assoc {X Y Z W}
        (h : Z -> set W) (g : Y -> set Z) (f : X -> set Y) :
      set_kl_compose h (set_kl_compose g f) = set_kl_compose (set_kl_compose h g) f.
    Proof.
      unfold set_kl_compose. rewrite set_monad_assoc. reflexivity.
    Qed.

    Definition set_kl_emb {X Y} (f : X -> Y) : X -> set Y :=
      f ;; set_emb.

    Lemma set_kl_compose_emb_l {X Y Z} (f : X -> Y) (α : Y -> set Z) :
      set_kl_compose α (set_kl_emb f) = f ;; α.
    Proof.
      apply functional_extensionality. intros x. apply set_ext_ana.
    Qed.

    Lemma set_kl_compose_emb_r {X Y Z} (α : X -> set Y) (f : Y -> Z) :
      set_kl_compose (set_kl_emb f) α = α ;; set_map f.
    Proof.
      reflexivity.
    Qed.

    Lemma set_kl_emb_id {X} :
      set_kl_emb (id : X -> X) = set_emb.
    Proof.
      reflexivity.
    Qed.

    Lemma set_kl_emb_compose {X Y Z} (g : Y -> Z) (f : X -> Y) :
      set_kl_emb (f ;; g) = set_kl_compose (set_kl_emb g) (set_kl_emb f).
    Proof.
      apply functional_extensionality. intros x. unfold set_kl_compose, set_kl_emb.
      rewrite set_ext_ana. reflexivity.
    Qed.
  End SET_KLEISLI.
End SET_MONAD.

Notation "{{ e ; x ∈ S }}" := (set_map (fun x => e) S)
  (at level 0, x ident, e at level 99, S at level 99, format "{{ e ; x ∈ S }}") : set_scope.

(** ** Knaster-Tarki Fixed Point Theorem *)
Module KTFP.
  Section KTFP.
    Context {L : Type} `{Lsl : SemiLattice L} 
            (f : L -> L) `{Hf: Monotonic f (ref ++> ref)}.

    Definition candidate x := x <= f x.

    Lemma candidate_apply x : candidate x -> candidate (f x).
    Proof.
      intros. monotonicity. assumption.
    Qed.
    
    Definition Candidate := {x | candidate x}.

    Definition gfp := lsup (fun c : Candidate  => `c).

    Lemma gfp_fixed : f gfp = gfp.
    Proof.
      assert (H: forall c : Candidate, `c <= f gfp).
      {
        intros c. destruct c as [l Hl] eqn:Hc. simpl. transitivity (f l). assumption.
        monotonicity. apply (sup_at c). subst. reflexivity.
      }
      assert (Hgfp: gfp <= f gfp).
      {
        eapply sup_lub. apply H.
      }
      apply antisymmetry; [| assumption].
      apply candidate_apply in Hgfp.
      apply (sup_at (exist _ (f gfp) Hgfp)). reflexivity.
    Qed.

    Lemma gfp_coind x :
      x <= f x -> x <= gfp.
    Proof.
      intros. apply (sup_at (exist _ x H)). reflexivity.
    Qed.
  End KTFP.
End KTFP.