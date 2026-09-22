Require Export structures.Posets.
Require Import interfaces.ConcreteCategory.

(* NOTE: This was created by first taking Jérémie's CDLattices and then 
removing all the data about infs. *)

(** * Join semi-lattices *)

(** ** Definition *)

Class SemiLattice (L : Type) :=
  {
    cdl_poset :> Poset L;

    lsup : forall {I}, (I -> L) -> L;

    lsup_sup {I} (u : I -> L) :> IsSup u (lsup u);
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
    intros Hi Hx. etransitivity; eauto using fsup_ub.
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