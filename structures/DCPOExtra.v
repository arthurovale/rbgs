Require Import coqrel.LogicalRelations.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import structures.Posets.
Require Import structures.DCPOs.

(** * Directed completeness without a least element *)

Class DirectedComplete `{PartialOrder} :=
  dcomplete : forall {I} (x : I -> P), inhabited I -> Directed x -> exists u, IsSup x u.

Global Instance eq_po (X : Type) : PartialOrder (@eq X) | 10.
Proof.
  split. typeclasses eauto. intros x y -> _. reflexivity.
Qed.

Global Instance eq_dcomplete (X : Type) : DirectedComplete (R := @eq X) | 10.
Proof.
  intros I x [i] Hx. exists (x i). split.
  - intros j. destruct (directed j i) as [k [-> <-]]. reflexivity.
  - intros y Hy. apply Hy.
Qed.

Global Instance dcpo_dcomplete `{DCPO} : DirectedComplete (R := lce).
Proof.
  intros I x _ Hx. exists (dsup x). apply dsup_is_sup.
Qed.

Section PROD.
  Context {P Q : Type} {R : relation P} {S : relation Q}
    `{!PartialOrder R} `{!PartialOrder S}
    `{!DirectedComplete (R := R)} `{!DirectedComplete (R := S)}.

  Global Instance prod_po : PartialOrder (R * S)%rel.
  Proof.
    split.
    - typeclasses eauto.
    - intros [x1 x2] [y1 y2] [Hxy1 Hxy2] [Hyx1 Hyx2]. cbn in *.
      f_equal; apply antisymmetry; auto.
  Qed.

  Global Instance prod_dcomplete : DirectedComplete (R := (R * S)%rel).
  Proof.
    intros I x HI Hx.
    assert (D1 : Directed (fun i => fst (x i))).
    { intros i j. destruct (directed i j) as [k [[H1 _] [H2 _]]]. exists k. auto. }
    assert (D2 : Directed (fun i => snd (x i))).
    { intros i j. destruct (directed i j) as [k [[_ H1] [_ H2]]]. exists k. auto. }
    destruct (dcomplete _ HI D1) as [u1 Hu1].
    destruct (dcomplete _ HI D2) as [u2 Hu2].
    exists (u1, u2). split.
    - intros i. split; cbn; [apply (sup_ub (IsSup := Hu1) i) | apply (sup_ub (IsSup := Hu2) i)].
    - intros [y1 y2] Hy. split; cbn.
      + apply (sup_lub (IsSup := Hu1)). intros i. apply (Hy i).
      + apply (sup_lub (IsSup := Hu2)). intros i. apply (Hy i).
  Qed.
End PROD.

(** * The lift of a directed-complete partial order *)

(** The carrier records the order as a phantom parameter, so that the flat
  domain [lift X eq] and the lift [lift D lce] of a DCPO [D] are
  distinguishable by instance resolution. *)

Inductive lift_raw (P : Type) :=
  | lift_bot
  | lift_el (x : P).

Arguments lift_bot {P}.
Arguments lift_el {P} x.

Definition lift (P : Type) (R : relation P) : Type := lift_raw P.

Section LIFT.
  Context `{PartialOrder} `{!DirectedComplete}.

  Inductive lift_lce : lift P R -> lift P R -> Prop :=
  | lift_lce_bot t : lift_lce lift_bot t
  | lift_lce_el x y : R x y -> lift_lce (lift_el x) (lift_el y).

  Global Instance lift_po : PartialOrder lift_lce.
  Proof.
    split.
    - split.
      + intros [| x]; constructor. reflexivity.
      + intros t u v Htu Huv. inversion Htu; subst; inversion Huv; subst; constructor.
        transitivity y; assumption.
    - intros t u Htu Hut. inversion Htu; subst; inversion Hut; subst; try reflexivity.
      f_equal. apply antisymmetry; assumption.
  Qed.

  (** *** Directed suprema *)

  (** The elements of [P] occurring in a family [x] form a family [lift_els x]. *)

  Definition lift_els {I} (x : I -> lift P R) : {p : P | exists i, x i = lift_el p} -> P :=
    fun j => proj1_sig j.

  Global Instance lift_els_directed {I} (x : I -> lift P R) `{!Directed x} :
    Directed (lift_els x).
  Proof.
    intros [p [i Hi]] [q [j Hj]].
    destruct (directed i j) as [k [Hik Hjk]].
    rewrite Hi in Hik. rewrite Hj in Hjk.
    destruct (x k) as [| r] eqn:Hk; inversion Hik; inversion Hjk; subst.
    exists (exist _ r (ex_intro _ k Hk)). cbn. split; assumption.
  Qed.

  (** When some element occurs, the lifted supremum of [lift_els x] is the
    supremum of [x]. *)

  Lemma lift_els_sup {I} (x : I -> lift P R) `{!Directed x} i0 a0 (u : P) :
    x i0 = lift_el a0 -> IsSup (lift_els x) u -> IsSup x (lift_el u).
  Proof.
    intros Hi0 Hu. split.
    - intros i. destruct (x i) eqn:Hi; [constructor |].
      constructor. exact (sup_ub (u := u) (exist _ x0 (ex_intro _ i Hi))).
    - intros z Hz. destruct z as [| w].
      + specialize (Hz i0). rewrite Hi0 in Hz. inversion Hz.
      + constructor. apply sup_lub. intros [p [i Hi]]. cbn.
        specialize (Hz i). rewrite Hi in Hz. inversion Hz; subst. assumption.
  Qed.

  Lemma lift_directed_sup {I} (x : I -> lift P R) `{!Directed x} :
    exists u, IsSup x u.
  Proof.
    destruct (classic (exists i a, x i = lift_el a)) as [[i0 [a0 Hi0]] | Hbot].
    - destruct (dcomplete (lift_els x) (inhabits (exist _ a0 (ex_intro _ i0 Hi0))) _) as [u Hu].
      exists (lift_el u). exact (lift_els_sup x i0 a0 u Hi0 Hu).
    - exists lift_bot. split.
      + intros j. destruct (x j) eqn:Hj; [constructor |].
        exfalso. apply Hbot. exists j, x0. exact Hj.
      + intros y _. constructor.
  Qed.

  Definition lift_dsup {I} (x : I -> lift P R) `{!Directed x} : lift P R :=
    epsilon (inhabits lift_bot) (fun u => IsSup x u).

  Global Program Instance lift_dcpo : DCPO (lift P R) :=
    {|
      lce := lift_lce;
      dsup := @lift_dsup;
    |}.
  Next Obligation.
    intros. unfold lift_dsup. apply epsilon_spec. apply lift_directed_sup. assumption.
  Qed.

  Lemma lift_bot_eq : bot = (lift_bot : lift P R).
  Proof.
    apply (antisymmetry (R := lce)); [apply bot_lb | apply lift_lce_bot].
  Qed.

  (** Either no element occurs and the supremum is [bot], or the supremum
    is the lift of the supremum of the occurring elements. *)

  Lemma lift_dsup_cases {I} (x : I -> lift P R) `{!Directed x} :
    dsup x = lift_bot \/
    exists u, IsSup (lift_els x) u /\ dsup x = lift_el u /\ exists i a, x i = lift_el a.
  Proof.
    destruct (classic (exists i a, x i = lift_el a)) as [[i0 [a0 Hi0]] | Hbot].
    - right. destruct (dcomplete (lift_els x) (inhabits (exist _ a0 (ex_intro _ i0 Hi0))) _) as [u Hu].
      pose proof (lift_els_sup x i0 a0 u Hi0 Hu) as Hx.
      exists u. split; [exact Hu | split; [| eauto]].
      apply (antisymmetry (R := lce)).
      + apply dsup_lub. apply (sup_ub (IsSup := Hx)).
      + apply (sup_lub (IsSup := Hx)). intros i. change (lce (x i) (dsup x)). apply dsup_ub.
    - left. apply (antisymmetry (R := lce)); [| apply lift_lce_bot].
      apply dsup_lub. intros j. destruct (x j) eqn:Hj; [constructor |].
      exfalso. apply Hbot. exists j, x0. exact Hj.
  Qed.
End LIFT.

(** * Kleisli extension *)

Section LIFT_EXT.
  Context `{PartialOrder} `{!DirectedComplete} {D} `{Ddcpo : DCPO D}.

  Definition ext (f : P -> D) (t : lift P R) : D :=
    match t with
    | lift_bot => bot
    | lift_el x => f x
    end.

  Lemma ext_emb (f : P -> D) (x : P) :
    ext f (lift_el x) = f x.
  Proof.
    reflexivity.
  Qed.

  Lemma ext_bot (f : P -> D) :
    ext f bot = bot.
  Proof.
    rewrite lift_bot_eq. reflexivity.
  Qed.

  (** [ext f] is strict Scott-continuous as soon as [f] is monotonic and
    preserves the suprema of inhabited directed families. *)

  Lemma ext_sc (f : P -> D)
      (Hmon : Monotonic f (R ++> lce))
      (Hsup : forall {I} (x : I -> P) (u : P), inhabited I -> Directed x -> IsSup x u ->
                forall y, (forall i, lce (f (x i)) y) -> lce (f u) y) :
    ScottContinuous true (ext f).
  Proof.
    split.
    - intros t u Htu. change (lift_lce t u) in Htu.
      inversion Htu; subst; cbn; [apply bot_lb | apply Hmon; assumption].
    - intros J HJ x Dx y Hy.
      destruct (lift_dsup_cases x) as [-> | [u [Hu [-> [i0 [a0 Hi0]]]]]].
      + cbn. apply bot_lb.
      + cbn. apply (Hsup _ (lift_els x) u (inhabits (exist _ a0 (ex_intro _ i0 Hi0))) _ Hu).
        intros [p [i Hi]]. cbn. specialize (Hy i). rewrite Hi in Hy. exact Hy.
  Qed.
End LIFT_EXT.

(** ** The flat domain: every function out of a set extends. *)

Global Instance flat_ext_sc {X D} `{DCPO D} (f : X -> D) :
  ScottContinuous true (ext (R := eq) f).
Proof.
  apply ext_sc.
  - intros a b ->. reflexivity.
  - intros I x u [i] Hx Hu y Hy.
    pose proof (sup_ub (IsSup := Hu) i) as <-. apply Hy.
Qed.

(** ** The lift monad: non-strict continuous maps extend to strict ones. *)

Global Instance lift_ext_sc {P D} `{DCPO P} `{DCPO D} (f : P -> D) `{!ScottContinuous false f} :
  ScottContinuous true (ext (R := lce) f).
Proof.
  apply ext_sc.
  - apply sc_lce.
  - intros I x u HI Hx Hu y Hy.
    replace u with (dsup x).
    + apply (sc_lub (HJ := (HI : ArityCondition false I))). exact Hy.
    + apply (antisymmetry (R := lce)).
      * apply dsup_lub. apply (sup_ub (IsSup := Hu)).
      * apply (sup_lub (IsSup := Hu)). apply dsup_ub.
Qed.

