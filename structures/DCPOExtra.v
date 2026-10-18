Require Import coqrel.LogicalRelations.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Logic.ClassicalChoice.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.KDCPOs.

(** * DCPOs without a least element *)

Class DirectedComplete `{PartialOrder} :=
  dcomplete : forall {I} (x : I -> P), inhabited I -> Directed x -> exists u, IsSup x u.

Global Hint Mode DirectedComplete ! - - : typeclass_instances.

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

(** * Strict maps between DCPOs *)

(** [Strict] is defined over pointed orders in [Posets]; here are the two
  derivations for DCPOs. Strict Scott-continuity implies strictness. *)
Global Instance sc_strict {A B} `{DCPO A} `{DCPO B} (f : A -> B) `{!ScottContinuous true f} :
  Strict f := sc_bot.

(** So does [K]-continuity for inhabited [K]. *)
Definition kcont_strict {K} (inK : inhabited K) {A B} `{DCPO A} `{DCPO B} (f : A -> B)
    `{!KContinuous K f} : Strict f := kc_strict inK f.

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
    { intros i j. destruct (Hx i j) as [k [[H1 _] [H2 _]]]. exists k. auto. }
    assert (D2 : Directed (fun i => snd (x i))).
    { intros i j. destruct (Hx i j) as [k [[_ H1] [_ H2]]]. exists k. auto. }
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
  Context `{PartialOrder} `{!DirectedComplete (R := R)}.

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

  Local Program Instance lift_dcpo : DCPO (lift P R) :=
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

Global Hint Extern 1 (DCPO (lift _ _)) => simple eapply @lift_dcpo : typeclass_instances.

(** * Kleisli extension *)

Section LIFT_EXT.
  Context `{PartialOrder} `{!DirectedComplete (R := R)}.

  (** The extension only needs a least element in its codomain. *)

  Section POINTED_CODOMAIN.
    Context {D} {RD : relation D} `{!PartialOrder RD} `{!Pointed RD}.

    Definition lift_ext (f : P -> D) (t : lift P R) : D :=
      match t with
      | lift_bot => bot
      | lift_el x => f x
      end.

    Lemma lift_ext_el (f : P -> D) (x : P) :
      lift_ext f (lift_el x) = f x.
    Proof.
      reflexivity.
    Qed.

    Global Instance lift_ext_strict (f : P -> D) : Strict (RB := RD) (lift_ext f).
    Proof.
      unfold Strict. rewrite lift_bot_eq. reflexivity.
    Qed.

    (** [lift_ext] is monotone in the extended map, pointwise. *)
    Lemma lift_ext_mon_r (g g' : P -> D) :
      (forall p, RD (g p) (g' p)) ->
      forall t, RD (lift_ext g t) (lift_ext g' t).
    Proof.
      intros Hg [| p]; [reflexivity | apply Hg].
    Qed.
  End POINTED_CODOMAIN.

  (** Continuity needs a DCPO in the codomain. [lift_ext f] is strict
    Scott-continuous as soon as [f] is monotonic and preserves the suprema
    of inhabited directed families. *)

  Section DCPO_CODOMAIN.
    Context {D} `{Ddcpo : DCPO D}.

    Lemma lift_ext_sc (f : P -> D)
        (Hmon : Monotonic f (R ++> lce))
        (Hsup : forall {I} (x : I -> P) (u : P), inhabited I -> Directed x -> IsSup x u ->
                  forall y, (forall i, lce (f (x i)) y) -> lce (f u) y) :
      ScottContinuous true (lift_ext (RD := lce) f).
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
  End DCPO_CODOMAIN.
End LIFT_EXT.

(** ** The flat domain: every function out of a set extends. *)

(** Out of a flat domain, every extension is monotone into any pointed
  order, since the only strict inequalities start at the bottom. *)
Lemma lift_ext_flat_mon {X D} {RD : relation D} `{!PartialOrder RD} `{!Pointed RD} (f : X -> D) :
  Monotonic (lift_ext (R := eq) (RD := RD) f) (lce ++> RD).
Proof.
  intros t u Htu. change (lift_lce t u) in Htu.
  inversion Htu; subst; cbn; [apply bot_lb | reflexivity].
Qed.

Global Instance lift_ext_flat_sc {X D} `{DCPO D} (f : X -> D) :
  ScottContinuous true (lift_ext (R := eq) (RD := lce) f).
Proof.
  apply lift_ext_sc.
  - intros a b ->. reflexivity.
  - intros I x u [i] Hx Hu y Hy.
    pose proof (sup_ub (IsSup := Hu) i) as <-. apply Hy.
Qed.

(** ** The lift monad: non-strict continuous maps extend to strict ones. *)

Global Instance lift_ext_dcpo_sc {P D} `{DCPO P} `{DCPO D} (f : P -> D) `{!ScottContinuous false f} :
  ScottContinuous true (lift_ext (R := lce) (RD := lce) f).
Proof.
  apply lift_ext_sc.
  - apply sc_lce.
  - intros I x u HI Hx Hu y Hy.
    replace u with (dsup x).
    + apply (sc_lub (HJ := (HI : ArityCondition false I))). exact Hy.
    + apply (antisymmetry (R := lce)).
      * apply dsup_lub. apply (sup_ub (IsSup := Hu)).
      * apply (sup_lub (IsSup := Hu)). apply dsup_ub.
Qed.

(** * Finitary DCPOs *)

(** A DCPO is finitary when every element has finitely many elements below
  it. Finitary DCPOs are used to build DCPOSLs out of DCPOs. *)

Class Finitary `{PartialOrder} := 
  finitary : forall d : P, exists l : list P, forall a, R a d <-> In a l.  

(** Instance search for [Finitary] must know the relation: otherwise
  [lift_finitary] below applies to itself indefinitely. *)
Global Hint Mode Finitary ! ! - : typeclass_instances.

(** From a point-of-view of partial orders as causal structures, this condition 
may be read as stating that every piece of information is can be justified 
by a finite amount of past information. *)

(** So we may use the finitary assumption effectively, we note that in any DCPO,
  any finite subset of a directed set admits an upper bound in the directed set.
  This generalizes the directedness property state on pairs to finite sets.  *)

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

(** **** Finitary DCPOs satisfy the ascending chain condition. *)

(** First, note that ascending chains are directed sets *)

Lemma monotone_seq_directed `{DCPO} (g : nat -> P) :
  (forall n, lce (g n) (g (S n))) -> Directed g.
Proof.
  intros Hg.
  assert (Hmon : forall n m, (n <= m)%nat -> lce (g n) (g m)).
  { intros n m Hnm. induction Hnm. reflexivity. transitivity (g m); auto. }
  intros n m. exists (Nat.max n m).
  split; apply Hmon. apply Nat.le_max_l. apply Nat.le_max_r.
Qed.

(** So we prove the following generalization of the ascending chain condition *)

Lemma finitary_DCPO_acc `{DCPO} `{!Finitary (R := lce)} {I} `{inhabited I} (x : I -> P) `{!Directed x} :
  exists i, forall j, lce (x j) (x i).
Proof.
  destruct (finitary (dsup x)) as [below Hbelow].
  destruct (directed_bounded_in (inhabited0 := inhabited0)  x below) as [i Hi].
  exists i. intros j. apply Hi, Hbelow, dsup_ub.
Qed.

(** Consequently, a strict monotonic map out of a finitary DCPO is
  Scott-continuous. *)

Lemma finitary_sc {A B} `{DCPO A} `{!Finitary (R := lce (P := A))} `{DCPO B} (f : A -> B)
    (Hmon : Monotonic f (lce ++> lce)) `{!Strict f} :
  ScottContinuous true f.
Proof.
  split; [exact Hmon |].
  intros J HJ x Dx y Hy.
  destruct (classic (inhabited J)) as [Hinh | Hemp].
  - destruct (finitary_DCPO_acc x (inhabited0 := Hinh)) as [i Hi].
    replace (dsup x) with (x i); [apply Hy |].
    apply antisymmetry; [apply dsup_ub | apply dsup_lub; exact Hi].
  - replace (dsup x) with (bot : A); [rewrite (strict_bot (f := f)); apply bot_lb |].
    apply antisymmetry; [apply bot_lb |].
    apply dsup_lub. intros j. exfalso. apply Hemp. exact (inhabits j).
Qed.

(** A key fact about finitary DCPOs is that any non-empty subset admits a maximal element *)

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

(** ** Finitary instances *)

(** A discrete order is finitary, and so is the lift of a finitary order. *)

Global Instance eq_finitary (X : Type) : Finitary (R := @eq X) | 10.
Proof.
  intros d. exists (cons d nil). intros a. split.
  - intros ->. left. reflexivity.
  - intros [<- | []]. reflexivity.
Qed.

Global Instance lift_finitary {P R} `{PartialOrder P R} `{!DirectedComplete (R := R)}
    `{!Finitary (R := R)} :
  Finitary (R := lce (P := lift P R)).
Proof.
  intros d. destruct d as [| p].
  - exists (cons lift_bot nil). intros x. split.
    + intros H'. inversion H'; subst. left. reflexivity.
    + intros [<- | []]. constructor.
  - destruct (finitary p) as [l Hl].
    exists (cons lift_bot (map lift_el l)). intros x. split.
    + intros H'. inversion H' as [| x' y' Hp]; subst; [left; reflexivity |].
      right. apply in_map_iff. exists x'. split; [reflexivity | apply Hl; exact Hp].
    + intros [<- | Hin]; [constructor |].
      apply in_map_iff in Hin. destruct Hin as [p' [<- Hp']]. constructor. apply Hl. exact Hp'.
Qed.
