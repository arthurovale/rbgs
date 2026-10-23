Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.KDCPOs.
Require Import structures.DCPOSLs.
Require Import Stdlib.Logic.ProofIrrelevance.

Local Open Scope em_scope.

(** * Labelled Coalgebras *)
(** Here we provided a generic interface for labelled coalgebras. *)

(** A transiton shape should formally be a category [Lab] of labels together
  with a bifunctor [T : Lab x PPoset -> PPoset]. *)
Module LCoalg (Lab : Category) (Tfunc : Bifunctor Lab PPoset PPoset).

  (** First, we use some definitions to peel through the concrete category interface
    for pointed posets exposing the bare functions. *)
  Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
  Local Abbreviation id := (fun x => x).

  (** A labelled coalgebra requires one to provide a transition shape [T] *)
  (** To handle divergence, the transition shape is required to be a functor
    [T : Lab -> PPoset -> PPoset] such that if the set of states [S] forms a
    pointed poset then the transition shape domain forms a pointed poset.
    Here [Lab] is the space of event labels. *)
  Definition T (E : Lab.t) (S : Type) `{PPoset S} : Type :=
    PPoset.carrier (Tfunc.omap E (PPoset.mkt S)).
  #[global] Typeclasses Opaque T.

  Local Instance T_ppo E S `{PPoset S} : PPoset (T E S) :=
    PPoset.structure (Tfunc.omap E (PPoset.mkt S)).
  Global Hint Extern 15 (PPoset (T _ _)) => simple eapply @T_ppo : typeclass_instances.

  Definition T_map {E E' S S'} `{PPoset S} `{PPoset S'}
      (l : Lab.m E E') (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} : T E S -> T E' S' :=
    PPoset.apply _ _ (Tfunc.fmap l (@PPoset.mkm (PPoset.mkt S) (PPoset.mkt S') h _)).

  Lemma T_map_sc {E E' S S'} `{PPoset S} `{PPoset S'}
      (l : Lab.m E E') (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} :
    PreContinuous (RA := pref) (RB := pref) (T_map l h).
  Proof. exact (PPoset.morphism _ _ (Tfunc.fmap l (@PPoset.mkm (PPoset.mkt S) (PPoset.mkt S') h _))). Qed.

  Lemma T_map_id E S `{PPoset S} :
    T_map (Lab.id E) id = id.
  Proof.
    unfold T_map.
    replace (@PPoset.mkm (PPoset.mkt S) (PPoset.mkt S) (fun s => s) _) with (PPoset.id (PPoset.mkt S))
      by (apply PPoset.meq; reflexivity).
    rewrite Tfunc.fmap_id. reflexivity.
  Qed.

  Lemma T_map_compose {E E' E'' S S' S''} `{PPoset S} `{PPoset S'} `{PPoset S''}
      (l : Lab.m E E') (l' : Lab.m E' E'') (h : S -> S') (h' : S' -> S'')
      `{!PreContinuous (RA := pref) (RB := pref) h} `{!PreContinuous (RA := pref) (RB := pref) h'} :
    T_map (Lab.compose l' l) (fun s => h' (h s)) = (fun t => T_map l' h' (T_map l h t)).
  Proof.
    unfold T_map.
    replace (@PPoset.mkm (PPoset.mkt S) (PPoset.mkt S'') (fun s => h' (h s)) _)
      with (PPoset.compose (@PPoset.mkm (PPoset.mkt S') (PPoset.mkt S'') h' _)
                           (@PPoset.mkm (PPoset.mkt S) (PPoset.mkt S') h _))
      by (apply PPoset.meq; reflexivity).
    rewrite Tfunc.fmap_compose. reflexivity.
  Qed.

  (** A labelled (non-deterministic) coalgebra of shape [T] then consists of:
  - A non-deterministic transition function [trans : S -> convex_set (T E S)]
  - A choice of initial states
  - Proofs that the transition functions is "pre-continuous", i.e. monotonic and
    strict. The transition function should be continuous. However,
    due to the same sizing issues related to non-deterministic choice we
    would need to require something like:
    [trans_kcont : exists K, KContinuous K trans]
    To make matters simpler for now, we make this "pre-continuity" requirement.
  *)
  Record lcoalg (E : Lab.t) S {Spp : PPoset S} :=
    {
      trans :> S -> convex_set (T E S);
      init : convex_set S;
      trans_pc :: PreContinuous (RA := pref) (RB := em_le) trans;
    }.

  Lemma lcoalg_ext {E S} {Spp : PPoset S} (a b : lcoalg E S) :
    trans E S a = trans E S b -> init E S a = init E S b -> a = b.
  Proof.
    destruct a, b; cbn. intros -> ->. f_equal; apply proof_irrelevance.
  Qed.

  Arguments trans {E S Spp} _.
  Arguments init {E S Spp} _.
  Arguments trans_pc {E S Spp} _.
  Arguments lcoalg_ext {E S Spp} _ _.

  (**
    I expect that for the most part base objects will be built out of the flat
    DCPO [lift S eq] over a set of states [S]. The following shows that in that
    case a labelled coalgebra may be defined directly as simply a transition
    function and a (plain) set of initial states.
  *)
  Definition flat_lcoalg {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) :
    lcoalg E (lift X eq) :=
    {|
      trans := lift_ext (RD := em_le) f;
      init := {{ t | exists x, t = lift_el x /\ i x }};
      trans_pc := lift_ext_flat_pc f;
    |}.

  (** Some useful technical lemmas about flat coalgebras *)
  Lemma flat_lcoalg_bot {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) :
    flat_lcoalg f i lift_bot = bot.
  Proof. reflexivity. Qed.

  Lemma flat_lcoalg_el {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) (x : X) :
    flat_lcoalg f i (lift_el x) = f x.
  Proof. reflexivity. Qed.

Section LCOALG_DCPO.
  Context {E : Lab.t} {S : Type} {Sdcpo : DCPO S}
    {Tdc : DirectedComplete (R := pref (P := T E S))}.
  Local Instance T_dcpo : DCPO (T E S) := dc_dcpo.
  Context {HS : EMComplete S} {HT : EMComplete (T E S)}.
  Local Instance TES_em_dcpo : DCPO (convex_set (T E S)) := em_dcpo_complete.
  Local Instance S_em_dcpo : DCPO (convex_set S) := em_dcpo_complete.

  Definition lcoalg_le (α β : lcoalg E S) : Prop :=
    lce (trans α) (trans β) /\ lce (init α) (init β).

  Local Instance lcoalg_le_po : PartialOrder lcoalg_le.
  Proof.
    split.
    - split.
      + intros α. split; reflexivity.
      + intros α β γ [H1 H2] [H1' H2']. split; etransitivity; eauto.
    - intros α β [H1 H2] [H1' H2']. apply lcoalg_ext; apply antisymmetry; assumption.
  Qed.

  Local Instance lcoalg_directed_trans {I} (x : I -> lcoalg E S)
      (Hx : Directed (R := lcoalg_le) x) :
    Directed (fun i => trans (x i)).
  Proof.
    intros i j. destruct (Hx i j) as [k [[H1 _] [H2 _]]]. exists k. auto.
  Qed.

  Local Instance lcoalg_directed_init {I} (x : I -> lcoalg E S)
      (Hx : Directed (R := lcoalg_le) x) :
    Directed (fun i => init (x i)).
  Proof.
    intros i j. destruct (Hx i j) as [k [[_ H1] [_ H2]]]. exists k. auto.
  Qed.

  Lemma lcoalg_dsup_pc {I} (x : I -> lcoalg E S) (Hx : Directed (R := lcoalg_le) x) :
    PreContinuous (RA := pref) (RB := em_le) (dsup (fun i => trans (x i))).
  Proof.
    split.
    - intros s s' Hs.
      apply (dsup_lub (H := TES_em_dcpo) (fun i => trans (x i) s)). intros i.
      etransitivity; [apply (pc_mon (PreContinuous := trans_pc (x i))); exact Hs |].
      apply (dsup_ub (H := TES_em_dcpo) (fun i => trans (x i) s')).
    - unfold Strict.
      apply (antisymmetry (R := lce)).
      + apply (dsup_lub (H := TES_em_dcpo) (fun i => trans (x i) bot)). intros i.
        rewrite (strict_bot (f := trans (x i))). reflexivity.
      + apply bot_lb.
  Qed.

  Definition lcoalg_dsup {I} (x : I -> lcoalg E S) (Hx : Directed (R := lcoalg_le) x) :
    lcoalg E S :=
    {|
      trans := dsup (fun i => trans (x i));
      init := dsup (fun i => init (x i));
      trans_pc := lcoalg_dsup_pc x Hx;
    |}.

  Lemma lcoalg_dsup_issup {I} (x : I -> lcoalg E S) (Hx : Directed (R := lcoalg_le) x) :
    IsSup (R := lcoalg_le) x (lcoalg_dsup x Hx).
  Proof.
    split.
    - intros i. split.
      + exact (dsup_ub (fun i => trans (x i)) i).
      + exact (dsup_ub (fun i => init (x i)) i).
    - intros y Hy. split.
      + exact (dsup_lub (fun i => trans (x i)) (trans y) (fun i => proj1 (Hy i))).
      + exact (dsup_lub (fun i => init (x i)) (init y) (fun i => proj2 (Hy i))).
  Qed.

  Lemma lcoalg_bot_pc : PreContinuous (RA := pref) (RB := em_le (P := T E S)) (fun _ : S => bot).
  Proof.
    split.
    - intros s s' _. reflexivity.
    - reflexivity.
  Qed.

  Definition lcoalg_bot : lcoalg E S :=
    {| trans := fun _ => bot; init := bot; trans_pc := lcoalg_bot_pc |}.

  Lemma lcoalg_bot_lb (α : lcoalg E S) : lcoalg_le lcoalg_bot α.
  Proof.
    split.
    - intros s. apply bot_lb.
    - apply bot_lb.
  Qed.

  Local Instance lcoalg_pointed : Pointed lcoalg_le :=
    {| bot := lcoalg_bot; bot_lb := lcoalg_bot_lb |}.

  Local Instance lcoalg_dcpo : DCPO (lcoalg E S) :=
    {|
      lce := lcoalg_le;
      lce_po := lcoalg_le_po;
      dsup := @lcoalg_dsup;
      dsup_is_sup := @lcoalg_dsup_issup;
      dcpo_pointed := lcoalg_pointed;
    |}.
  End LCOALG_DCPO.

  Global Hint Extern 1 (DCPO (lcoalg _ _)) => simple eapply @lcoalg_dcpo : typeclass_instances.

  Section LCOALG_MOR.

    (** A standard coalgebra morphism *)
    Record lcoalg_mor {E S E' S'} {Spp : PPoset S} {Spp' : PPoset S'}
        (α : lcoalg E S) (β : lcoalg E' S') :=
      {
        lab_mor : Lab.m E E';
        st_mor :> S -> S';

        (** We can require the stronger property [exists K, KContinuous K st_mor].
          Since it might not be necessary, for now I require the weaker property that
          it be pre-continuous. *)
        st_mor_mon : PreContinuous (RA := pref) (RB := pref) st_mor;

        homomorphism_eq : α ;; convex_map (T_map lab_mor st_mor) = st_mor ;; β;
        init_eq : convex_map st_mor (init α) = init β;
      }.

    (** TODO: compose, id, etc *)
  End LCOALG_MOR.

  (** A Coalgebra is said safe if it never makes an empty choice, i.e.
    it never gets stuck. *)
  Definition safe {E S} {Spp : PPoset S} (α : lcoalg E S) :=
    forall s, exists t, α s t.

  (** TODO: Kleisli morphisms conditional on safe *)
End LCoalg.
