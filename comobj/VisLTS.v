From Coinduction Require Import all.
Import CoindNotations.

Require Import interfaces.Category.
Require Import interfaces.Functor.

Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.KDCPOs.
Require Import structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import Stdlib.Logic.FunctionalExtensionality.

Require Import comobj.SilEvents.
Import SilEvents.

Require Import comobj.LCoalg.
Require Import comobj.SilLTS.

Local Open Scope em_scope.


(** * The Loudening Operator *)

Open Scope tsil_scope.

Local Abbreviation id := (fun x => x).

(** ** Behaviour Objects *)

(** A behaviour object differs from a communicating object in that it has no
  silent transitions *)
Definition Tvis (E S : Type) {Spp : PPoset S} : Type :=
  lift (E * S) (eq * pref)%rel.
#[global] Typeclasses Opaque Tvis.

Section TVIS.
  Context {E S : Type} {Spp : PPoset S}.
  Local Instance Tvis_ppo : PPoset (Tvis E S) := lift_ppo.

  Lemma Tvis_ppo_bot_eq : (bot : Tvis E S) = ↺.
  Proof. apply lift_ppo_bot_eq. Qed.

  Section TVIS_DCPO.
    Context {Sdc : DirectedComplete (R := pref (P := S))}.
    Local Instance Tvis_dcpo : DCPO (Tvis E S) := lift_dcpo.

    Lemma Tvis_bot_eq : (bot : Tvis E S) = ↺.
    Proof. apply lift_bot_eq. Qed.

    Global Instance Tvis_finitary `{!Finitary (R := pref (P := S))} :
      Finitary (R := lce (P := Tvis E S)).
    Proof.
      intros d. destruct d as [| [e s]].
      - exists [↺]. intros x. split.
        + intros H. inversion H; subst. left. reflexivity.
        + intros [<- | []]. constructor.
      - destruct (finitary s) as [l Hl].
        exists (↺ :: map (fun s' => - e -> s') l). intros x. split.
        + intros H. inversion H as [| x' y' Hp]; subst; [left; reflexivity |].
          destruct x' as [e' s']. destruct Hp as [He Hs]. cbn in He, Hs. subst e'.
          right. apply in_map_iff. exists s'. split; [reflexivity | apply Hl; exact Hs].
        + intros [<- | Hin]; [constructor |].
          apply in_map_iff in Hin. destruct Hin as [s' [<- Hs']].
          constructor. split; [reflexivity | apply Hl; exact Hs'].
    Qed.
  End TVIS_DCPO.

  (** Note that [Tsil E S] ≅ [TVis E S] ⊕ [lift S].
    As a result, [TSil] supports a copairing operation. *)
  Definition Tsil_copair {X} (fl : Tvis E S -> X) (fr : S -> X) : (Tsil E S -> X) :=
    fun t =>
      match t with
      | ↺ => fl ↺
      | -'e-> s => fl (-e-> s)
      | -ɛ-> s => fr s
      end.

  (** The copairing is monotone in its silent branch, pointwise. *)
  Lemma Tsil_copair_mon_r {X} {RX : relation X} `{!PartialOrder RX}
      (fl : Tvis E S -> X) (fr fr' : S -> X) :
    (forall c, RX (fr c) (fr' c)) ->
    forall t, RX (Tsil_copair fl fr t) (Tsil_copair fl fr' t).
  Proof.
    intros Hfr [| [[e |] c]]; [reflexivity | reflexivity | apply Hfr].
  Qed.

  Lemma Tsil_copair_mon {X} {RX : relation X} `{!PartialOrder RX}
      (fl : Tvis E S -> X) (fr : S -> X)
      (Hl : Monotonic fl (pref ++> RX)) (Hr : Monotonic fr (pref ++> RX))
      (Hglue : RX (fl ↺) (fr bot)) :
    Monotonic (Tsil_copair fl fr) (pref ++> RX).
  Proof.
    intros t u Htu. inversion Htu as [? | x y Hxy]; subst.
    - destruct u as [| [[e |] c]]; cbn.
      + reflexivity.
      + apply Hl. constructor.
      + transitivity (fr bot); [exact Hglue |]. apply Hr. apply bot_lb.
    - destruct x as [[e |] c], y as [[e' |] c']; destruct Hxy as [He Hc]; cbn in *;
        try discriminate He.
      + injection He as <-. apply Hl. constructor. split; [reflexivity | exact Hc].
      + apply Hr. exact Hc.
  Qed.

  Global Instance Tsil_copair_strict {X} {RX : relation X} `{!PartialOrder RX} `{!Pointed RX}
      (fl : Tvis E S -> X) (fr : S -> X) `{!Strict (RA := pref) (RB := RX) fl} :
    Strict (RA := pref) (RB := RX) (Tsil_copair fl fr).
  Proof.
    unfold Strict. rewrite Tsil_ppo_bot_eq. change (fl ↺ = bot).
    rewrite <- Tvis_ppo_bot_eq. apply strict_bot.
  Qed.

  Lemma Tsil_copair_pc {X} {RX : relation X} `{!PartialOrder RX} `{!Pointed RX}
      (fl : Tvis E S -> X) (fr : S -> X)
      `{!PreContinuous (RA := pref) (RB := RX) fl} (Hr : Monotonic fr (pref ++> RX))
      (Hglue : RX (fl ↺) (fr bot)) :
    PreContinuous (RA := pref) (RB := RX) (Tsil_copair fl fr).
  Proof.
    split.
    - apply Tsil_copair_mon; [exact (pc_mon (f := fl)) | exact Hr | exact Hglue].
    - exact (Tsil_copair_strict fl fr).
  Qed.

  (** By the same isomorphism above, [Tvis] injects into [Tsil] by a map
    isomorphic to the left coprojection. *)
  Definition tvis_tsil (t : Tvis E S) : Tsil E S :=
    match t with
    | ↺ => ↺
    | -e-> c => -'e-> c
    end.

  (** the injection [tvis_tsil] has a retract forming and embedding-projection pair *)
  Definition tsil_tvis : Tsil E S -> Tvis E S :=
    Tsil_copair (fun x => x) (fun x => ↺).

  Lemma tvis_tsil_retract : tvis_tsil ;; tsil_tvis = id.
  Proof.
    apply functional_extensionality. intros [ | [e s]]; reflexivity.
  Qed.

  Lemma tvis_tsil_proj (t : Tsil E S) : pref ((tsil_tvis ;; tvis_tsil) t) t.
  Proof.
    destruct t as [| [[e |] s]]; cbn.
    - constructor.
    - constructor. split; reflexivity.
    - constructor.
  Qed.

  (** Both maps of the embedding-projection pair are pre-continuous *)

  Lemma tvis_tsil_mon : Monotonic tvis_tsil (pref ++> pref).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [e c], y as [e' c']; destruct H0 as [He Hc]; cbn in *; subst.
    constructor. split; [reflexivity | exact Hc].
  Qed.

  Lemma tsil_tvis_mon : Monotonic tsil_tvis (pref ++> pref).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [[e |] c], y as [[e' |] c']; destruct H0 as [He Hc]; cbn in *;
      try discriminate He; try constructor.
    injection He as <-. split; [reflexivity | exact Hc].
  Qed.

  Lemma tvis_tsil_strict : Strict (RA := pref) (RB := pref) tvis_tsil.
  Proof.
    unfold Strict. rewrite Tvis_ppo_bot_eq, Tsil_ppo_bot_eq. reflexivity.
  Qed.

  Lemma tsil_tvis_strict : Strict (RA := pref) (RB := pref) tsil_tvis.
  Proof.
    unfold Strict. rewrite Tsil_ppo_bot_eq, Tvis_ppo_bot_eq. reflexivity.
  Qed.

  Global Instance tvis_tsil_pc : PreContinuous (RA := pref) (RB := pref) tvis_tsil :=
    {| pc_mon := tvis_tsil_mon; pc_strict := tvis_tsil_strict |}.

  Global Instance tsil_tvis_pc : PreContinuous (RA := pref) (RB := pref) tsil_tvis :=
    {| pc_mon := tsil_tvis_mon; pc_strict := tsil_tvis_strict |}.

  Section TVIS_SC.
    Context {Sdc : DirectedComplete (R := pref (P := S))} `{!Finitary (R := pref (P := S))}.
    Local Existing Instance Tvis_dcpo.

    Lemma Tsil_copair_sc {X} `{DCPO X}
        (fl : Tvis E S -> X) (fr : S -> X)
        `{!PreContinuous (RA := pref) (RB := lce) fl} (Hr : Monotonic fr (pref ++> lce))
        (Hglue : lce (fl ↺) (fr bot)) :
      ScottContinuous true (Tsil_copair fl fr).
    Proof.
      exact (finitary_sc (Tsil_copair fl fr) (Hf := Tsil_copair_pc fl fr Hr Hglue)).
    Qed.

    Global Instance tvis_tsil_sc : ScottContinuous true tvis_tsil :=
      finitary_sc tvis_tsil (Hf := tvis_tsil_pc).

    Global Instance tsil_tvis_sc : ScottContinuous true tsil_tvis :=
      finitary_sc tsil_tvis (Hf := tsil_tvis_pc).
  End TVIS_SC.
End TVIS.

Global Hint Extern 15 (PPoset (Tvis _ _)) => simple eapply @Tvis_ppo : typeclass_instances.
Global Hint Extern 1 (DCPO (Tvis _ _)) => simple eapply @Tvis_dcpo : typeclass_instances.

(** A visible LTS is then a labelled coalgebra with visible transitions *)

Section TVIS_MAP.
  Context {E E' S S' : Type} {Spp : PPoset S} {Spp' : PPoset S'}.

  Definition Tvis_map (l : E -> E') (h : S -> S') (t : Tvis E S) : Tvis E' S' :=
    match t with
    | ↺ => ↺
    | -e-> s => -(l e)-> h s
    end.

  Lemma Tvis_map_mon l (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} :
    Monotonic (Tvis_map l h) (pref ++> pref).
  Proof.
    intros t u Htu. inversion Htu as [? | [a s] [a' s'] [Ha Hs]]; subst; cbn.
    - constructor.
    - cbn in Ha. subst a'. constructor. split; [reflexivity | exact (pc_mon (f := h) s s' Hs)].
  Qed.

  Lemma Tvis_map_strict l h : Strict (RA := pref) (RB := pref) (Tvis_map l h).
  Proof. unfold Strict. rewrite !Tvis_ppo_bot_eq. reflexivity. Qed.

  Definition Tvis_map_pc l (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} :
    PreContinuous (RA := pref) (RB := pref) (Tvis_map l h) :=
    {| pc_mon := Tvis_map_mon l h; pc_strict := Tvis_map_strict l h |}.
End TVIS_MAP.

Module TvisF <: Bifunctor SET PPoset PPoset.
  Definition omap (E : Type) (S : PPoset.t) : PPoset.t :=
    PPoset.mkt (Tvis E (PPoset.carrier S)).

  Definition fmap {E1 S1 E2 S2} (l : E1 -> E2) (h : PPoset.m S1 S2) :
    PPoset.m (omap E1 S1) (omap E2 S2) :=
    @PPoset.mkm (omap E1 S1) (omap E2 S2)
      (Tvis_map l (PPoset.apply _ _ h)) (Tvis_map_pc l (PPoset.apply _ _ h)).

  Proposition fmap_id E S :
    fmap id (PPoset.id S) = PPoset.id (omap E S).
  Proof. apply PPoset.meq. intros [| [e s]]; reflexivity. Qed.

  Proposition fmap_compose {E1 S1 E2 S2 E3 S3}
      (l' : E2 -> E3) (h' : PPoset.m S2 S3)
      (l : E1 -> E2) (h : PPoset.m S1 S2) :
    fmap (l ;; l') (PPoset.compose h' h) =
      PPoset.compose (fmap l' h') (fmap l h).
  Proof.
    apply PPoset.meq. intros [| [e s]]; cbn; [reflexivity | reflexivity].
  Qed.

  Include BifunctorTheory SET PPoset PPoset.
End TvisF.

(** ** LTSs with only Visible Events *)
Module VisLTS := LCoalg SET TvisF.
Export (hints, coercions) SilLTS.
Export (hints, coercions) VisLTS.

Local Instance T_dcpo {E S} `{DCPO S} : DCPO (VisLTS.T E S) := Tvis_dcpo.
Global Hint Extern 1 (DCPO (VisLTS.T _ _)) => simple eapply @T_dcpo : typeclass_instances.

Global Instance T_dcomplete {E S} `{DCPO S} : DirectedComplete (R := pref (P := VisLTS.T E S)) :=
  lift_dcomplete.

Global Instance T_finitary {E S} `{DCPO S} `{!Finitary (R := lce (P := S))} :
  Finitary (R := lce (P := VisLTS.T E S)) := Tvis_finitary.

Abbreviation VisLTS := VisLTS.lcoalg.

Program Definition VisLTS_to_SilLTS {E S} {Spp : PPoset S} (α : VisLTS E S) : SilLTS E S :=
  {|
    SilLTS.trans := VisLTS.trans α ;; convex_map tvis_tsil;
    SilLTS.init := VisLTS.init α
  |}.
Next Obligation.
  split.
  - intros s s' Hs. apply (convex_map_mon tvis_tsil (Hf := tvis_tsil_pc)).
    exact (pc_mon (PreContinuous := VisLTS.trans_pc α) s s' Hs).
  - unfold Strict. lazy beta.
    etransitivity; [exact (f_equal (convex_map tvis_tsil) (strict_bot (f := VisLTS.trans α))) |].
    unfold convex_map.
    etransitivity; [exact (em_ext_bot _) |]. lazy beta.
    pose proof (strict_bot (f := tvis_tsil (E := E) (S := S))) as Hs.
    etransitivity; [exact (f_equal {{-}} Hs) |].
    exact em_emb_bot.
Qed.

(** ** Simple Behaviour Objects *)

Definition vis_div {E} : VisLTS E (lift unit eq) :=
  VisLTS.flat_lcoalg (fun s => {{↺}}) (fun _ => True).

(** ** Loud Communicating Objects *)

(** A loud communicating object is one that has no silent transitions.
  This is nicely defined as a communicating object that factors through
  the retraction [tvis_tsil]. *)
Definition loud {E S} {Spp : PPoset S} (α : SilLTS E S) (α_vis : VisLTS E S) :=
  α_vis ;; convex_map tvis_tsil = α /\ VisLTS.init α_vis = SilLTS.init α.

(** And since the map is a retraction it is mono, so factorings are unique. **)
Lemma loud_unique_trans {E S} {Spp : PPoset S} {α : SilLTS E S} {α_vis : VisLTS E S} {α_vis' : VisLTS E S} :
 loud α α_vis -> loud α α_vis' -> α_vis = α_vis' :> (S -> convex_set (Tvis E S)).
Proof.
  intros [H _] [H' _]. apply functional_extensionality. intros s.
  assert (R : forall x : convex_set (Tvis E S), convex_map tsil_tvis (convex_map tvis_tsil x) = x).
  { intros x. apply (fcomp_pt (convex_map tvis_tsil) (convex_map tsil_tvis) id id).
    rewrite <- (convex_map_compose tsil_tvis tvis_tsil (Hg := tsil_tvis_mon)).
    rewrite tvis_tsil_retract, convex_map_id. reflexivity. }
  apply (f_equal (fun h => convex_map tsil_tvis (h s))) in H, H'.
  rewrite <- (R (α_vis s)), <- (R (α_vis' s)).
  etransitivity; [exact H | symmetry; exact H'].
Qed.

Lemma loud_unique {E S} {Spp : PPoset S} {α : SilLTS E S} {α_vis : VisLTS E S} {α_vis' : VisLTS E S} :
  loud α α_vis -> loud α α_vis' -> VisLTS.init α_vis = VisLTS.init α_vis' -> α_vis = α_vis'.
Proof.
  intros H H' Hi. apply VisLTS.lcoalg_ext; [exact (loud_unique_trans H H') | exact Hi].
Qed.

(** [VisLTS_to_SilLTS] is indeed an embedding *)

Lemma VisLTS_to_SilLTS_loud {E S} {Spp : PPoset S} (α : VisLTS E S) :
  loud (VisLTS_to_SilLTS α) α.
Proof.
  split; reflexivity.
Qed.

Lemma VisLTS_to_SilLTS_inj {E S} {Spp : PPoset S} (α β : VisLTS E S) :
  VisLTS_to_SilLTS α = VisLTS_to_SilLTS β -> α = β.
Proof.
  intros H.
  assert (Lβ : loud (VisLTS_to_SilLTS α) β) by (rewrite H; split; reflexivity).
  apply (loud_unique (VisLTS_to_SilLTS_loud α) Lβ). exact (f_equal SilLTS.init H).
Qed.

(** ** Visible Steps *)

Section VIS_STEP.
  Context {E S : Type} {Spp : PPoset S}.

  Definition vis_step (α : S -> convex_set (Tsil E S)) (s : S) : Tvis E S -> Prop :=
    fun t =>
      match t with
      | ↺ => diverges α s
      | -e-> t' => exists s_mid, α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t'
      end.

  Lemma vis_step_sil (α : S -> convex_set (Tsil E S)) {s s'} :
    α ⊢ s -ɛ-> s' -> forall t, vis_step α s' t -> vis_step α s t.
  Proof.
    intros Hs [| [e t]] Ht.
    - apply diverges_unfold. right. exists s'. split; assumption.
    - destruct Ht as [s_mid [Hstar Hvis]].
      exists s_mid. split; [exact (sil_star_cons α s s' s_mid Hs Hstar) | exact Hvis].
  Qed.

  Lemma vis_step_hull_mem (α : S -> convex_set (Tsil E S)) (s : S) (e : E) (t : S) :
    chull (vis_step α s) (-e-> t) <->
    (exists s_mid t', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t' /\ pref t t') /\
    (diverges α s \/ (exists s_mid t', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t' /\ pref t' t)).
  Proof.
    split.
    - intros [a [c [Ha [Hc [Hat Htc]]]]].
      inversion Htc as [| ? [e' t'] [He Ht]]; cbn in He, Ht; subst e' c.
      destruct Hc as [s_mid [Hstar Hvis]].
      split; [exists s_mid, t'; split; [exact Hstar | split; [exact Hvis | exact Ht]] |].
      destruct a as [| [e0 t0]]; [left; exact Ha |].
      inversion Hat as [| ? ? [He0 Ht0]]; cbn in He0, Ht0; subst e0.
      destruct Ha as [s_mid0 [Hstar0 Hvis0]].
      right. exists s_mid0, t0. split; [exact Hstar0 | split; [exact Hvis0 | exact Ht0]].
    - intros [[s_mid [t' [Hstar [Hvis Hle]]]] Hlow].
      destruct Hlow as [Hdiv | [s_mid0 [t0 [Hstar0 [Hvis0 Hle0]]]]].
      + exists ↺, (-e-> t'). split; [exact Hdiv |].
        split; [exists s_mid; split; assumption |].
        split; [constructor | constructor; constructor; [reflexivity | exact Hle]].
      + exists (-e-> t0), (-e-> t'). split; [exists s_mid0; split; assumption |].
        split; [exists s_mid; split; assumption |].
        split; constructor; constructor; [reflexivity | exact Hle0 | reflexivity | exact Hle].
  Qed.
End VIS_STEP.

Notation "α ⊢ s = e => t" := (chull (vis_step α s) (-e-> t))
  (at level 70, s at level 35, e at level 35, t at level 35).

(** ** The Loudening Operator *)

(** We now define an operation that acts like Milner saturation, removing silent steps.
  However, unlike the milner star, it does so why computing infinite sequences of
  silent steps into a divergence. *)

(** First, we define a functional operator that filters a visible step.
  On a visible transition, it simply uses the singleton map, while on a silent
  transition it iterates the candidate. *)
Section LOUDEN.
  Context {E S : Type} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}.

  Definition vstep (g : VisLTS E S) : Tsil E S -> convex_set (Tvis E S) :=
    Tsil_copair {{-}} g.

  (** [vstep] is monotonic in both the candidate and the input transition *)
  Lemma vstep_mono_l (g g' : VisLTS E S) :
    lce g g' -> forall t, lce (vstep g t) (vstep g' t).
  Proof.
    intros Hg. apply Tsil_copair_mon_r. exact (proj1 Hg).
  Qed.

  Lemma vstep_mono_r (g : VisLTS E S) :
    Monotonic (vstep g) (lce ++> lce).
  Proof.
    apply Tsil_copair_mon.
    - exact em_emb_mon.
    - exact (pc_mon (PreContinuous := VisLTS.trans_pc g)).
    - rewrite <- Tvis_bot_eq, em_emb_bot, (strict_bot (f := VisLTS.trans g)). reflexivity.
  Qed.

  (** [vstep] is strict *)
  Lemma vstep_bot (g : VisLTS E S) : vstep g bot = div_set.
  Proof.
    unfold vstep. rewrite Tsil_bot_eq. cbn [Tsil_copair]. rewrite <- Tvis_bot_eq. apply em_emb_bot.
  Qed.

  Lemma vstep_div (g : VisLTS E S) (t : Tsil E S) : t = ↺ -> vstep g t = div_set.
  Proof.
    intros ->. rewrite <- Tsil_bot_eq. apply vstep_bot.
  Qed.

  Lemma vstep_strict (g : VisLTS E S) :
    Strict (RB := lce) (POB := lce_po) (PB := dcpo_pointed) (vstep g).
  Proof.
    unfold Strict. rewrite vstep_bot. apply (antisymmetry (R := lce)); [apply div_set_bot | apply bot_lb].
  Qed.

  Definition vstep_pc (g : VisLTS E S) :
    PreContinuous (RB := lce) (POB := lce_po) (PB := dcpo_pointed) (vstep g) :=
    {| pc_mon := vstep_mono_r g; pc_strict := vstep_strict g |}.

  (** The functional operator proper is defined on transitions by:
  [g] ↦ [α ;; em_ext (vstep g)].
  That is, we take a step of the communicating object α,
    then for each transition possible we filter it using [vstep] and continue
    as [g] in case it was a silent one.

  To be able to compute its fixpoint, we show it is pre-continuous.
  *)
  Lemma Φ_louden_trans_pc (α : SilLTS E S) (g : VisLTS E S) :
    PreContinuous (RA := pref) (RB := em_le) (α ;; em_ext (vstep g)).
  Proof.
    split.
    - intros s s' Hs.
      exact (em_ext_mon (vstep g) (Hf := vstep_pc g)
               (α s) (α s') (pc_mon (PreContinuous := SilLTS.trans_pc α) s s' Hs)).
    - unfold Strict. unfold fcomp. rewrite (strict_bot (f := SilLTS.trans α)), em_ext_bot. apply vstep_bot.
  Qed.

  (** The functional proper is defined on coalgebras directly. *)
  Definition Φ_louden (α : SilLTS E S) (g : VisLTS E S) : VisLTS E S :=
    {|
      VisLTS.trans := α ;; em_ext (vstep g);
      VisLTS.init := SilLTS.init α;
      VisLTS.trans_pc := Φ_louden_trans_pc α g;
    |}.

  Lemma Φ_louden_mon (α : SilLTS E S) :
    Monotonic (Φ_louden α) (lce ++> lce).
  Proof.
    intros g g' Hg. split.
    - intros s. unfold Φ_louden. cbn [VisLTS.trans fcomp]. unfold em_ext.
      apply (lsup_mon (H := em_dcposl (P := Tvis E S))).
      intros [p Hp]. apply vstep_mono_l. exact Hg.
    - reflexivity.
  Qed.

  (** [Φ_louden α] is monotonic but not Scott-continuous for arbitrary
    directed families when [S] has infinite silent branching, so the least
    fixpoint is taken by transfinite iteration. *)
  Definition louden (α : SilLTS E S) : VisLTS E S :=
    TFP.lfp (Φ_louden α) (Hf := Φ_louden_mon α).

  Lemma louden_unfold (α : SilLTS E S) :
    louden α = Φ_louden α (louden α).
  Proof.
    symmetry. apply TFP.lfp_fixed.
  Qed.

  (** ** Basic Facts *)

  Lemma louden_init (α : SilLTS E S) :
    VisLTS.init (louden α) = SilLTS.init α.
  Proof.
    rewrite louden_unfold. reflexivity.
  Qed.

  Lemma louden_mem_div {α : SilLTS E S} {s} : 
    louden α ⊢ s -↺-> <-> diverges α s. 
  Proof.
    split.
    - intros Ht. unfold diverges. revert s Ht. coinduction R CH.
      intros s Ht. rewrite louden_unfold in Ht. simpl. simpl in Ht.
      rewrite <- Tvis_bot_eq in Ht. apply chull_bot in Ht.
      destruct Ht as [[t Htrans] Ht]. simpl in Ht.
      destruct t as [| [e s']]; [left; assumption | ].
      right. exists s'. destruct e as [e |].
      + cbn in Ht. exfalso.
        assert (Hc : (- e -> s') = ↺).
          { rewrite <- Ht; exact lift_ppo_bot_eq. }
        discriminate Hc.
      + split; [assumption |]. cbn in Ht. 
        apply CH. rewrite <- Tvis_bot_eq. exact Ht.
    - revert s. unfold louden.
      apply TFP.lfp_ind. intros I x y Hx HD Hy s Hd.
      rewrite <- Tvis_bot_eq. eapply em_issup_bot.
      apply (VisLTS.lcoalg_issup_trans _ HD y Hy s).
      intros i. apply diverges_unfold in Hd. destruct Hd as [Ht | [t [Ht Hd]]].
      + apply chull_extensive. exists (exist _ ↺ Ht). 
        simpl. rewrite <- Tvis_bot_eq. reflexivity.
      + apply chull_extensive. exists (exist _ (-ɛ-> t) Ht). simpl.
        specialize (Hx i t Hd). rewrite <- Tvis_bot_eq in Hx. apply Hx.
  Qed.

  Lemma louden_vis_intro {α : SilLTS E S} {s s_mid s' e} :
    α ⊢ s -ɛ*-> s_mid -> α ⊢ s_mid -'e-> s' -> louden α ⊢ s -e-> s'.
  Proof.
    induction 1 as [s | s s_mid' s_mid Hstep _ IH]; intros Hvis.
    - rewrite louden_unfold. apply chull_extensive.
      exists (exist _ (-'e-> s') Hvis). reflexivity.
    - rewrite louden_unfold. apply chull_extensive.
      exists (exist _ (-ɛ-> s_mid') Hstep). apply IH. assumption.
  Qed.

  Lemma louden_vis_elim {α : SilLTS E S} :
    forall s s' e, louden α ⊢ s -e-> s' ->
      exists s_mid s'', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> s'' /\ lce s' s''.
  Proof.
    unfold louden. apply TFP.lfp_ind. intros I x y Hx HD Hy s s' e Hs.
    assert (Hne : (-e-> s' : Tvis E S) <> bot).
    { rewrite Tvis_bot_eq. discriminate. }
    destruct (VisLTS.lcoalg_issup_trans_mem _ HD y Hy s _ Hs Hne) as [i Hi].
    simpl in Hi. destruct Hi as [a [c [_ [[[p Hp] Hc] [_ Hac]]]]]. simpl in Hc.
    destruct p as [| [o t]]; [| destruct o as [e' |]]; simpl in Hc.
    - subst c. inversion Hac.
    - subst c. inversion Hac as [| ? ? [He Ht]]; cbn in He, Ht; subst e'.
      exists s, t. split; [constructor | split; [exact Hp | exact Ht]].
    - inversion Hac as [| ? [e' t'] [He Ht]]; cbn in He, Ht; subst e' c.
      destruct (Hx i t t' e Hc) as [s_mid [s'' [Hstar [Hvis Hle]]]].
      exists s_mid, s''. split; [econstructor; eassumption | split; [exact Hvis |]].
      transitivity t'; assumption.
  Qed.

  Lemma louden_vis_lower {α : SilLTS E S} {e} :
    forall s t, louden α ⊢ s -e-> t ->
    ~ (exists s_mid t', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t' /\ lce t' t) ->
    diverges α s.
  Proof.
    change (forall s t, louden α ⊢ s -e-> t ->
      ~ (exists s_mid t', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t' /\ lce t' t) ->
      gfp (divergesF α) s).
    coinduction R CH. intros s t Hmem Hno.
    rewrite louden_unfold in Hmem. simpl in Hmem.
    destruct Hmem as [a [c [[[p Hp] Ha] [_ [Hat _]]]]]. simpl in Ha.
    destruct p as [| [o u]]; [| destruct o as [e0 |]]; simpl in Ha.
    - left. exact Hp.
    - subst a. inversion Hat as [| ? ? [He Hu]]; cbn in He, Hu; subst e0.
      exfalso. apply Hno. exists s, u. split; [constructor | split; [exact Hp | exact Hu]].
    - destruct a as [| [e0 t0]].
      + right. exists u. split; [exact Hp |].
        apply (gfp_chain R). exact (proj1 (louden_mem_div (s := u)) Ha).
      + inversion Hat as [| ? ? [He Ht0]]; cbn in He, Ht0; subst e0.
        right. exists u. split; [exact Hp |].
        apply (CH u t0 Ha). intros [s_mid [t' [Hstar [Hvis Hle]]]].
        apply Hno. exists s_mid, t'.
        split; [exact (sil_star_cons α s u s_mid Hp Hstar) | split; [exact Hvis |]].
        transitivity t0; assumption.
  Qed.

  Lemma vis_step_louden {α : SilLTS E S} {s} :
    forall t, vis_step α s t -> louden α s t.
  Proof.
    intros [| [e t]] Ht.
    - apply louden_mem_div. exact Ht.
    - destruct Ht as [s_mid [Hstar Hvis]]. exact (louden_vis_intro Hstar Hvis).
  Qed.

  Lemma louden_trans_eq {α : SilLTS E S} (s : S) :
    louden α s = chull (vis_step α s).
  Proof.
    apply convex_set_ext. intros t. split.
    - intros Ht. destruct t as [| [e t]].
      + apply chull_extensive. apply louden_mem_div. exact Ht.
      + apply vis_step_hull_mem. split; [exact (louden_vis_elim s t e Ht) |].
        destruct (Classical_Prop.classic
                    (exists s_mid t', α ⊢ s -ɛ*-> s_mid /\ α ⊢ s_mid -'e-> t' /\ lce t' t))
          as [Hlow | Hno].
        * right. exact Hlow.
        * left. exact (louden_vis_lower s t Ht Hno).
    - intros [a [c [Ha [Hc [Hat Htc]]]]].
      apply (convexity (louden α s) a t c); [| | exact Hat | exact Htc];
        apply vis_step_louden; assumption.
  Qed.

  Lemma louden_mem_vis {α : SilLTS E S} {s t e} :
    louden α ⊢ s -e-> t <-> α ⊢ s =e=> t.
  Proof.
    split; intros H.
    - rewrite <- louden_trans_eq. exact H.
    - rewrite louden_trans_eq. exact H.
  Qed.

  (** Silencing a loud communicating object does nothing *)

  Lemma vstep_tvis_tsil (g : VisLTS E S) :
    tvis_tsil ;; vstep g = {{-}}.
  Proof.
    apply functional_extensionality. intros [| [e c]]; reflexivity.
  Qed.

  Lemma em_ext_vstep_loud_fn (g : VisLTS E S) :
    convex_map tvis_tsil ;; em_ext (vstep g) = id.
  Proof.
    unfold convex_map.
    rewrite <- (em_monad_assoc (vstep g) (tvis_tsil ;; {{-}}) (Hg := vstep_mono_r g)).
    rewrite fcomp_assoc, <- em_monad_runital, vstep_tvis_tsil. apply em_monad_lunital.
  Qed.

  Lemma em_ext_vstep_loud (g : VisLTS E S) (x : convex_set (Tvis E S)) :
    em_ext (vstep g) (convex_map tvis_tsil x) = x.
  Proof.
    exact (f_equal (fun h => h x) (em_ext_vstep_loud_fn g)).
  Qed.

  Lemma louden_loud (α : SilLTS E S) (α_vis : VisLTS E S) : loud α α_vis -> louden α = α_vis.
  Proof.
    intros [H Hi]. rewrite (louden_unfold α). apply VisLTS.lcoalg_ext.
    - apply functional_extensionality. intros s. unfold Φ_louden. cbn [VisLTS.trans fcomp].
      rewrite <- H. lazy beta. apply em_ext_vstep_loud.
    - symmetry. exact Hi.
  Qed.

  (** A corollary is that [louden] is idempotent *)

  Lemma louden_idem (α : SilLTS E S) : louden (VisLTS_to_SilLTS (louden α)) = louden α.
  Proof.
    apply louden_loud. apply VisLTS_to_SilLTS_loud.
  Qed.
End LOUDEN.

Arguments louden : simpl never.

(** ** Sanity Check: loudening a silent loop yields divergence *)

Lemma louden_sil_loop_div {E} : louden (sil_loop E) = vis_div.
Proof.
  apply antisymmetry.
  - apply TFP.lfp_least_prefixed. split.
    + intros [| []]; unfold Φ_louden, sil_loop, vis_div; cbn [VisLTS.trans fcomp].
      * rewrite !SilLTS.flat_lcoalg_bot, em_ext_bot. erewrite vstep_div; [apply div_set_bot |].
        apply lift_ppo_bot_eq.
      * rewrite !SilLTS.flat_lcoalg_el, em_ext_ana. reflexivity.
    + reflexivity.
  - split.
    + intros [| []]; unfold vis_div.
      * rewrite VisLTS.flat_lcoalg_bot. apply bot_lb.
      * rewrite VisLTS.flat_lcoalg_el, <- Tvis_bot_eq, em_emb_bot. apply div_set_bot.
    + rewrite (louden_unfold (sil_loop E)). reflexivity.
Qed.