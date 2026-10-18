Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import Stdlib.Logic.FunctionalExtensionality.

Require Import comobj.SilentEvents.
Import SilentEvents.

Require Import comobj.LCoalg.
Require Import comobj.ComObj.


(** * The Silencing Operator *)

Open Scope tsil_scope.

Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
Local Abbreviation id := (fun x => x).

(** ** Behaviour Objects *)

(** A behaviour object differs from a communicating object in that it has no 
  silent transitions *)
Definition Tvis (E S : Type) {Sdcpo : DCPO S} : Type := lift (E * S) (eq * lce)%rel.
#[global] Typeclasses Opaque Tvis.

Section TVIS.
  Context {E S : Type} {Sdcpo : DCPO S}.

  Local Instance Tvis_dcpo : DCPO (Tvis E S) := lift_dcpo.

  Lemma Tvis_bot : (bot : Tvis E S) = ↺.
  Proof. apply lift_bot_eq. Qed.

  Global Instance Tvis_finitary `{!Finitary (R := lce (P := S))} :
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
  Lemma Tsil_copair_mon_r {X} `{DCPO X} (fl : Tvis E S -> X) (fr fr' : S -> X) :
    (forall c, lce (fr c) (fr' c)) ->
    forall t, lce (Tsil_copair fl fr t) (Tsil_copair fl fr' t).
  Proof.
    intros Hfr [| [[e |] c]]; [reflexivity | reflexivity | apply Hfr].
  Qed.

  Lemma Tsil_copair_mon {X} `{DCPO X} (fl : Tvis E S -> X) (fr : S -> X)
      (Hl : Monotonic fl (lce ++> lce)) (Hr : Monotonic fr (lce ++> lce))
      (Hglue : lce (fl ↺) (fr bot)) :
    Monotonic (Tsil_copair fl fr) (lce ++> lce).
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

  Global Instance Tsil_copair_strict {X} `{DCPO X} (fl : Tvis E S -> X) (fr : S -> X)
      `{!Strict fl} :
    Strict (Tsil_copair fl fr).
  Proof.
    unfold Strict. rewrite Tsil_bot. change (fl ↺ = bot).
    rewrite <- Tvis_bot. apply strict_bot.
  Qed.

  Lemma Tsil_copair_sc {X} `{DCPO X} `{!Finitary (R := lce (P := S))}
      (fl : Tvis E S -> X) (fr : S -> X)
      (Hl : Monotonic fl (lce ++> lce)) (Hr : Monotonic fr (lce ++> lce))
      (Hglue : lce (fl ↺) (fr bot)) `{!Strict fl} :
    ScottContinuous true (Tsil_copair fl fr).
  Proof.
    apply finitary_sc. apply Tsil_copair_mon; assumption. typeclasses eauto.
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

  Lemma tvis_tsil_proj (t : Tsil E S) : lce ((tsil_tvis ;; tvis_tsil) t) t.
  Proof.
    destruct t as [| [[e |] s]]; cbn.
    - constructor.
    - constructor. split; reflexivity.
    - constructor.
  Qed.

  (** Both maps of the embedding-projection pair are strict Scott-continuous *)

  Lemma tvis_tsil_mon : Monotonic tvis_tsil (lce ++> lce).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [e c], y as [e' c']; destruct H0 as [He Hc]; cbn in *; subst.
    constructor. split; [reflexivity | exact Hc].
  Qed.

  Lemma tsil_tvis_mon : Monotonic tsil_tvis (lce ++> lce).
  Proof.
    intros t u H. inversion H; subst; cbn; [constructor |].
    destruct x as [[e |] c], y as [[e' |] c']; destruct H0 as [He Hc]; cbn in *;
      try discriminate He; try constructor.
    injection He as <-. split; [reflexivity | exact Hc].
  Qed.

  Global Instance tvis_tsil_strict : Strict tvis_tsil.
  Proof.
    unfold Strict. rewrite Tvis_bot, Tsil_bot. reflexivity.
  Qed.

  Global Instance tsil_tvis_strict : Strict tsil_tvis.
  Proof.
    unfold Strict. rewrite Tsil_bot, Tvis_bot. reflexivity.
  Qed.

  Global Instance tvis_tsil_sc `{!Finitary (R := lce (P := S))} : ScottContinuous true tvis_tsil :=
    finitary_sc tvis_tsil tvis_tsil_mon.

  Global Instance tsil_tvis_sc `{!Finitary (R := lce (P := S))} : ScottContinuous true tsil_tvis :=
    finitary_sc tsil_tvis tsil_tvis_mon.
End TVIS.

Global Hint Extern 1 (DCPO (Tvis _ _)) => simple eapply @Tvis_dcpo : typeclass_instances.

(** A behaviour object is then a labelled coalgebra with visible transitions *)

Abbreviation behobj := (lcoalg Tvis).

Program Definition behobj_to_silobj {E S} {Sdcpo : DCPO S} (α : behobj E S) : comobj E S := 
  {|
    trans := trans α ;; convex_map tvis_tsil;
    init := init α
  |}.
Next Obligation.
  intros s s' Hs. apply (convex_map_mon tvis_tsil (Hf := tvis_tsil_mon)). exact (trans_mon α s s' Hs).
Qed.
Next Obligation.
  unfold Strict. lazy beta.
  etransitivity; [exact (f_equal (convex_map tvis_tsil) (strict_bot (f := trans α))) |].
  unfold convex_map.
  etransitivity; [exact (em_ext_bot _) |]. lazy beta.
  etransitivity; [exact (f_equal {{-}} (strict_bot (f := tvis_tsil))) |].
  exact em_emb_bot.
Qed.

(** ** Simple Behaviour Objects *)

Definition beh_div {E} : behobj E (lift unit eq) := 
  flat_lcoalg Tvis (fun s => {{↺}}) (fun _ => True).

(** ** Loud Communicating Objects *)

(** A loud communicating object is one that has no silent transitions. 
  This is nicely defined as a communicating object that factors through 
  the retraction [tvis_tsil]. *)
Definition loud {E S} `{Sdcpo : DCPO S} (α : comobj E S) (α_vis : behobj E S) :=
  α_vis ;; convex_map tvis_tsil = α /\ init α_vis = init α.

(** And since the map is a retraction it is mono, so factorings are unique. **)
Lemma loud_unique_trans {E S} `{Sdcpo : DCPO S} {α : comobj E S} {α_vis : behobj E S} {α_vis' : behobj E S} :
 loud α α_vis -> loud α α_vis' -> α_vis = α_vis' :> (S -> convex_set (Tvis E S)).
Proof.
  intros [H _] [H' _]. apply functional_extensionality. intros s.
  assert (R : forall x : convex_set (Tvis E S), convex_map tsil_tvis (convex_map tvis_tsil x) = x).
  { intros x. change ((convex_map tvis_tsil ;; convex_map tsil_tvis) x = x).
    rewrite <- (convex_map_compose tsil_tvis tvis_tsil (Hg := tsil_tvis_mon)).
    rewrite tvis_tsil_retract, convex_map_id. reflexivity. }
  apply (f_equal (fun h => convex_map tsil_tvis (h s))) in H, H'. 
  rewrite <- (R (α_vis s)), <- (R (α_vis' s)).
  etransitivity; [exact H | symmetry; exact H'].
Qed.

Lemma loud_unique {E S} `{Sdcpo : DCPO S} {α : comobj E S} {α_vis : behobj E S} {α_vis' : behobj E S} :
  loud α α_vis -> loud α α_vis' -> init α_vis = init α_vis' -> α_vis = α_vis'.
Proof.
  intros H H' Hi. apply lcoalg_ext; [exact (loud_unique_trans H H') | exact Hi].
Qed.

(** [behobj_to_silobj] is indeed an embedding *)

Lemma behobj_to_silobj_loud {E S} {Sdcpo : DCPO S} (α : behobj E S) :
  loud (behobj_to_silobj α) α.
Proof.
  split; reflexivity.
Qed.

Lemma behobj_to_silobj_inj {E S} {Sdcpo : DCPO S} (α β : behobj E S) :
  behobj_to_silobj α = behobj_to_silobj β -> α = β.
Proof.
  intros H.
  assert (Lβ : loud (behobj_to_silobj α) β) by (rewrite H; split; reflexivity).
  apply (loud_unique (behobj_to_silobj_loud α) Lβ). exact (f_equal init H).
Qed.

(** ** The Silencing Operator *)

(** We now define an operation that acts like Milner saturation, removing silent steps.
  However, unlike the milner star, it does so why computing infinite sequences of 
  silent steps into a divergence. *)

(** First, we define a functional operator that filters a visible step. 
  On a visible transition, it simply uses the singleton map, while on a silent 
  transition it iterates the candidate. *)
Definition vstep {E S} `{Sdcpo : DCPO S} (g : behobj E S) : Tsil E S -> convex_set (Tvis E S) :=
  Tsil_copair {{-}} g.

(** [vstep] is monotonic in both the candidate and the input transition *)
Lemma vstep_mono_l {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (g g' : behobj E S) :
  lce g g' -> forall t, lce (vstep g t) (vstep g' t).
Proof.
  intros Hg. apply Tsil_copair_mon_r. exact (proj1 Hg).
Qed.

Lemma vstep_mono_r {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (g : behobj E S) :
  Monotonic (vstep g) (lce ++> lce).
Proof.
  apply Tsil_copair_mon.
  - exact em_emb_mon.
  - exact (trans_mon g).
  - rewrite <- Tvis_bot, em_emb_bot, (strict_bot (f := trans g)). reflexivity.
Qed.

(** [vstep] is strict *)
Lemma vstep_bot {E S} `{Sdcpo : DCPO S} (g : behobj E S) : vstep g bot = div_set.
Proof.
  unfold vstep. rewrite Tsil_bot. cbn [Tsil_copair]. rewrite <- Tvis_bot. apply em_emb_bot.
Qed.

Lemma vstep_strict {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (g : behobj E S) :
  Strict (RB := lce) (POB := lce_po) (PB := dcpo_pointed) (vstep g).
Proof.
  unfold Strict. rewrite vstep_bot. apply (antisymmetry (R := lce)); [apply div_set_bot | apply bot_lb].
Qed.

(** The functional operator proper is defined on transitions by: 
[g] ↦ [α ;; em_ext (vstep g)].
That is, we take a step of the communicating object α, 
  then for each transition possible we filter it using [vstep] and continue 
  as [g] in case it was a silent one.

To be able to compute its fixpoint, we show it is pre-continuous.
*)
Lemma Φ_silence_trans_mon {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}
    (α : comobj E S) (g : behobj E S) :
  Monotonic (α ;; em_ext (vstep g)) (lce ++> em_le).
Proof.
  intros s s' Hs.
  exact (em_ext_mon (vstep g) (Hf := vstep_mono_r g) (Hf_strict := vstep_strict g)
           (α s) (α s') (trans_mon α s s' Hs)).
Qed.

Lemma Φ_silence_trans_strict {E S} `{Sdcpo : DCPO S} (α : comobj E S) (g : behobj E S) :
  Strict (RB := em_le) (α ;; em_ext (vstep g)).
Proof.
  unfold Strict. rewrite (strict_bot (f := trans α)), em_ext_bot. apply vstep_bot.
Qed.

(** The functional proper is defined on coalgebras directly. *)
Definition Φ_silence {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}
    (α : comobj E S) (g : behobj E S) : behobj E S :=
  {|
    trans := α ;; em_ext (vstep g);
    init := init α;
    trans_mon := Φ_silence_trans_mon α g;
    trans_strict := Φ_silence_trans_strict α g;
  |}.

Lemma Φ_silence_mon {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (α : comobj E S) :
  Monotonic (Φ_silence α) (lce ++> lce).
Proof.
  intros g g' Hg. split.
  - intros s. unfold Φ_silence. cbn [trans]. unfold em_ext.
    apply (lsup_mon (H := em_dcposl (P := Tvis E S))).
    intros [p Hp]. apply vstep_mono_l. exact Hg.
  - reflexivity.
Qed.

(** [Φ_silence α] is monotonic but not Scott-continuous for arbitrary
  directed families when [S] has infinite silent branching, so the least
  fixpoint is taken by transfinite iteration. *)
Definition silence {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (α : comobj E S) : behobj E S :=
  TFP.lfp (Φ_silence α) (Hf := Φ_silence_mon α).

Lemma μ_silence_fixed {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (α : comobj E S) :
  Φ_silence α (silence α) = silence α.
Proof.
  apply TFP.lfp_fixed.
Qed.

(** ** Basic Facts *)

Lemma silence_init {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))} (α : comobj E S) : 
  init (silence α) = init α.
Proof. 
  rewrite <- μ_silence_fixed. reflexivity.
Qed.

(** ** Sanity Check: silencing a silent loop yields divergence *)

Lemma silence_sil_loop_div {E} : silence (sil_loop E) = beh_div.
Proof.
  apply antisymmetry.
  - apply TFP.lfp_least_prefixed. split.
    + intros [| []]; unfold Φ_silence, sil_loop, beh_div; cbn [trans].
      * rewrite !flat_lcoalg_bot, em_ext_bot, vstep_bot. apply div_set_bot.
      * rewrite !flat_lcoalg_el, em_ext_ana. reflexivity.
    + reflexivity.
  - split.
    + intros [| []]; unfold beh_div.
      * rewrite flat_lcoalg_bot. apply bot_lb.
      * rewrite flat_lcoalg_el, <- Tvis_bot, em_emb_bot. apply div_set_bot.
    + rewrite <- (μ_silence_fixed (sil_loop E)). reflexivity.
Qed.

(** Silencing a loud communicating object does nothing *)

Lemma vstep_tvis_tsil {E S} `{Sdcpo : DCPO S} (g : behobj E S) :
  tvis_tsil ;; vstep g = {{-}}.
Proof.
  apply functional_extensionality. intros [| [e c]]; reflexivity.
Qed.

Lemma em_ext_vstep_loud {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}
    (g : behobj E S) (x : convex_set (Tvis E S)) :
  em_ext (vstep g) (convex_map tvis_tsil x) = x.
Proof.
  unfold convex_map.
  etransitivity;
    [exact (eq_sym (f_equal (fun h => h x)
              (em_monad_assoc (vstep g) (tvis_tsil ;; {{-}}) (Hg := vstep_mono_r g)))) |].
  etransitivity; [| exact (f_equal (fun h => h x) em_monad_lunital)].
  apply (f_equal (fun h => em_ext h x)).
  apply functional_extensionality. intros t. lazy beta. rewrite em_ext_ana.
  destruct t as [| [e c]]; reflexivity.
Qed.

Lemma cant_silence_loud {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}
    (α : comobj E S) (α_vis : behobj E S) : loud α α_vis -> silence α = α_vis.
Proof.
  intros [H Hi]. rewrite <- (μ_silence_fixed α). apply lcoalg_ext.
  - apply functional_extensionality. intros s. unfold Φ_silence. cbn [trans].
    rewrite <- H. lazy beta. apply em_ext_vstep_loud.
  - symmetry. exact Hi.
Qed.

(** A corollary is that [silence] is idempotent *)

Lemma silence_idem {E S} `{Sdcpo : DCPO S} `{!Finitary (R := lce (P := S))}
    (α : comobj E S) : silence (behobj_to_silobj (silence α)) = silence α.
Proof.
  apply cant_silence_loud. apply behobj_to_silobj_loud.
Qed.