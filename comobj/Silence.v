Definition Tvis (E S : Type) : Type := lift (E * lift S eq) (eq * lce)%rel.
#[global] Typeclasses Opaque Tvis.

Section TVIS.
  Context {E S : Type}.

  Global Instance Tvis_dcpo : DCPO (Tvis E S) := lift_dcpo.

  Lemma Tvis_bot : (bot : Tvis E S) = ⊥.
  Proof. apply lift_bot_eq. Qed.

  Global Instance Tvis_finitary : Finitary (R := lce (P := Tvis E S)).
  Proof.
    intros d. destruct d as [| [e [| s]]].
    - exists [⊥]. intros x. split.
      + intros H. inversion H; subst. left. reflexivity.
      + intros [<- | []]. constructor.
    - exists [⊥; - e -> ↺]. intros x. split.
      + intros H. inversion H; subst; [left; reflexivity |].
        destruct x0 as [e' t']. destruct H2 as [He Ht]. cbn in He, Ht. subst e'.
        change (lift_lce t' lift_bot) in Ht. inversion Ht; subst.
        right. left. reflexivity.
      + intros [<- | [<- | []]]; constructor. split; [reflexivity | constructor].
    - exists [⊥; - e -> ↺; - e -> ↑s]. intros x. split.
      + intros H. inversion H; subst; [left; reflexivity |].
        destruct x0 as [e' t']. destruct H2 as [He Ht]. cbn in He, Ht. subst e'.
        change (lift_lce t' (lift_el s)) in Ht. inversion Ht; subst.
        * right. left. reflexivity.
        * right. right. left. reflexivity.
      + intros [<- | [<- | [<- | []]]]; constructor; split; try reflexivity; constructor.
  Qed.

  Definition vis_sil_copair {X} (fl : Tvis E S -> X) (fr : lift S eq -> X) : (Tsil E S -> X) :=
    fun t => 
      match t with 
      | ⊥ => fl ⊥
      | -'e-> s => fl (-e-> s)
      | -ɛ-> s => fr s
      end.

  (** The copairing is monotone in its silent branch, pointwise. *)
  Lemma vis_sil_copair_mon_r {X} `{DCPO X} (fl : Tvis E S -> X) (fr fr' : lift S eq -> X) :
    (forall c, lce (fr c) (fr' c)) ->
    forall t, lce (vis_sil_copair fl fr t) (vis_sil_copair fl fr' t).
  Proof.
    intros Hfr [| [[e |] c]]; [reflexivity | reflexivity | apply Hfr].
  Qed.

  Lemma vis_sil_copair_mon {X} `{DCPO X} (fl : Tvis E S -> X) (fr : lift S eq -> X)
      (Hl : Monotonic fl (lce ++> lce)) (Hr : Monotonic fr (lce ++> lce))
      (Hglue : lce (fl ⊥) (fr ↺)) :
    Monotonic (vis_sil_copair fl fr) (lce ++> lce).
  Proof.
    intros t u Htu. inversion Htu as [? | x y Hxy]; subst.
    - destruct u as [| [[e |] c]]; cbn.
      + reflexivity.
      + apply Hl. constructor.
      + transitivity (fr ↺); [exact Hglue |]. apply Hr. constructor.
    - destruct x as [[e |] c], y as [[e' |] c']; destruct Hxy as [He Hc]; cbn in *;
        try discriminate He.
      + injection He as <-. apply Hl. constructor. split; [reflexivity | exact Hc].
      + apply Hr. exact Hc.
  Qed.

  Global Instance vis_sil_copair_strict {X} `{DCPO X} (fl : Tvis E S -> X) (fr : lift S eq -> X)
      `{!Strict fl} :
    Strict (vis_sil_copair fl fr).
  Proof.
    unfold Strict. rewrite Tsil_bot. change (fl ⊥ = bot).
    rewrite <- Tvis_bot. apply strict_bot.
  Qed.

  Lemma vis_sil_copair_sc {X} `{DCPO X} (fl : Tvis E S -> X) (fr : lift S eq -> X)
      (Hl : Monotonic fl (lce ++> lce)) (Hr : Monotonic fr (lce ++> lce))
      (Hglue : lce (fl ⊥) (fr ↺)) `{!Strict fl} :
    ScottContinuous true (vis_sil_copair fl fr).
  Proof.
    apply finitary_sc. apply vis_sil_copair_mon; assumption.
  Qed.

  (** [Tvis] sits inside [Tsil] as the visible transitions. *)
  Definition tvis_tsil (t : Tvis E S) : Tsil E S :=
    match t with
    | ⊥ => ⊥
    | -e-> c => -'e-> c
    end.

  (** the injection [tvis_tsil] has a retract forming and embedding-projection pair *)
  Definition tsil_tvis : Tsil E S -> Tvis E S :=
    vis_sil_copair (fun x => x) (fun x => ⊥).

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

  (** Both maps of the embedding-projection pair are strict Scott-continuous:
    they are monotonic and strict, and both domains are finitary. *)

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

  Global Instance tvis_tsil_sc : ScottContinuous true tvis_tsil :=
    finitary_sc tvis_tsil tvis_tsil_mon.

  Global Instance tsil_tvis_sc : ScottContinuous true tsil_tvis :=
    finitary_sc tsil_tvis tsil_tvis_mon.
End TVIS.

  Definition behobj E S := S -> convex_set (Tvis E S).

  Definition beh_div {E} : behobj E unit := fun s => {{⊥}}.

  Global Instance behobj_dcpo {E S} : DCPO (behobj E S) := _ : DCPO (S -> convex_set (Tvis E S)).

  Definition loud {E S} (α : comobj E S) :=
    exists (α_vis : behobj E S), α_vis ;; convex_map tvis_tsil = α.

  Lemma loud_unique {E S} {α : comobj E S} {α_vis : behobj E S} {α_vis' : behobj E S} : 
    α_vis ;; convex_map tvis_tsil = α -> α_vis' ;; convex_map tvis_tsil = α
      -> α_vis = α_vis'.
  Proof.
    intros H H'.  apply (f_equal (fun x => x ;; convex_map tsil_tvis)) in H, H'.
    change (α_vis ;; (convex_map tvis_tsil ;; convex_map tsil_tvis) = α ;; convex_map tsil_tvis) in H.
    change (α_vis' ;; (convex_map tvis_tsil ;; convex_map tsil_tvis) = α ;; convex_map tsil_tvis) in H'.
    rewrite <- (convex_map_compose tsil_tvis tvis_tsil (Hg := tsil_tvis_mon)) in H, H'.
    rewrite tvis_tsil_retract, convex_map_id in H, H'.
    change (α_vis = α ;; convex_map tsil_tvis) in H.
    change (α_vis' = α ;; convex_map tsil_tvis) in H'.
    rewrite H, H'. reflexivity.
  Qed.

  Definition vstep {E S} (g : behobj E S) : Tsil E S -> convex_set (Tvis E S) := 
    vis_sil_copair em_emb (lift_ext g).

  Lemma vstep_mon {E S} (g g' : behobj E S) :
    lce g g' -> forall t, lce (vstep g t) (vstep g' t).
  Proof.
    intros Hg. apply vis_sil_copair_mon_r, lift_ext_mon_r, Hg.
  Qed.

  Definition Φ_silence {E S} (α : comobj E S) (g : behobj E S) : behobj E S :=
    α ;; em_ext (vstep g).

  Lemma Φ_silence_mon {E S} (α : comobj E S) : Monotonic (Φ_silence α) (lce ++> lce).
  Proof.
    intros g g' Hg s. unfold Φ_silence, em_ext.
    apply (lsup_mon (H := em_dcposl (P := Tvis E S))).
    intros [p Hp]. apply vstep_mon. exact Hg.
  Qed.

  (** [Φ_silence α] is monotonic but not Scott-continuous for arbitrary
    directed families when [S] has infinite silent branching, so the least
    fixpoint is taken by transfinite iteration. *)
  Definition silence {E S} (α : comobj E S) : behobj E S :=
    TFP.lfp (Φ_silence α) (Hf := Φ_silence_mon α).

  Lemma μ_silence_fixed {E S} (α : comobj E S) : Φ_silence α (silence α) = silence α.
  Proof.
    apply TFP.lfp_fixed.
  Qed.

  Lemma silence_sil_loop_div {E} : silence (E := E) sil_loop = beh_div.
  Proof.
    apply antisymmetry.
    - apply TFP.lfp_least_prefixed. intros []. simpl.
      unfold Φ_silence, sil_loop. rewrite em_ext_ana.
      reflexivity.
    - intros []. unfold beh_div. rewrite <- lift_bot_eq, em_emb_bot. apply div_set_bot.
  Qed.