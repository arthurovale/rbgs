Require Import structures.Posets.
Require Import structures.SemiLattices.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Require Import comobj.SilLTS.
Require Import comobj.VisLTS.
Require Import comobj.Traces.

Require Import Stdlib.Lists.List.
Import ListNotations.

Section EM_MEMBERSHIP.
  Context {P : Type} {R : relation P} `{!PartialOrder R}.

  Lemma em_ext_in {Q} {RQ : relation Q} `{!PartialOrder RQ}
      (f : P -> convex_set Q) (x : convex_set P) (p : P) (q : Q) :
    p ∈ x -> q ∈ f p -> q ∈ em_ext f x.
  Proof.
    intros Hp Hq. apply chull_extensive. exists (exist _ p Hp). exact Hq.
  Qed.

  Lemma em_ext_incl_lub {Q} {RQ : relation Q} `{!PartialOrder RQ}
      (f : P -> convex_set Q) (x : convex_set P) (y : convex_set Q) :
    (forall p, p ∈ x -> f p ⊆ y) -> em_ext f x ⊆ y.
  Proof.
    intros Hf q [u [v [[[p Hp] Hu] [[[p' Hp'] Hv] [Huq Hqv]]]]]. cbn in Hu, Hv.
    apply (convexity y u q v); [apply (Hf p Hp) | apply (Hf p' Hp') | |]; assumption.
  Qed.

  Lemma em_ext_incl_mon {Q} {RQ : relation Q} `{!PartialOrder RQ}
      (f : P -> convex_set Q) (x y : convex_set P) :
    x ⊆ y -> em_ext f x ⊆ em_ext f y.
  Proof.
    intros Hxy. apply em_ext_incl_lub. intros p Hp q Hq. exact (em_ext_in f y p q (Hxy p Hp) Hq).
  Qed.

  Lemma em_fin_incl (l : list P) (y : convex_set P) :
    (forall p, In p l -> p ∈ y) -> em_fin l ⊆ y.
  Proof.
    intros Hl q [u [v [[[p Hp] Hu] [[[p' Hp'] Hv] [Huq Hqv]]]]]. cbn in Hu, Hv. subst u v.
    apply (convexity y p q p'); [apply Hl | apply Hl | |]; assumption.
  Qed.

  Lemma fsup_emb_antichain (Q : P -> Prop) (p : P) :
    (forall x y, Q x -> Q y -> R x y -> x = y) ->
    p ∈ fsup Q {{-}} -> Q p.
  Proof.
    intros HQ [x [y [[[x' Hx'] Hx] [[[y' Hy'] Hy] [Hxp Hpy]]]]]. cbn in Hx, Hy. subst.
    assert (x' = y') as <- by (apply HQ; [exact Hx' | exact Hy' | transitivity p; assumption]).
    replace p with x'; [exact Hx' |]. apply antisymmetry; assumption.
  Qed.

  Lemma emb_ext_fin_incl {Q} {RQ : relation Q} `{!PartialOrder RQ} (f : P -> Q)
      (Hf : forall p q, R p q -> RQ (f p) (f q)) (l : list P) :
    em_ext (fun p => {{f p}}) (em_fin l) ⊆ em_fin (map f l).
  Proof.
    intros q [u [v [[[p Hp] Hu] [[[p' Hp'] Hv] [Huq Hqv]]]]]. cbn in Hu, Hv. subst u v.
    destruct Hp as [x [y [[[x' Hx'] Hx] [[[y' Hy'] Hy] [Hxp Hpy]]]]]. cbn in Hx, Hy. subst x y.
    destruct Hp' as [x [y [[[x'' Hx''] Hx] [[[y'' Hy''] Hy] [Hxp' Hpy']]]]]. cbn in Hx, Hy. subst x y.
    exists (f x'), (f y''). split; [| split; [| split]].
    - exists (exist _ (f x') (in_map f l x' Hx')). reflexivity.
    - exists (exist _ (f y'') (in_map f l y'' Hy'')). reflexivity.
    - transitivity (f p); [apply Hf; exact Hxp | exact Huq].
    - transitivity (f p'); [exact Hqv | apply Hf; exact Hpy'].
  Qed.
End EM_MEMBERSHIP.

Inductive ev := a | b | c.

Inductive S1 := s0 | s1 | s2 | s3.

Definition α1 : VisLTS ev (lift S1 eq) :=
  VisLTS.flat_lcoalg
    (fun s =>
       match s with
       | s0 => {{-a-> ↑s1}}
       | s1 => {{-b-> ↑s2, -c-> ↑s3}}
       | s2 | s3 => {{↺}}
       end)
    (fun s => s = s0).

Definition tr1 (s : lift S1 eq) : convex_set (Tr ev) :=
  match s with
  | ↑s0 => {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}
  | ↑s1 => {{(b ⋅ ↺)%tr, (c ⋅ ↺)%tr}}
  | _ => {{↺%tr}}
  end.

Lemma traces_at_α1 : traces_at α1 = tr1.
Proof.
  apply antisymmetry.
  - apply sup_lub. intros [x Hx]. intros s.
    assert (Hb : forall s', x s' ⊆ Φ_traces α1 x s') by exact Hx.
    unfold Φ_traces, em_kl_compose, em_kl_emb in Hb.
    assert (H2 : x ↑s2 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity. }
    assert (H3 : x ↑s3 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity. }
    assert (H1 : x ↑s1 ⊆ {{(b ⋅ ↺)%tr, (c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      apply em_ext_incl_lub. intros t Ht. apply fsup_emb_antichain in Ht.
      2:{ intros u v [<- | [<- | []]] [<- | [<- | []]] Huv; try reflexivity;
          inversion Huv; subst;
          match goal with H : (eq * _)%rel _ _ |- _ => destruct H as [He _]; cbn in He; discriminate He end. }
      destruct Ht as [<- | [<- | []]].
      - unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H2 |].
        unfold convex_map. rewrite !em_ext_ana. apply em_in_iff. apply em_fin_in. left. reflexivity.
      - unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H3 |].
        unfold convex_map. rewrite !em_ext_ana. apply em_in_iff. apply em_fin_in. right. left. reflexivity. }
    assert (H0 : x ↑s0 ⊆ {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H1 |].
      unfold convex_map.
      etransitivity; [apply em_ext_incl_mon; apply emb_ext_fin_incl |].
      { intros p q Hpq. constructor. split; [reflexivity | exact Hpq]. }
      etransitivity; [apply emb_ext_fin_incl |].
      { exact (pc_mon (PreContinuous := Tr_fold_pc)). }
      cbn [map Tr_fold]. reflexivity. }
    destruct s as [| [| | |]].
    + etransitivity; [apply Hb |]. apply em_ext_incl_lub. intros t Ht.
      change (t = bot) in Ht.
      assert (Hbot : t = ↺) by (rewrite Ht; apply Tvis_bot_eq). rewrite Hbot.
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
  - apply KTFP.gfp_coind. intros s.
    unfold Φ_traces, em_kl_compose, em_kl_emb.
    destruct s as [| [| | |]].
    + apply em_in_iff. apply (em_ext_in _ _ ↺).
      * change (↺ = (bot : Tvis ev (lift S1 eq))). symmetry. apply Tvis_bot_eq.
      * unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + apply em_fin_incl. intros q Hq.
      apply (em_ext_in _ _ (-a-> ↑s1)); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      destruct Hq as [<- | [<- | []]].
      * apply (em_ext_in _ _ (-a-> (b ⋅ ↺)%tr)); [| reflexivity].
        apply (em_ext_in _ _ (b ⋅ ↺)%tr); [| reflexivity]. apply em_fin_in. left. reflexivity.
      * apply (em_ext_in _ _ (-a-> (c ⋅ ↺)%tr)); [| reflexivity].
        apply (em_ext_in _ _ (c ⋅ ↺)%tr); [| reflexivity]. apply em_fin_in. right. left. reflexivity.
    + apply em_fin_incl. intros q Hq.
      destruct Hq as [<- | [<- | []]].
      * apply (em_ext_in _ _ (-b-> ↑s2)); [apply em_fin_in; left; reflexivity |].
        unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        apply (em_ext_in _ _ (-b-> ↺%tr)); [| reflexivity].
        apply (em_ext_in _ _ ↺%tr); reflexivity.
      * apply (em_ext_in _ _ (-c-> ↑s3)); [apply em_fin_in; right; left; reflexivity |].
        unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        apply (em_ext_in _ _ (-c-> ↺%tr)); [| reflexivity].
        apply (em_ext_in _ _ ↺%tr); reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ ↺); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ ↺); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
Qed.

Lemma traces_α1 : traces α1 = {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}.
Proof.
  transitivity (em_ext tr1 (VisLTS.init α1)).
  { exact (f_equal (fun f => em_ext f (VisLTS.init α1)) traces_at_α1). }
  apply (antisymmetry (R := DCPOSLs.incl)).
  - apply em_ext_incl_lub. intros t Ht. apply fsup_emb_antichain in Ht.
    + destruct Ht as [y [-> ->]]. reflexivity.
    + intros u v [u' [-> ->]] [v' [-> ->]] _. reflexivity.
  - intros q Hq. apply (em_ext_in _ _ ↑s0); [| exact Hq]. apply em_comp_in. exists s0. split; reflexivity.
Qed.

Inductive S2 := t0 | t1 | t1' | t2 | t3.

Definition α2 : VisLTS ev (lift S2 eq) :=
  VisLTS.flat_lcoalg
    (fun s =>
       match s with
       | t0 => {{-a-> ↑t1, -a-> ↑t1'}}
       | t1 => {{-b-> ↑t2}}
       | t1' => {{-c-> ↑t3}}
       | t2 | t3 => {{↺}}
       end)
    (fun s => s = t0).

Definition tr2 (s : lift S2 eq) : convex_set (Tr ev) :=
  match s with
  | ↑t0 => {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}
  | ↑t1 => {{(b ⋅ ↺)%tr}}
  | ↑t1' => {{(c ⋅ ↺)%tr}}
  | _ => {{↺%tr}}
  end.

Lemma traces_at_α2 : traces_at α2 = tr2.
Proof.
  apply antisymmetry.
  - apply sup_lub. intros [x Hx]. intros s.
    assert (Hb : forall s', x s' ⊆ Φ_traces α2 x s') by exact Hx.
    unfold Φ_traces, em_kl_compose, em_kl_emb in Hb.
    assert (H2 : x ↑t2 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity. }
    assert (H3 : x ↑t3 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity. }
    assert (H1 : x ↑t1 ⊆ {{(b ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H2 |].
      unfold convex_map. rewrite !em_ext_ana. reflexivity. }
    assert (H1' : x ↑t1' ⊆ {{(c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite em_ext_ana. unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H3 |].
      unfold convex_map. rewrite !em_ext_ana. reflexivity. }
    assert (H0 : x ↑t0 ⊆ {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      apply em_ext_incl_lub. intros t Ht. apply fsup_emb_antichain in Ht.
      2:{ intros u v [<- | [<- | []]] [<- | [<- | []]] Huv; try reflexivity;
          inversion Huv; subst;
          match goal with H : (eq * _)%rel _ _ |- _ => destruct H as [_ Hs]; cbn in Hs; inversion Hs; discriminate end. }
      destruct Ht as [<- | [<- | []]].
      - unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H1 |].
        unfold convex_map. rewrite !em_ext_ana. apply em_in_iff. apply em_fin_in. left. reflexivity.
      - unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        etransitivity; [apply em_ext_incl_mon; unfold convex_map; apply em_ext_incl_mon; exact H1' |].
        unfold convex_map. rewrite !em_ext_ana. apply em_in_iff. apply em_fin_in. right. left. reflexivity. }
    destruct s as [| [| | | |]].
    + etransitivity; [apply Hb |]. apply em_ext_incl_lub. intros t Ht.
      change (t = bot) in Ht.
      assert (Hbot : t = ↺) by (rewrite Ht; apply Tvis_bot_eq). rewrite Hbot.
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + exact H0.
    + exact H1.
    + exact H1'.
    + exact H2.
    + exact H3.
  - apply KTFP.gfp_coind. intros s.
    unfold Φ_traces, em_kl_compose, em_kl_emb.
    destruct s as [| [| | | |]].
    + apply em_in_iff. apply (em_ext_in _ _ ↺).
      * change (↺ = (bot : Tvis ev (lift S2 eq))). symmetry. apply Tvis_bot_eq.
      * unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + apply em_fin_incl. intros q Hq.
      destruct Hq as [<- | [<- | []]].
      * apply (em_ext_in _ _ (-a-> ↑t1)); [apply em_fin_in; left; reflexivity |].
        unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        apply (em_ext_in _ _ (-a-> (b ⋅ ↺)%tr)); [| reflexivity].
        apply (em_ext_in _ _ (b ⋅ ↺)%tr); reflexivity.
      * apply (em_ext_in _ _ (-a-> ↑t1')); [apply em_fin_in; right; left; reflexivity |].
        unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
        apply (em_ext_in _ _ (-a-> (c ⋅ ↺)%tr)); [| reflexivity].
        apply (em_ext_in _ _ (c ⋅ ↺)%tr); reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ (-b-> ↑t2)); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      apply (em_ext_in _ _ (-b-> ↺%tr)); [| reflexivity].
      apply (em_ext_in _ _ ↺%tr); reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ (-c-> ↑t3)); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis].
      apply (em_ext_in _ _ (-c-> ↺%tr)); [| reflexivity].
      apply (em_ext_in _ _ ↺%tr); reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ ↺); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
    + apply em_in_iff. apply (em_ext_in _ _ ↺); [reflexivity |].
      unfold convex_Tvis. cbn [Tvis_map λ_Tvis]. rewrite em_ext_ana. reflexivity.
Qed.

Lemma traces_α2 : traces α2 = {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}.
Proof.
  transitivity (em_ext tr2 (VisLTS.init α2)).
  { exact (f_equal (fun f => em_ext f (VisLTS.init α2)) traces_at_α2). }
  apply (antisymmetry (R := DCPOSLs.incl)).
  - apply em_ext_incl_lub. intros t Ht. apply fsup_emb_antichain in Ht.
    + destruct Ht as [y [-> ->]]. reflexivity.
    + intros u v [u' [-> ->]] [v' [-> ->]] _. reflexivity.
  - intros q Hq. apply (em_ext_in _ _ ↑t0); [| exact Hq]. apply em_comp_in. exists t0. split; reflexivity.
Qed.

Theorem branching_traces_eq : traces α1 = traces α2.
Proof.
  rewrite traces_α1, traces_α2. reflexivity.
Qed.
