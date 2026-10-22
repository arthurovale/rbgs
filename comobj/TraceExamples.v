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
  Local Open Scope set_scope.

  Lemma em_ext_in {Q} (f : P -> set Q) (x : convex_set P) (p : P) (q : Q) :
    p ∈ x -> q ∈ f p -> q ∈ em_ext f x.
  Proof.
    intros Hp Hq. exists (exist _ p Hp). exact Hq.
  Qed.

  Lemma set_ext_em_emb {Q} (f : P -> set Q) (p : P) :
    set_ext f (mem (em_emb p)) = f p.
  Proof.
    apply set_ext_ana.
  Qed.

  Lemma fsup_emb_antichain (Q : P -> Prop) (p : P) :
    (forall x y, Q x -> Q y -> R x y -> x = y) ->
    p ∈ fsup Q em_emb -> Q p.
  Proof.
    intros HQ [x [y [[[x' Hx'] Hx] [[[y' Hy'] Hy] [Hxp Hpy]]]]]. cbn in Hx, Hy. subst.
    assert (x' = y') as <- by (apply HQ; [exact Hx' | exact Hy' | transitivity p; assumption]).
    replace p with x'; [exact Hx' |]. apply antisymmetry; assumption.
  Qed.
End EM_MEMBERSHIP.

Section SET_MEMBERSHIP.
  Local Open Scope set_scope.

  Lemma set_ext_in {P Q} (f : P -> set Q) (x : set P) (p : P) (q : Q) :
    p ∈ x -> q ∈ f p -> q ∈ set_ext f x.
  Proof.
    intros Hp Hq. exists (exist _ p Hp). exact Hq.
  Qed.

  Lemma set_ext_lub {P Q} (f : P -> set Q) (x : set P) (y : set Q) :
    (forall p, p ∈ x -> f p ⊆ y) -> set_ext f x ⊆ y.
  Proof.
    intros Hf q [[p Hp] Hq]. exact (Hf p Hp q Hq).
  Qed.

  Lemma set_fin_lub {P} (l : list P) (y : set P) :
    (forall p, In p l -> p ∈ y) -> set_fin l ⊆ y.
  Proof.
    intros Hl q [[p Hp] Hq]. change (q = p) in Hq. subst q. apply Hl. exact Hp.
  Qed.
End SET_MEMBERSHIP.

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

Local Open Scope set_scope.

Definition tr1 (s : lift S1 eq) : set (Tr ev) :=
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
    unfold Φ_traces, set_kl_compose, set_kl_emb in Hb.
    assert (H2 : x ↑s2 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. rewrite set_ext_ana. reflexivity. }
    assert (H3 : x ↑s3 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. rewrite set_ext_ana. reflexivity. }
    assert (H1 : x ↑s1 ⊆ {{(b ⋅ ↺)%tr, (c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      apply set_ext_lub. intros t Ht. apply fsup_emb_antichain in Ht.
      2:{ intros u v [<- | [<- | []]] [<- | [<- | []]] Huv; try reflexivity;
          inversion Huv; subst;
          match goal with H : (eq * _)%rel _ _ |- _ => destruct H as [He _]; cbn in He; discriminate He end. }
      destruct Ht as [<- | [<- | []]].
      - cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
        destruct Hp as [[t' Ht'] Hp]. change (p = -b-> t') in Hp. subst p.
        apply H2 in Ht'. change (t' = ↺%tr) in Ht'. subst t'.
        apply set_fin_in. left. reflexivity.
      - cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
        destruct Hp as [[t' Ht'] Hp]. change (p = -c-> t') in Hp. subst p.
        apply H3 in Ht'. change (t' = ↺%tr) in Ht'. subst t'.
        apply set_fin_in. right. left. reflexivity. }
    assert (H0 : x ↑s0 ⊆ {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α1. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
      destruct Hp as [[t' Ht'] Hp]. change (p = -a-> t') in Hp. subst p.
      apply H1 in Ht'. destruct Ht' as [[u Hu] Ht']. change (t' = u) in Ht'. subst t'.
      destruct Hu as [<- | [<- | []]]; apply set_fin_in; [left | right; left]; reflexivity. }
    destruct s as [| [| | |]].
    + etransitivity; [apply Hb |]. apply set_ext_lub. intros t Ht.
      change (t = bot) in Ht.
      assert (Hbot : t = ↺) by (rewrite Ht; apply Tvis_bot_eq). rewrite Hbot.
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
  - apply KTFP.gfp_coind. intros s.
    unfold Φ_traces, set_kl_compose, set_kl_emb.
    destruct s as [| [| | |]].
    + apply set_in_iff. apply (set_ext_in _ _ ↺).
      * change (↺ = (bot : Tvis ev (lift S1 eq))). symmetry. apply Tvis_bot_eq.
      * cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + apply set_fin_lub. intros q Hq.
      apply (set_ext_in _ _ (-a-> ↑s1)); [reflexivity |].
      cbn [set_Tvis].
      destruct Hq as [<- | [<- | []]].
      * apply (set_ext_in _ _ (-a-> (b ⋅ ↺)%tr)); [| reflexivity].
        apply (set_ext_in _ _ (b ⋅ ↺)%tr); [| reflexivity]. apply set_fin_in. left. reflexivity.
      * apply (set_ext_in _ _ (-a-> (c ⋅ ↺)%tr)); [| reflexivity].
        apply (set_ext_in _ _ (c ⋅ ↺)%tr); [| reflexivity]. apply set_fin_in. right. left. reflexivity.
    + apply set_fin_lub. intros q Hq.
      destruct Hq as [<- | [<- | []]].
      * apply (set_ext_in _ _ (-b-> ↑s2)); [apply em_fin_in; left; reflexivity |].
        cbn [set_Tvis].
        apply (set_ext_in _ _ (-b-> ↺%tr)); [| reflexivity].
        apply (set_ext_in _ _ ↺%tr); reflexivity.
      * apply (set_ext_in _ _ (-c-> ↑s3)); [apply em_fin_in; right; left; reflexivity |].
        cbn [set_Tvis].
        apply (set_ext_in _ _ (-c-> ↺%tr)); [| reflexivity].
        apply (set_ext_in _ _ ↺%tr); reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ ↺); [reflexivity |].
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ ↺); [reflexivity |].
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
Qed.

Lemma traces_α1 : traces α1 = {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}.
Proof.
  transitivity (em_ext tr1 (VisLTS.init α1)).
  { exact (f_equal (fun f => em_ext f (VisLTS.init α1)) traces_at_α1). }
  apply set_eq. intros t. split.
  - intros [[s Hs] Ht]. cbn in Ht. apply fsup_emb_antichain in Hs.
    + destruct Hs as [y [-> ->]]. exact Ht.
    + intros u v [u' [-> ->]] [v' [-> ->]] _. reflexivity.
  - intros Ht. apply (em_ext_in _ _ ↑s0); [| exact Ht]. apply em_comp_in. exists s0. split; reflexivity.
Qed.

Definition tr2 (s : lift S2 eq) : set (Tr ev) :=
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
    unfold Φ_traces, set_kl_compose, set_kl_emb in Hb.
    assert (H2 : x ↑t2 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. rewrite set_ext_ana. reflexivity. }
    assert (H3 : x ↑t3 ⊆ {{↺%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. rewrite set_ext_ana. reflexivity. }
    assert (H1 : x ↑t1 ⊆ {{(b ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
      destruct Hp as [[t' Ht'] Hp]. change (p = -b-> t') in Hp. subst p.
      apply H2 in Ht'. change (t' = ↺%tr) in Ht'. subst t'. reflexivity. }
    assert (H1' : x ↑t1' ⊆ {{(c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      rewrite set_ext_em_emb. cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
      destruct Hp as [[t' Ht'] Hp]. change (p = -c-> t') in Hp. subst p.
      apply H3 in Ht'. change (t' = ↺%tr) in Ht'. subst t'. reflexivity. }
    assert (H0 : x ↑t0 ⊆ {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}).
    { etransitivity; [apply Hb |]. unfold α2. rewrite VisLTS.flat_lcoalg_el. lazy beta iota.
      apply set_ext_lub. intros t Ht. apply fsup_emb_antichain in Ht.
      2:{ intros u v [<- | [<- | []]] [<- | [<- | []]] Huv; try reflexivity;
          inversion Huv; subst;
          match goal with H : (eq * _)%rel _ _ |- _ => destruct H as [_ Hs]; cbn in Hs; inversion Hs; discriminate end. }
      destruct Ht as [<- | [<- | []]].
      - cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
        destruct Hp as [[t' Ht'] Hp]. change (p = -a-> t') in Hp. subst p.
        apply H1 in Ht'. change (t' = (b ⋅ ↺)%tr) in Ht'. subst t'.
        apply set_fin_in. left. reflexivity.
      - cbn [set_Tvis]. apply set_ext_lub. intros p Hp. apply set_in_iff.
        destruct Hp as [[t' Ht'] Hp]. change (p = -a-> t') in Hp. subst p.
        apply H1' in Ht'. change (t' = (c ⋅ ↺)%tr) in Ht'. subst t'.
        apply set_fin_in. right. left. reflexivity. }
    destruct s as [| [| | | |]].
    + etransitivity; [apply Hb |]. apply set_ext_lub. intros t Ht.
      change (t = bot) in Ht.
      assert (Hbot : t = ↺) by (rewrite Ht; apply Tvis_bot_eq). rewrite Hbot.
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + exact H0.
    + exact H1.
    + exact H1'.
    + exact H2.
    + exact H3.
  - apply KTFP.gfp_coind. intros s.
    unfold Φ_traces, set_kl_compose, set_kl_emb.
    destruct s as [| [| | | |]].
    + apply set_in_iff. apply (set_ext_in _ _ ↺).
      * change (↺ = (bot : Tvis ev (lift S2 eq))). symmetry. apply Tvis_bot_eq.
      * cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + apply set_fin_lub. intros q Hq.
      destruct Hq as [<- | [<- | []]].
      * apply (set_ext_in _ _ (-a-> ↑t1)); [apply em_fin_in; left; reflexivity |].
        cbn [set_Tvis].
        apply (set_ext_in _ _ (-a-> (b ⋅ ↺)%tr)); [| reflexivity].
        apply (set_ext_in _ _ (b ⋅ ↺)%tr); reflexivity.
      * apply (set_ext_in _ _ (-a-> ↑t1')); [apply em_fin_in; right; left; reflexivity |].
        cbn [set_Tvis].
        apply (set_ext_in _ _ (-a-> (c ⋅ ↺)%tr)); [| reflexivity].
        apply (set_ext_in _ _ (c ⋅ ↺)%tr); reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ (-b-> ↑t2)); [reflexivity |].
      cbn [set_Tvis].
      apply (set_ext_in _ _ (-b-> ↺%tr)); [| reflexivity].
      apply (set_ext_in _ _ ↺%tr); reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ (-c-> ↑t3)); [reflexivity |].
      cbn [set_Tvis].
      apply (set_ext_in _ _ (-c-> ↺%tr)); [| reflexivity].
      apply (set_ext_in _ _ ↺%tr); reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ ↺); [reflexivity |].
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
    + apply set_in_iff. apply (set_ext_in _ _ ↺); [reflexivity |].
      cbn [set_Tvis]. rewrite set_ext_ana. reflexivity.
Qed.

Lemma traces_α2 : traces α2 = {{(a ⋅ b ⋅ ↺)%tr, (a ⋅ c ⋅ ↺)%tr}}.
Proof.
  transitivity (em_ext tr2 (VisLTS.init α2)).
  { exact (f_equal (fun f => em_ext f (VisLTS.init α2)) traces_at_α2). }
  apply set_eq. intros t. split.
  - intros [[s Hs] Ht]. cbn in Ht. apply fsup_emb_antichain in Hs.
    + destruct Hs as [y [-> ->]]. exact Ht.
    + intros u v [u' [-> ->]] [v' [-> ->]] _. reflexivity.
  - intros Ht. apply (em_ext_in _ _ ↑t0); [| exact Ht]. apply em_comp_in. exists t0. split; reflexivity.
Qed.

Theorem branching_traces_eq : traces α1 = traces α2.
Proof.
  rewrite traces_α1, traces_α2. reflexivity.
Qed.
