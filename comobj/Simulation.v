From Coinduction Require Import all.
Import CoindNotations.

Require Import coqrel.LogicalRelations.

Require Import comobj.SilLTS.
Import SilLTS.

Require Import comobj.VisLTS.
Require Import comobj.Traces.
Require Import comobj.Refinement.

Local Open Scope em_scope.

Section SIMF.
  Context {E : Type} {Sα Sβ : Type} {Sα_po : PPoset Sα} {Sβ_po : PPoset Sβ}
    (α : Sα -> convex_set (Tsil E Sα)) (β : Sβ -> convex_set (Tsil E Sβ)).

  Section NoElim.
    #[local] Unset Elimination Schemes.
    Inductive divpresInd (Rdiv : rel Sα Sβ) : rel Sα Sβ :=
    | dpi sα sβ : (forall sα', α ⊢ sα -ɛ-> sα' ->
        (exists sβ', β ⊢ sβ -ɛ-> sβ' /\ Rdiv sα' sβ') \/ divpresInd Rdiv sα' sβ)
        -> (α ⊢ sα -↺-> -> (exists sβ', β ⊢ sβ -ɛ-> sβ' /\ Rdiv sα sβ') \/ β ⊢ sβ -↺->) ->
        divpresInd Rdiv sα sβ.
  End NoElim.

  Lemma divpresInd_ind Rdiv (P : rel Sα Sβ) :
    (forall sα sβ,
      (forall sα', α ⊢ sα -ɛ-> sα' ->
        (exists sβ', β ⊢ sβ -ɛ-> sβ' /\ Rdiv sα' sβ') \/ (divpresInd Rdiv sα' sβ /\ P sα' sβ)) ->
      (α ⊢ sα -↺-> -> (exists sβ', β ⊢ sβ -ɛ-> sβ' /\ Rdiv sα sβ') \/ β ⊢ sβ -↺->) ->
      P sα sβ) ->
    forall sα sβ, divpresInd Rdiv sα sβ -> P sα sβ.
  Proof.
    intros H. fix F 3. intros ? ? [sα sβ Hs Hd]. apply H; [| exact Hd]. intros sα' Hstep.
    destruct (Hs sα' Hstep) as [Hm | Hm]; [left; exact Hm | right; split; [exact Hm | exact (F _ _ Hm)]].
  Qed.
  Register Scheme divpresInd_ind as ind_nodep for divpresInd.

  Program Definition divpresF : mon (rel Sα Sβ) :=
  {| body Rdiv sα sβ := divpresInd Rdiv sα sβ |}.
  Next Obligation.
    intros Rdiv Rdiv' HR sα sβ H. induction H. constructor. 
    - intros sα' Htrans. destruct (H sα' Htrans) as [[sβ' [Hb Hr]] | [_ IH]].
      + left. exists sβ'. split; [assumption | apply HR; assumption].
      + right; assumption.
    - intros Htrans. destruct (H0 Htrans) as [[sβ' [Htβ HRdiv]] | H1].
      + left. exists sβ'. split. assumption. apply HR. assumption.
      + right; assumption.
  Qed.

  Local Notation "R ←" := (R true) (at level 1).
  Local Notation "R →" := (R false) (at level 1).

  Variant simF_ (R : bool -> rel Sα Sβ) : bool -> rel Sα Sβ :=
  | simF_game sα sβ :
    ((forall e sα', α ⊢ sα -'e-> sα' -> 
      (* Chappe uses R←^+ in the visible branch instead *)
       exists sβ', exists sβ_mid,
        β ⊢ sβ -ɛ*-> sβ_mid /\ β ⊢ sβ_mid -'e-> sβ' /\ R← sα' sβ')
        /\ 
        (forall sα', α ⊢ sα -ɛ-> sα' -> 
          ((exists sβ', β ⊢ sβ -ɛ+-> sβ' /\ R← sα' sβ') 
          \/ 
          (R← sα' sβ /\ R→ sα' sβ)))
        /\
        (α ⊢ sα -↺-> -> (R← sα sβ /\ R→ sα sβ))) -> simF_ R true sα sβ
  | simF_divpres sα sβ : divpresF R→ sα sβ -> simF_ R false sα sβ
  .

  Program Definition simF : mon (bool -> rel Sα Sβ) :=
    {| body := simF_ |}.
  Next Obligation.
    intros R R' HR b sα sβ Hsim.
    destruct Hsim as [sα sβ [Hvis [Hsil Hdiv]] | sα sβ Hdp]; constructor.
    - split; [| split].
      + intros e sα' Hstep. destruct (Hvis e sα' Hstep) as [sβ' [sβ_mid [H1 [H2 H3]]]].
        exists sβ', sβ_mid. split; [exact H1 | split; [exact H2 | apply HR←; exact H3]].
      + intros sα' Hstep. destruct (Hsil sα' Hstep) as [[sβ' [H1 H2]] | [H1 H2]].
        * left. exists sβ'. split; [exact H1 | apply HR←; exact H2].
        * right. split; [apply HR←; exact H1 | apply HR→; exact H2].
      + intros Hd. destruct (Hdiv Hd) as [H1 H2].
        split; [apply HR←; exact H1 | apply HR→; exact H2].
    - exact (Hbody divpresF R→ R'→ HR→ sα sβ Hdp).
  Qed.
End SIMF.

Section SIM.
  Context {E : Type} {Sα Sβ : Type} {Sα_po : PPoset Sα} {Sβ_po : PPoset Sβ}.

  Definition sim_ 
    (α : Sα -> convex_set (Tsil E Sα)) 
    (β : Sβ -> convex_set (Tsil E Sβ)) : bool -> rel Sα Sβ := gfp (simF α β).

  Definition sim (α : SilLTS E Sα) (β : SilLTS E Sβ) : Prop :=
    forall sα, sα ∈ init α -> exists sβ, sβ ∈ init β /\ sim_ α β true sα sβ.

  Lemma sim_unfold {α : SilLTS E Sα} {β : SilLTS E Sβ} {sα sβ}: 
    sim_ α β true sα sβ <-> simF α β (sim_ α β) true sα sβ.
  Proof.
    split.
    - intros Hsim. unfold sim_ in Hsim. apply (gfp_fp (simF α β)) in Hsim.
      assumption.
    - intros HsimF. unfold sim_. apply (gfp_fp (simF α β)). assumption.
  Qed.

  Lemma sim_div_unfold {α : SilLTS E Sα} {β : SilLTS E Sβ} {sα sβ}: 
    sim_ α β false sα sβ <-> divpresInd α β (sim_ α β false) sα sβ.
  Proof.
    split.
    - intros Hsim. apply (gfp_fp (simF α β)) in Hsim. inversion Hsim; subst.
      assumption.
    - intros HsimF. apply (gfp_fp (simF α β)). constructor. exact HsimF.
  Qed.
End SIM.

Local Close Scope em_scope.
Local Open Scope set_scope.

Section CORRECTNESS.
  Context {E : Type}
    {Sα : Type} `{Sα_dcpo: DCPO Sα} `{!Finitary (R := lce (P := Sα))}
    {Sβ : Type} `{Sβ_dcpo: DCPO Sβ} `{!Finitary (R := lce (P := Sβ))}. 

  Lemma sim_sil_star {α : SilLTS E Sα} {β : SilLTS E Sβ} {sα sα'} sβ :
    α ⊢ sα -ɛ*-> sα' -> sim_ α β true sα sβ ->
    exists sβ', β ⊢ sβ -ɛ*-> sβ' /\ sim_ α β true sα' sβ'.
  Proof.
    intros Hstar. revert sβ.
    induction Hstar as [sα | sα sα1 sα' Hstep _ IH]; intros sβ Hsim.
    - exists sβ. split; [constructor | exact Hsim].
    - apply (proj1 sim_unfold) in Hsim. inversion Hsim as [? ? [_ [Hsil _]] |]; subst.
      destruct (Hsil sα1 Hstep) as [[sβ1 [[sβm [Hβ Hβstar]] HR]] | [HR _]].
      + destruct (IH sβ1 HR) as [sβ' [Hstar' Hsim']].
        exists sβ'. split; [| exact Hsim'].
        eapply sil_star_cons. apply Hβ. eapply sil_star_trans.
        eapply Hβstar. assumption.
      + apply IH. assumption.
  Qed.

  Lemma sim_div_divpres {α : SilLTS E Sα} {β : SilLTS E Sβ} :
    forall sα sβ, sim_ α β false sα sβ -> diverges α sα -> diverges β sβ.
  Proof. 
    change (forall sα sβ, sim_ α β false sα sβ -> diverges α sα -> gfp (divergesF β) sβ).
    coinduction R CH.
    intros sα sβ Hsim Hd. apply sim_div_unfold in Hsim.
    revert Hd. induction Hsim as [sα sβ Hstep Hdiv]. intros Hd.
    pose proof Hd as Hd0. apply diverges_unfold in Hd. destruct Hd as [Hd | [sα' [Hα Hd]]].
    - destruct (Hdiv Hd) as [[sβ' [Hβ HR]] | Hβ].
      + right. exists sβ'. split. exact Hβ. eapply CH. apply HR. apply Hd0.
      + left. exact Hβ.
    - destruct (Hstep sα' Hα) as [[sβ' [Hβ HR]] | [_ IH]].
      + right. exists sβ'. split. exact Hβ. eapply CH. apply HR. assumption.
      + apply IH. assumption.
  Qed.

  Lemma diverges_sil_star {β : SilLTS E Sβ} (R : Chain (divergesF β)) s s' :
    β ⊢ s -ɛ*-> s' -> `R s' -> `R s.
  Proof.
    induction 1 as [| s s_mid s' Hstep _ IH]; intros Hs'.
    - exact Hs'.
    - apply (b_chain R). right. exists s_mid. split; [exact Hstep | exact (IH Hs')].
  Qed.

  Lemma sim_divpres {α : SilLTS E Sα} {β : SilLTS E Sβ} :
    forall sα sβ, sim_ α β true sα sβ -> diverges α sα -> diverges β sβ.
  Proof.
    change (forall sα sβ, sim_ α β true sα sβ -> diverges α sα -> gfp (divergesF β) sβ).
    coinduction R CH.
    intros sα sβ Hsim Hd. apply (proj1 sim_unfold) in Hsim.
    inversion Hsim as [? ? [_ [Hsil Hdiv]] |]; subst.
    pose proof Hd as Hd0. apply diverges_unfold in Hd. destruct Hd as [Hd | [sα' [Hα Hd]]].
    - destruct (Hdiv Hd) as [_ Hfalse].
      apply (gfp_bchain R). eapply sim_div_divpres. apply Hfalse. assumption.
    - destruct (Hsil sα' Hα) as [[sβ' [[s_mid [Hβ Hstar]] HR]] | [_ Hfalse]].
      + right. exists s_mid. split; [exact Hβ |].
        apply (diverges_sil_star R s_mid sβ' Hstar). exact (CH sα' sβ' HR Hd).
      + apply (gfp_bchain R). eapply sim_div_divpres. exact Hfalse. assumption.
  Qed.

  Lemma soundness_at {α : SilLTS E Sα} {β : SilLTS E Sβ} {sα : Sα} {sβ : Sβ} : 
    sim_ α β true sα sβ -> traces_at (louden α) sα ⊆ traces_at (louden β) sβ.
  Proof.
    intros Hsim s Hs. apply traces_at_mem. 
    apply traces_at_mem in Hs.
    destruct Hs as [s' [Hlouden Hs']]. apply (proj1 sim_unfold) in Hsim.
    destruct s' as [ | [e sα']].
    - exists ↺. split; [| exact Hs'].
      apply louden_mem_div. apply (gfp_fp (simF α β)) in Hsim. 
      eapply sim_divpres. exact Hsim. 
      apply louden_mem_div. assumption.
    - apply louden_vis_elim in Hlouden. destruct Hlouden as [sα_mid [sα_mid' Hl]].
      simpl in sα_mid'. destruct Hsim as [Hsim | Hsim].
      +   

  Theorem soundness {α : SilLTS E Sα} {β : SilLTS E Sβ} : 
    sim α β -> α ⊒ β.
  Proof.
    intros Hsim. unfold refines, traces. intros p Hp.
    apply em_ext_set_mem in Hp as (sα & Hsα & Hp). rewrite louden_init in Hsα.
    destruct (Hsim sα Hsα) as (sβ & Hsβ & Hsim').
    apply em_ext_set_mem. exists sβ. split.
    - rewrite louden_init. exact Hsβ.
    - apply (soundness_at Hsim'). exact Hp.
  Qed.
  
  Theorem completeness {α : SilLTS E Sα} {β : SilLTS E Sβ} :
    α ⊒ β -> sim α β.
  Admitted.
  
End CORRECTNESS.