From Coinduction Require Import all.

Require Import coqrel.LogicalRelations.

Require Import comobj.SilLTS.
Import SilLTS.

Require Import comobj.VisLTS.
Require Import comobj.Traces.
Require Import comobj.Refinement.

Local Open Scope em_scope.

Reserved Notation "α ⊢ s -ɛ*-> t" (at level 70, s at level 35, t at level 35).

Inductive sil_star {E : Type} {Sα : Type} {Sα_po : PPoset Sα}
  (α : Sα -> convex_set (Tsil E Sα)) : Sα -> Sα -> Prop :=
| sil_star_nil s : α ⊢ s -ɛ*-> s
| sil_star_cons s s_mid s' : 
  α ⊢ s -ɛ-> s_mid -> α ⊢ s_mid -ɛ*-> s' -> α ⊢ s -ɛ*-> s'
  where "α ⊢ s -ɛ*-> t" := (sil_star α s t) : tsil_scope.

Definition sil_plus {E : Type} {Sα : Type} {Sα_po : PPoset Sα}
  (α : Sα -> convex_set (Tsil E Sα)) : Sα -> Sα -> Prop := 
  fun s s' => exists s_mid, α ⊢ s -ɛ-> s_mid /\ α ⊢ s_mid -ɛ*-> s'.

Notation "α ⊢ s -ɛ+-> t" := (sil_plus α s t) (at level 70, s at level 35, t at level 35).

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
End SIM.

Local Close Scope em_scope.
Local Open Scope set_scope.

Section CORRECTNESS.
  Context {E : Type}
    {Sα : Type} `{DCPO Sα} `{!Finitary (R := lce (P := Sα))}
    {Sβ : Type} `{DCPO Sβ} `{!Finitary (R := lce (P := Sβ))}. 

  Lemma soundness_at {α : SilLTS E Sα} {β : SilLTS E Sβ} {sα : Sα} {sβ : Sβ} : 
    sim_ α β true sα sβ -> traces_at (louden α) sα ⊆ traces_at (louden β) sβ.
  Admitted.

  Theorem soundness {α : SilLTS E Sα} {β : SilLTS E Sβ} : 
    sim α β -> α ⊒ β.
  Proof.
    intros Hsim. unfold refines, traces. unfold subset.
    intros p. intros Hp. destruct Hp as [[sα Hsα]  Hp].
    unfold sim in Hsim. remember Hsα as Hsα'. clear HeqHsα'. 
    rewrite louden_init in Hsα. specialize (Hsim sα Hsα).
    destruct Hsim as [sβ [Hsβ Hsim]]. cbn [proj1_sig] in Hp.
    unshelve eexists. rewrite <- louden_init in Hsβ. exact (exist _ sβ Hsβ).
    apply (soundness_at Hsim). assumption.
  Qed.
  
  Theorem completeness {α : SilLTS E Sα} {β : SilLTS E Sβ} :
    α ⊒ β -> sim α β.
  Admitted.
  
End CORRECTNESS.