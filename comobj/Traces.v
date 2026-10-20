Require Import comobj.SilLTS.
Require Import comobj.VisLTS.

Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.

Require Import Stdlib.Logic.FunctionalExtensionality.


Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
Local Abbreviation id := (fun x => x).

(** * Traces *)

(** ** Definition, Bissimulation and Equality *)

(** A trace over E is just the final coalgebra of [TVis E] computed over [PreDCPO] *)

CoInductive Tr E := 
| Tr_div : Tr E
| Tr_step : E -> Tr E -> Tr E.
Arguments Tr_div {_}.
Arguments Tr_step {_} _ _.

Declare Scope tr_scope.
Delimit Scope tr_scope with tr.
Bind Scope tr_scope with Tr.

Notation "↺" := Tr_div : tr_scope.
Notation "e ⋅ t" :=(Tr_step e t) (at level 60, right associativity) : tr_scope.

Open Scope tr_scope.

Definition Tr_frob {E} (t : Tr E) : Tr E := 
  match t with
  | ↺ => ↺
  | e ⋅ tl => e ⋅ tl
  end.

Lemma Tr_frob_eq {E} (t : Tr E) : t = Tr_frob t.
Proof.
  destruct t; reflexivity.
Qed.

(** It's notion of equality is necessarilly bisimulation *)
CoInductive Tr_bisim {E} : Tr E -> Tr E -> Prop := 
| Tr_bisim_div : Tr_bisim ↺ ↺
| Tr_bisim_step e tr e' tr' : 
    e = e' -> Tr_bisim tr tr' -> Tr_bisim (e ⋅ tr) (e' ⋅ tr').

(** which comes with an associatiated coinductive principle *)
Lemma Tr_bisim_coind {E} (R : Tr E -> Tr E -> Prop) :
  (forall s t, R s t -> 
    match s, t with
    | ↺, ↺ => True
    | e ⋅ s', e' ⋅ t' => e = e' /\ R s' t'
    | _,_ => False
    end) ->
  forall s t, R s t -> Tr_bisim s t.
Proof.
  intros H. cofix CIH. intros s t HI.
  specialize (H s t HI). destruct s as [| e s'], t as [| e' t'].
  - constructor.
  - contradiction.
  - contradiction.
  - destruct H. constructor. assumption. apply CIH. assumption.
Qed.

Global Instance Tr_bisim_equiv E : Equivalence (Tr_bisim (E := E)).
Proof.
  split.
  - intros s. apply (Tr_bisim_coind eq); [| reflexivity].
    clear s. intros s t Heq. subst. destruct t. 
    + exact I.
    + split; reflexivity.
  - intros s t H. apply (Tr_bisim_coind (fun s t => Tr_bisim t s)); [| assumption].
    clear H s t. intros s t H. destruct s as [| e s'], t as [| e' t'].
    + exact I.
    + inversion H.
    + inversion H.
    + inversion H; subst. split; [reflexivity | assumption].
  - intros t1 t2 t3 t12 t23.
    apply (Tr_bisim_coind (fun t1 t3 => exists t2, Tr_bisim t1 t2 /\ Tr_bisim t2 t3));
      [| exists t2; split; assumption].
    intros s t HI. destruct s, t; try (exact I).
    + destruct HI as [t' [HIl HIr]]. destruct t'.
      inversion HIr. inversion HIl.
    + destruct HI as [t' [HIl HIr]].
      destruct t'. inversion HIl. inversion HIr.
    + destruct HI as [t' [HIl HIr]]. destruct t'.
      * inversion HIl.
      * inversion HIl; inversion HIr; subst. split. reflexivity.
        exists t'. split; assumption.
Qed.

(** While not derivable, it is consistent and convenient to assume bisimulation implies equality *)
Axiom Tr_bisim_eq : forall E, forall (s t : Tr E), Tr_bisim s t -> s = t.

(** ** DCPO structure *)
CoInductive Tr_lce {E} : Tr E -> Tr E -> Prop := 
| Tr_lce_div tr : Tr_lce ↺ tr
| Tr_lce_step e tr e' tr' : 
  e = e' -> Tr_lce tr tr' -> Tr_lce (e ⋅ tr) (e' ⋅ tr').

Lemma Tr_lce_coind {E} (R : Tr E -> Tr E -> Prop) : 
  (forall s t, R s t -> 
    match s, t with 
    | ↺, _ => True 
    | e ⋅ s', e' ⋅ t' => e = e' /\ R s' t'
    | _ ⋅ _, ↺ => False
    end) ->
  forall s t, R s t -> Tr_lce s t.
Proof.
  intros H. cofix CIH. intros s t HI.
  specialize (H s t HI). destruct s as [| e s'], t as [| e' t'].
  1,2: constructor. contradiction. 
  destruct H as [Heq HR]. constructor. assumption.
  apply CIH. assumption.
Qed.

Global Instance Tr_pro (E : Type) : PreOrder (Tr_lce (E := E)).
Proof.
  split.
  + intros t. apply (Tr_lce_coind eq); [|reflexivity].
    clear t. intros s t Heq. destruct s, t; try (exact I).
    inversion Heq. inversion Heq. easy.
  + intros t1 t2 t3 t12 t23.
    apply (Tr_lce_coind (fun t1 t3 => exists t2, Tr_lce t1 t2 /\ Tr_lce t2 t3));
      [| exists t2; split; assumption].
    intros s t HI. destruct s, t; try (exact I).
    * destruct HI as [t' [HIl HIr]]. destruct t'.
      inversion HIl. inversion HIr.
    * destruct HI as [t' [HIl HIr]].
      destruct t'. inversion HIl.
      inversion HIl. inversion HIr. subst. 
      split. reflexivity.
      exists t'. split; assumption.
Qed.

Lemma Tr_antisym {E} (s t : Tr E) : Tr_lce s t -> Tr_lce t s -> Tr_bisim s t.
Proof.
  intros Hst Hts. apply (Tr_bisim_coind (fun s t => Tr_lce s t /\ Tr_lce t s));
  [| split;assumption]. clear Hst Hts s t.
  intros s t [Hst Hts]. destruct s as [| e s'], t as [| e' t'].
  - exact I.
  - inversion Hts.
  - inversion Hst.
  - inversion Hst; inversion Hts; subst. split. reflexivity. split; assumption.
Qed.

Global Instance Tr_po (E : Type) : PartialOrder (Tr_lce (E := E)).
Proof.
  split. typeclasses eauto. intros s t Hst Hts.
  apply Tr_bisim_eq. apply Tr_antisym; assumption.
Qed.

Local Instance Tr_pointed (E : Type) : Pointed (Tr_lce (E := E)).
Proof.
  exists ↺. intros t. constructor.
Qed.

Lemma Tr_bot_eq (E : Type) : bot = Tr_div (E := E).
Proof.
  symmetry. apply lce_bot_eq. constructor.
Qed.

Definition Tr_tl {E} (t : Tr E) : Tr E := 
  match t with
  | ↺ => ↺
  | e ⋅ tl => tl
  end.

Global Instance Tr_tl_pc {E} : PreContinuous (Tr_tl (E := E)).
Proof.
  split.
  - intros s t Hst. destruct s as [| e s'], t as [| e' t'].
    + constructor.
    + constructor.
    + inversion Hst.
    + inversion Hst; subst. assumption.
  - unfold Strict. rewrite Tr_bot_eq. reflexivity.
Qed.

Open Scope tsil_scope.

Definition Tr_hd {E} (t : Tr E) : lift E eq :=
  match t with
  | ↺%tr => ↺
  | e ⋅ _ => ↑e
  end.

Global Instance Tr_hd_mon {E} : PreContinuous (Tr_hd (E := E)).
Proof.
  split.
  - intros s t Hst. destruct s as [| e s'], t as [| e' t']; simpl.
    + reflexivity.
    + constructor.
    + inversion Hst.
    + inversion Hst; subst. constructor. reflexivity.
  - unfold Strict. rewrite Tr_bot_eq. simpl. symmetry. apply lift_bot_eq.
Qed.

CoFixpoint Tr_dsup {E} {I} (x : I -> Tr E) `{!Directed (R := Tr_lce) x} : Tr E :=
  match dsup (fun i => Tr_hd (x i)) with
  | ↺ => ↺
  | ↑e => e ⋅ (Tr_dsup (fun i => Tr_tl (x i)))
  end.

Lemma Tr_dsup_unfold {E} {I} (x : I -> Tr E) `{!Directed (R := Tr_lce) x} :
  Tr_dsup x =
    match dsup (fun i => Tr_hd (x i)) with
    | lift_bot => Tr_div
    | lift_el e => Tr_step e (Tr_dsup (fun i => Tr_tl (x i)))
    end.
Proof.
  rewrite Tr_frob_eq. rewrite (Tr_frob_eq (Tr_dsup x)). reflexivity.
Qed.

Lemma Tr_dsup_is_sup {E} {I} (x : I -> Tr E) `{!Directed (R := Tr_lce) x} :
  IsSup (R := Tr_lce) x (Tr_dsup x).
Proof.
  split.
  - intros i.
    apply (Tr_lce_coind (fun s t => exists (y : I -> Tr E) (Hy : Directed (R := Tr_lce) y) i, s = y i /\ t = Tr_dsup y)).
    + clear Directed0 x i. intros s t CIH. destruct s as [| e s']. trivial.
      destruct CIH as [x [HDx [i [Heq Hdsup]]]]. subst.
      pose proof (dsup_ub (fun i0 : I => Tr_hd (x i0)) i) as H.
      simpl in H. rewrite <- Heq in H. simpl in H. inversion H; subst.
      rewrite Tr_dsup_unfold. simpl. rewrite <- H1.
      split. reflexivity. exists ((fun i1 : I => Tr_tl (x i1))). 
      exists _. exists i. split.
      * rewrite <- Heq. reflexivity.
      * reflexivity.
    + exists x. exists Directed0. exists i. split. reflexivity. reflexivity.    
  - intros y Hlce. 
    apply (Tr_lce_coind (fun s u => exists (y : I -> Tr E) (Hy : Directed (R := Tr_lce) y), s = Tr_dsup y /\ forall i, Tr_lce (y i) u)).
    + clear Directed0 Hlce y x. intros s t CIH.
      destruct CIH as [x [HDx [Heq CIH]]]. rewrite Tr_dsup_unfold in Heq.
      destruct (dsup (fun i : I => Tr_hd (x i))) as [| e] eqn:H; subst.
      * trivial.
      * assert (Hhd: lce (lift_el e : lift E eq) (Tr_hd t)).
        { rewrite <- H. apply (dsup_lub (fun i : I => Tr_hd (x i)) (Tr_hd t)). 
          intros i. apply pc_mon. apply CIH. }
        inversion Hhd; subst. destruct t as [| e t]. inversion H1.
        simpl in H1. inversion H1. split. reflexivity.
        exists (fun i : I => Tr_tl (x i)). exists _. split.
        reflexivity. intros i. specialize (CIH i).
        inversion CIH; subst; simpl. constructor.
        rewrite <- H0 in CIH. inversion CIH; subst. assumption.
    + exists x. exists Directed0. split. reflexivity. assumption.
Qed.

Local Instance Tr_dcpo E : DCPO (Tr E) :=
  {
    lce := Tr_lce;
    dsup I x Hx := Tr_dsup x;
    dsup_is_sup I x Hx := Tr_dsup_is_sup x;
  }.

Global Hint Extern 1 (DCPO (Tr _)) => simple eapply @Tr_dcpo : typeclass_instances.

(** ** Final Coalgebra Structure *)

Definition Tr_unfold {E} : Tr E -> Tvis E (Tr E) :=
  fun t => 
    match t with
    | ↺%tr => ↺
    | e ⋅ tl => -e-> tl
    end.

Lemma Tr_unfold_pc {E} : PreContinuous (Tr_unfold (E := E)).
Proof.
  split.
  - intros s t Hst. destruct s as [| e s'], t as [| e' t']; simpl.
    + reflexivity.
    + constructor.
    + inversion Hst.
    + inversion Hst; subst. constructor. split; [reflexivity|]. assumption.
  - unfold Strict. rewrite Tr_bot_eq. rewrite Tvis_bot_eq. reflexivity.
Qed.

Definition Tr_fold {E} : Tvis E (Tr E) -> Tr E :=
  fun t =>
    match t with
    | ↺ => ↺%tr
    | -e-> tl => e ⋅ tl
    end.

Lemma Tr_fold_pc {E} : PreContinuous (Tr_fold (E := E)).
Proof.
  split.
  - intros s t Hst. destruct s as [| s], t as [| t].
    + reflexivity.
    + constructor.
    + inversion Hst.
    + destruct s as [e s], t as [e' t]. inversion Hst; subst. destruct H1.
      simpl in *. subst. constructor. reflexivity. assumption.
  - unfold Strict. rewrite Tr_bot_eq. rewrite Tvis_bot_eq. reflexivity.
Qed.

Lemma Tr_fold_unfold_eq {E} : @Tr_unfold E ;; Tr_fold = id.
Proof.
  apply functional_extensionality. intros t.
  destruct t as [| e t]. reflexivity. reflexivity.
Qed.

Lemma Tr_unfold_fold_eq {E} : @Tr_fold E ;; Tr_unfold = id.
Proof.
  apply functional_extensionality. intros t.
  destruct t as [| [e t]]. reflexivity. reflexivity.
Qed.

CoFixpoint Tr_ana {E S} `{DCPO S} (a : S -> Tvis E S) : S -> Tr E :=
  fun s => 
    match (a s) with
    | ↺ => ↺%tr
    | -e-> s' => e ⋅ (Tr_ana a s')
    end.

Lemma Tr_ana_homo {E S} `{DCPO S} (a : S -> Tvis E S) : 
  a ;; Tvis_map id (Tr_ana a) = Tr_ana a ;; Tr_unfold.
Proof.
  apply functional_extensionality. intros s. simpl.
  destruct (a s) as [| [e s']]; simpl; reflexivity.
Qed.

Lemma Tr_ana_bisim {E S} `{DCPO S} (a : S -> Tvis E S) (f : S -> Tr E) :
  a ;; Tvis_map id f = f ;; Tr_unfold -> forall s, Tr_bisim (f s) (Tr_ana a s).
Proof.
  intros Heq s.
  apply (Tr_bisim_coind (fun s t => exists i, s = f i /\ t = Tr_ana a i)).
  - clear s. intros s t CIH. destruct CIH as [i [Hfeq Hana]].
    apply (f_equal (fun g => g i)) in Heq. symmetry in Hfeq, Hana.
    rewrite (Tr_frob_eq (Tr_ana a i)) in Hana. simpl in Hana.
    destruct s as [| e s], t as [| e' t]; simpl in *.
    + exact I.
    + destruct (a i) as [| [ea sa]] eqn:Ha.
      * inversion Hana.
      * rewrite Hfeq in Heq. simpl in Heq. inversion Heq.
    + rewrite Hfeq in Heq. destruct (a i) as [| [ea sa]] eqn:Ha.
      * simpl in Heq. inversion Heq.
      * inversion Hana.
    + destruct (a i) as [| [ea sa]] eqn:Ha; inversion Hana; subst.
      rewrite Hfeq in Heq. simpl in Heq. inversion Heq; subst.
      split. reflexivity.
      exists sa. split; reflexivity.
  - exists s; split; reflexivity.
Qed.

Lemma Tr_ana_unique {E S} `{DCPO S} (a : S -> Tvis E S) (f : S -> Tr E) :
  a ;; Tvis_map id f = f ;; Tr_unfold -> f = (Tr_ana a).
Proof.
  intros. apply functional_extensionality. intros. 
  apply Tr_bisim_eq. apply Tr_ana_bisim. assumption.
Qed.