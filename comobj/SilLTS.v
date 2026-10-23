Require Import interfaces.Functor.

Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.KDCPOs.
Require Export structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import Stdlib.Logic.FunctionalExtensionality.

Require Export comobj.SilEvents.
Export SilEvents.
Require Import comobj.LCoalg.

Local Open Scope em_scope.

(** * Communicating Objects *)

(** ** Transition Shape *)

(** A communicating object has several types of transitions:
- [↺] a divergent transition
- [-ɛ-> s] a silent transition to a new state [s]
- [-'e-> s] a visible transition with label [e] to a new state [s]
Note that since [S] has its own bottom element, there are also the following
special transitions:
- [-ɛ-> ↺_S] a silent transition to the later diverging state [↺_S]
- [-'e-> ↺_S] a visible transition to the later diverging state [↺_S]
these are special in that the only possible transition out of [↺_S] will
be the divergent transition [↺]
*)
Definition Tsil (E S : Type) {Spp : PPoset S} : Type :=
  lift (Sil E * S) (eq * pref)%rel.

#[global] Typeclasses Opaque Tsil.

Declare Scope tsil_scope.
Delimit Scope tsil_scope with tsil.

Notation "↑ s" := (lift_el s) (at level 9, s at next level) : tsil_scope.
Notation "↺" := lift_bot : tsil_scope.
Notation "- a -> t" := (lift_el (a, t))
  (at level 35, a at level 35, t at level 35) : tsil_scope.
Notation "↺_S" := (bot (R := pref)) : tsil_scope.

Open Scope tsil_scope.

Local Abbreviation id := (fun x => x).

Section TSIL.
  Context {E S : Type} {Spp : PPoset S}.
  Local Instance Tsil_ppo : PPoset (Tsil E S) := lift_ppo.

  Lemma Tsil_ppo_bot_eq : (bot : Tsil E S) = ↺.
  Proof. apply lift_ppo_bot_eq. Qed.

  Section TSIL_DCPO.
    Context {Sdc : DirectedComplete (R := pref (P := S))}.
    Local Instance Tsil_dcpo : DCPO (Tsil E S) := lift_dcpo.

    Lemma Tsil_bot_eq : (bot : Tsil E S) = ↺.
    Proof. apply lift_bot_eq. Qed.

    Global Instance Tsil_finitary `{!Finitary (R := pref (P := S))} :
      Finitary (R := lce (P := Tsil E S)).
    Proof.
      intros d. destruct d as [| [a s]].
      - exists [↺]. intros x. split.
        + intros H. inversion H; subst. left. reflexivity.
        + intros [<- | []]. constructor.
      - destruct (finitary s) as [l Hl].
        exists (↺ :: map (fun s' => - a -> s') l). intros x. split.
        + intros H. inversion H as [| x' y' Hp]; subst; [left; reflexivity |].
          destruct x' as [a' s']. destruct Hp as [Ha Hs]. cbn in Ha, Hs. subst a'.
          right. apply in_map_iff. exists s'. split; [reflexivity | apply Hl; exact Hs].
        + intros [<- | Hin]; [constructor |].
          apply in_map_iff in Hin. destruct Hin as [s' [<- Hs']].
          constructor. split; [reflexivity | apply Hl; exact Hs'].
    Qed.
  End TSIL_DCPO.
End TSIL.

Global Hint Extern 1 (PPoset (Tsil _ _)) => simple eapply @Tsil_ppo : typeclass_instances.
Global Hint Extern 1 (DCPO (Tsil _ _)) => simple eapply @Tsil_dcpo : typeclass_instances.

Section TSIL_MAP.
  Context {E E' S S' : Type} {Spp : PPoset S} {Spp' : PPoset S'}.

  Definition Tsil_map (l : SilEvents.m E E') (h : S -> S') (t : Tsil E S) : Tsil E' S' :=
    match t with
    | ↺ => ↺
    | -a-> s => -(SilEvents.ext l a)-> h s
    end.

  Lemma Tsil_map_mon l (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} :
    Monotonic (Tsil_map l h) (pref ++> pref).
  Proof.
    intros t u Htu. inversion Htu as [? | [a s] [a' s'] [Ha Hs]]; subst; cbn.
    - constructor.
    - cbn in Ha. subst a'. constructor. split; [reflexivity | exact (pc_mon (f := h) s s' Hs)].
  Qed.

  Lemma Tsil_map_strict l h : Strict (RA := pref) (RB := pref) (Tsil_map l h).
  Proof. unfold Strict. rewrite !Tsil_ppo_bot_eq. reflexivity. Qed.

  Definition Tsil_map_pc l (h : S -> S') `{!PreContinuous (RA := pref) (RB := pref) h} :
    PreContinuous (RA := pref) (RB := pref) (Tsil_map l h) :=
    {| pc_mon := Tsil_map_mon l h; pc_strict := Tsil_map_strict l h |}.
End TSIL_MAP.

Module TsilF <: Bifunctor SilEvents PPoset PPoset.
  Definition omap (E : SilEvents.t) (S : PPoset.t) : PPoset.t :=
    PPoset.mkt (Tsil E (PPoset.carrier S)).

  Definition fmap {E1 S1 E2 S2} (l : SilEvents.m E1 E2) (h : PPoset.m S1 S2) :
    PPoset.m (omap E1 S1) (omap E2 S2) :=
    @PPoset.mkm (omap E1 S1) (omap E2 S2)
      (Tsil_map l (PPoset.apply _ _ h)) (Tsil_map_pc l (PPoset.apply _ _ h)).

  Proposition fmap_id E S :
    fmap (SilEvents.id E) (PPoset.id S) = PPoset.id (omap E S).
  Proof. apply PPoset.meq. intros [| [[e |] s]]; reflexivity. Qed.

  Proposition fmap_compose {E1 S1 E2 S2 E3 S3}
      (l' : SilEvents.m E2 E3) (h' : PPoset.m S2 S3)
      (l : SilEvents.m E1 E2) (h : PPoset.m S1 S2) :
    fmap (SilEvents.compose l' l) (PPoset.compose h' h) =
      PPoset.compose (fmap l' h') (fmap l h).
  Proof.
    apply PPoset.meq. intros [| [[e |] s]]; cbn; [reflexivity | | reflexivity].
    unfold SilEvents.compose. destruct (l e); reflexivity.
  Qed.

  Include BifunctorTheory SilEvents PPoset PPoset.
End TsilF.

(** ** LTSs with Silent Events *)
Module SilLTS := LCoalg SilEvents TsilF.
Import SilLTS.

Local Instance T_dcpo {E S} `{DCPO S} : DCPO (T E S) := Tsil_dcpo.
Global Hint Extern 1 (DCPO (SilLTS.T _ _)) => simple eapply @T_dcpo : typeclass_instances.

Global Instance T_dcomplete {E S} `{DCPO S} : DirectedComplete (R := pref (P := T E S)) :=
  lift_dcomplete.

Global Instance T_finitary {E S} `{DCPO S} `{!Finitary (R := lce (P := S))} :
  Finitary (R := lce (P := T E S)) := Tsil_finitary.

Abbreviation SilLTS := lcoalg.

Notation "α ⊢ s - e -> t" := (-e-> t ∈ α s)
  (at level 70, s at level 35, e at level 35, t at level 35) : tsil_scope.

(** ** Simple Communicating Objects *)

(** The communicating object [sil_loop] consists of a single non-diverging
state [tt] and a silent-loop on it. *)
Definition sil_loop E : SilLTS E (lift unit eq) :=
  flat_lcoalg (fun s => {{-ɛ-> ↑s}}) (fun _ => True).
