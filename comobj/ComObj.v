Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Require Import Stdlib.Lists.List.
Import ListNotations.

Require Import Stdlib.Logic.FunctionalExtensionality.

Require Import comobj.SilentEvents.
Import SilentEvents.

Definition Tsil (E S : Type) {Sdcpo : DCPO S} : Type :=
  lift (Sil E * S) (eq * lce)%rel.

(** Instance search must not unfold [Tsil]: it is literally [Tvis (Sil E) S],
  and the two must not compete for the same instances. *)
#[global] Typeclasses Opaque Tsil.

Declare Scope tsil_scope.
Delimit Scope tsil_scope with tsil.

Notation "↑ s" := (lift_el s) (at level 9, s at next level) : tsil_scope.
Notation "↺" := lift_bot : tsil_scope.
Notation "- a -> t" := (lift_el (a, t))
  (at level 35, a at level 35, t at level 35) : tsil_scope.

Open Scope tsil_scope.

Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
Local Abbreviation id := (fun x => x).

Section TSIL.
  Context {E S : Type} {Sdcpo : DCPO S}.
  Global Instance Tsil_dcpo : DCPO (Tsil E S) := lift_dcpo.

  Lemma Tsil_bot : (bot : Tsil E S) = ↺.
  Proof. apply lift_bot_eq. Qed.

  Global Instance Tsil_finitary `{!Finitary (R := lce (P := S))} :
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
End TSIL.

Record comobj E S {Sdcpo : DCPO S} :=
  {
    trans :> S -> convex_set (Tsil E S);
    init : S -> Prop;
    trans_mon :: Monotonic trans (lce ++> lce);
    trans_strict :: Strict trans;
  }.

Definition sil_loop {E} : comobj E (lift unit eq) :=
  lift_ext (D := convex_set (Tsil E (lift unit eq))) (fun s => {{-ɛ-> ↑s}}).

