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
Definition Tsil (E S : Type) {Sdcpo : DCPO S} : Type :=
  lift (Sil E * S) (eq * lce)%rel.

#[global] Typeclasses Opaque Tsil.

Declare Scope tsil_scope.
Delimit Scope tsil_scope with tsil.

Notation "↑ s" := (lift_el s) (at level 9, s at next level) : tsil_scope.
Notation "↺" := lift_bot : tsil_scope.
Notation "- a -> t" := (lift_el (a, t))
  (at level 35, a at level 35, t at level 35) : tsil_scope.
Notation "↺_S" := (bot : S).

Open Scope tsil_scope.

Local Notation "f ;; g" := (fun x => g (f x)) (at level 60, right associativity).
Local Abbreviation id := (fun x => x).

Section TSIL.
  Context {E S : Type} {Sdcpo : DCPO S}.
  Local Instance Tsil_dcpo : DCPO (Tsil E S) := lift_dcpo.

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

Global Hint Extern 1 (DCPO (Tsil _ _)) => simple eapply @Tsil_dcpo : typeclass_instances.

(** ** Communicating Objects *)
Abbreviation comobj := (lcoalg Tsil).

(** ** Simple Communicating Objects *)

(** The communicating object [sil_loop] consists of a single non-diverging
state [tt] and a silent-loop on it. *)
Definition sil_loop E : comobj E (lift unit eq) :=
  flat_lcoalg Tsil (fun s => {{-ɛ-> ↑s}}) (fun _ => True).