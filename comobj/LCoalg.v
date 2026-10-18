Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.
Require Import Stdlib.Logic.ProofIrrelevance.

(** * Labelled Coalgebras *)
(** Here we provided a generic interface for labelled coalgebras. *)

Section COALG.
  (** A labelled coalgebra requires one to provide a transition shape [T] *)
  (** Since we work over a catgory of domains, to handle divergence, 
    the transition shape is required to be a functor [T : E -> S -> Type] 
    such that if the set of states [S] forms a DCPO then the transition shape 
    domain forms a DCPO. Here [E] is the space of event labels. *)
  Context (T : Type -> forall S, DCPO S -> Type).
  Arguments T _ _ {_}.
  Context `{TD : forall E S (Sdcpo : DCPO S), DCPO (T E S)}.

  (** A labelled (non-deterministic) coalgebra of shape [T] then consists of:
  - A non-deterministic transition function [trans : S -> convex_set (T E S Sdcpo)]
  - A choice of initial states
  - Proofs that the transition functions is "pre-continuous", i.e. monotonic and 
    strict. The transition function should be continuous. However, 
    due to the same sizing issues related to non-deterministic choice we 
    would need to require something like:
    [trans_kcont : exists K, KContinuous K trans]
    To make matters simpler for now, we make this "pre-continuity" requirement.
  *)
  Record lcoalg E S {Sdcpo : DCPO S} :=
    {
      trans :> S -> convex_set (T E S);
      init : convex_set S;
      trans_mon :: Monotonic trans (lce ++> em_le);
      trans_strict :: Strict (RB := em_le) trans;
    }.

  Lemma lcoalg_ext {E S} {Sdcpo : DCPO S} (a b : lcoalg E S) :
    trans E S a = trans E S b -> init E S a = init E S b -> a = b.
  Proof.
    destruct a, b; cbn. intros -> ->. f_equal; apply proof_irrelevance.
  Qed.

  (**
    I expect that for the most part base objects will be built out of the flat 
    DCPO [lift S eq] over a set of states [S]. The following shows that in that 
    case a labelled coalgebra may be defined directly as simply a transition 
    function and a (plain) set of initial states.
  *)

  Definition flat_lcoalg {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) :
    lcoalg E (lift X eq) :=
    {|
      trans := lift_ext (RD := em_le) f;
      init := {{ t | exists x, t = lift_el x /\ i x }};
      trans_mon := lift_ext_flat_mon f;
      trans_strict := lift_ext_strict f;
    |}.

  (** Some useful technical lemmas about flat coalgebras *)
  Lemma flat_lcoalg_bot {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) :
    flat_lcoalg f i lift_bot = bot.
  Proof. reflexivity. Qed.

  Lemma flat_lcoalg_el {E X} (f : X -> convex_set (T E (lift X eq))) (i : X -> Prop) (x : X) :
    flat_lcoalg f i (lift_el x) = f x.
  Proof. reflexivity. Qed.
End COALG.

Arguments trans {T TD E S Sdcpo} _.
Arguments init {T TD E S Sdcpo} _.
Arguments trans_mon {T TD E S Sdcpo} _.
Arguments trans_strict {T TD E S Sdcpo} _.
Arguments lcoalg_ext {T TD E S Sdcpo} _ _.

Section LCOALG_DCPO.
  Context (T : Type -> forall S, DCPO S -> Type).
  Arguments T _ _ {_}.
  Context `{TD : forall E S (Sdcpo : DCPO S), DCPO (T E S)}.
  Context `{TF : forall E S (Sdcpo : DCPO S),
              Finitary (R := lce (P := S)) -> Finitary (R := lce (P := T E S))}.
  Context {E S : Type} {Sdcpo : DCPO S} {Sfin : Finitary (R := lce (P := S))}.

  Definition lcoalg_le (a b : lcoalg T E S) : Prop :=
    lce (trans a) (trans b) /\ em_le (init a) (init b).

  Local Instance lcoalg_le_po : PartialOrder lcoalg_le.
  Proof.
    split.
    - split.
      + intros a. split; reflexivity.
      + intros a b c [H1 H2] [H1' H2']. split; etransitivity; eauto.
    - intros a b [H1 H2] [H1' H2']. apply lcoalg_ext; apply antisymmetry; assumption.
  Qed.

  Local Instance lcoalg_directed_trans {I} (x : I -> lcoalg T E S)
      (Hx : Directed (R := lcoalg_le) x) :
    Directed (fun i => trans (x i)).
  Proof.
    intros i j. destruct (Hx i j) as [k [[H1 _] [H2 _]]]. exists k. auto.
  Qed.

  Local Instance lcoalg_directed_init {I} (x : I -> lcoalg T E S)
      (Hx : Directed (R := lcoalg_le) x) :
    Directed (R := em_le) (fun i => init (x i)).
  Proof.
    intros i j. destruct (Hx i j) as [k [[_ H1] [_ H2]]]. exists k. auto.
  Qed.

  Lemma lcoalg_dsup_mon {I} (x : I -> lcoalg T E S) (Hx : Directed (R := lcoalg_le) x) :
    Monotonic (dsup (fun i => trans (x i))) (lce ++> em_le).
  Proof.
    intros s s' Hs.
    apply (dsup_lub (H := em_dcpo) (fun i => trans (x i) s)). intros i.
    etransitivity; [apply (trans_mon (x i)); exact Hs |].
    apply (dsup_ub (H := em_dcpo) (fun i => trans (x i) s')).
  Qed.

  Lemma lcoalg_dsup_strict {I} (x : I -> lcoalg T E S) (Hx : Directed (R := lcoalg_le) x) :
    Strict (RB := em_le) (dsup (fun i => trans (x i))).
  Proof.
    unfold Strict.
    apply (antisymmetry (R := lce)).
    - apply (dsup_lub (H := em_dcpo) (fun i => trans (x i) bot)). intros i.
      rewrite (strict_bot (f := trans (x i))). reflexivity.
    - apply bot_lb.
  Qed.

  Definition lcoalg_dsup {I} (x : I -> lcoalg T E S) (Hx : Directed (R := lcoalg_le) x) :
    lcoalg T E S :=
    {|
      trans := dsup (fun i => trans (x i));
      init := dsup (fun i => init (x i));
      trans_mon := lcoalg_dsup_mon x Hx;
      trans_strict := lcoalg_dsup_strict x Hx;
    |}.

  Lemma lcoalg_dsup_issup {I} (x : I -> lcoalg T E S) (Hx : Directed (R := lcoalg_le) x) :
    IsSup (R := lcoalg_le) x (lcoalg_dsup x Hx).
  Proof.
    split.
    - intros i. split.
      + exact (dsup_ub (fun i => trans (x i)) i).
      + exact (dsup_ub (H := em_dcpo) (fun i => init (x i)) i).
    - intros y Hy. split.
      + exact (dsup_lub (fun i => trans (x i)) (trans y) (fun i => proj1 (Hy i))).
      + exact (dsup_lub (H := em_dcpo) (fun i => init (x i)) (init y) (fun i => proj2 (Hy i))).
  Qed.

  Local Instance lcoalg_dcpo : DCPO (lcoalg T E S) :=
    {|
      lce := lcoalg_le;
      lce_po := lcoalg_le_po;
      dsup := @lcoalg_dsup;
      dsup_is_sup := @lcoalg_dsup_issup;
    |}.
End LCOALG_DCPO.

Global Hint Extern 1 (DCPO (lcoalg _ _ _)) => simple eapply @lcoalg_dcpo : typeclass_instances.
