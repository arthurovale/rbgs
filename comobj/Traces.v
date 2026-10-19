Require Import comobj.VisLTS.
Require Import structures.Posets.

CoInductive Tr E := 
| Tr_div : Tr E
| Tr_step : E -> Tr E -> Tr E.
Arguments Tr_div {_}.
Arguments Tr_step {_} _ _.

CoInductive Tr_lce {E} : Tr E -> Tr E -> Prop := 
| Tr_lce_div tr : Tr_lce Tr_div tr
| Tr_lce_step e tr e' tr' : 
  e = e' -> Tr_lce tr tr' -> Tr_lce (Tr_step e tr) (Tr_step e' tr').

Lemma Tr_lce_coind {E} (R : Tr E -> Tr E -> Prop) : 
  (forall s t, R s t -> 
    match s, t with 
    | Tr_div, _ => True 
    | Tr_step e s', Tr_step e' t' => e = e' /\ R s' t'
    | Tr_step _ _, Tr_div => False
    end) ->
  forall s t, R s t -> Tr_lce s t.
Proof.
  intros H. cofix CIH. intros s t I.
  specialize (H s t I). destruct s as [| e s'], t as [| e' t'].
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