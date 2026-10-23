Require Import coqrel.LogicalRelations.
Require Import structures.Posets.
Require Import structures.DCPOs.
Require Import structures.DCPOExtra.
Require Import structures.DCPOSLs.

Local Open Scope em_scope.

Timeout 5 Fail Definition neg_dcpo := (_ : DCPO _).
Timeout 5 Fail Definition neg_dcposl := (_ : DCPOSL _).
Timeout 5 Fail Definition neg_sl := (_ : SemiLattice _).
Timeout 5 Fail Definition neg_poset := (_ : Poset _).
Timeout 5 Fail Definition neg_po := (_ : PartialOrder _).
Timeout 5 Fail Definition neg_pointed := (_ : Pointed _).
Timeout 5 Fail Definition neg_dcomplete := (_ : DirectedComplete (R := _)).
Timeout 5 Fail Definition neg_finitary := (_ : Finitary (R := _)).
Timeout 5 Fail Definition neg_finitary_lce := (_ : Finitary (R := lce (P := _))).
Timeout 5 Fail Definition neg_po_lce := (_ : PartialOrder (lce (P := _))).
Timeout 5 Fail Definition neg_pointed_lce := (_ : Pointed (lce (P := _))).
Timeout 5 Fail Definition neg_em_dcpo := (_ : DCPO (convex_set _)).
Timeout 5 Fail Definition neg_emcomplete := (_ : EMComplete _).
Timeout 5 Fail Definition neg_lift_po := (_ : PartialOrder (_ : relation (lift _ _))).
Timeout 5 Fail Definition neg_precont := (_ : PreContinuous _).
Timeout 5 Fail Definition neg_strict := (_ : Strict _).
Timeout 5 Fail Definition neg_ppo := (_ : PPoset _).
Timeout 5 Fail Definition neg_pointed_pref := (_ : Pointed (pref (P := _))).
Timeout 5 Fail Definition neg_dcomplete_pref := (_ : DirectedComplete (R := pref (P := _))).

Section PROBE_DCPO.
  Context `{DCPO}.
  Timeout 5 Definition probe_lct x y := lce x y /\ x <> y.
  Timeout 5 Definition probe_bot_lce := lce bot bot.
End PROBE_DCPO.

Section PROBE_POINTED.
  Context `{PartialOrder} `{!Pointed R}.
  Timeout 5 Definition probe_emb_bot := ({{ (bot : P) }} = div_set).
  Timeout 5 Definition probe_em_bot : (bot : convex_set P) = div_set := eq_refl.
End PROBE_POINTED.

Section PROBE_FINITARY.
  Context `{DCPO} `{!Finitary (R := lce)}.
  Timeout 5 Definition probe_em_bot_fin : (bot : convex_set P) = div_set := eq_refl.
End PROBE_FINITARY.

Section PROBE_PRECONT.
  Context {A B} `{DCPO A} `{DCPO B} (f : A -> B) `{!ScottContinuous true f}.
  Timeout 5 Definition probe_sc_precont := (_ : PreContinuous f).
  Timeout 5 Definition probe_sc_strict := strict_bot (f := f).
  Timeout 5 Definition probe_sc_mon := (pc_mon (f := f) : Monotonic f (lce ++> lce)).
End PROBE_PRECONT.

Timeout 5 Definition probe_lift_bot := (bot : lift nat eq).
Timeout 5 Definition probe_lift_dcpo_bot_eq : (bot : lift nat eq) = @bot _ (lce (P := lift nat eq)) _ _ := eq_refl.
Timeout 5 Definition probe_lift_ppo : (_ : PPoset (lift nat eq)) = dcpo_ppo (H := lift_dcpo) := eq_refl.
Timeout 5 Definition probe_prod_dcpo := (_ : DCPO (lift nat eq * (nat -> lift nat eq))).

Section PROBE_PPOSET.
  Context `{DCPO}.
  Timeout 5 Definition probe_dcpo_ppo := (_ : PPoset P).
  Timeout 5 Definition probe_pref_dcomplete := (_ : DirectedComplete (R := pref (P := P))).
  Timeout 5 Definition probe_lift_pref_dcomplete := (_ : DirectedComplete (R := pref (P := lift P lce))).
  Timeout 5 Definition probe_pref_bot : (bot : P) = @bot _ (pref (P := P)) _ _ := eq_refl.
End PROBE_PPOSET.
