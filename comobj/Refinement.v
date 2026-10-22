Require Import structures.DCPOSLs.

Require Import comobj.SilLTS.
Require Import comobj.VisLTS.
Require Import comobj.Traces.

Definition refines {E Sα Sβ} 
  `{DCPO Sα} `{!Finitary (R := lce (P := Sα))} 
  `{DCPO Sβ} `{!Finitary (R := lce (P := Sβ))} 
  (α : SilLTS E Sα) (β : SilLTS E Sβ) := traces (louden α) ⊆ traces (louden β).