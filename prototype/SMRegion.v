Set Implicit Arguments.

Require Import Region.

Definition BasicSMRegion : Set := 
  { P : { B : Boundary & Region B } | 
  match P with (existT _ R) => signature_minimal R /\ basic R end }.

Definition boundaryBSM (B : BasicSMRegion) : Boundary :=
  match B with (exist (existT B _) _) => B end.

Inductive SMRegion : Set :=
  basicSMR : BasicSMRegion -> SMRegion |
  unionSMR : SMRegion -> BasicSMRegion -> SMRegion.

Axiom code : forall B (R : Region B), signature_minimal R -> SMRegion.

Fixpoint boundary (R : SMRegion) : Boundary :=
  match R with
    basicSMR B => boundaryBSM B |
    unionSMR R B => unionB (boundary R) (boundaryBSM B)
    end.

Program Fixpoint decode (R : SMRegion) : Region (boundary R) :=
  match R with
    basicSMR (exist (existT _ R) _) => R |
    unionSMR R (exist (existT _ R') _) => unionR (decode R) R'
    end.

Axiom code_size : forall B R p, size (decode (@code B R p)) = size R.
