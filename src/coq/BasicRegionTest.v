Require Import BasicRegion.
Require Import Boundary.
Require Import Region.
Require Import Vector.
Import VectorNotations.

Definition testBasicRegion : BasicRegion :=
 mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (isolated two zero) (top zero) true false.

