Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegion : BasicRegion :=
 mkBasicRegion (mkBoundary nat
  (0 :: 1 :: 2 :: nil) 
 (0 :: 2 :: nil)) isolated top true false.

