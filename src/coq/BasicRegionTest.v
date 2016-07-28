Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegion : BasicRegion :=
 mkBasicRegion (mkBoundary nat
  (nil) 
 (nil)) isolated top true false.

