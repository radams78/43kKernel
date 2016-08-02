Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegion : BasicRegion :=
 mkBasicRegion (mkBoundary zero zero (0) (2) ((nil nat)) 
 ((nil nat))) isolated top true false.

