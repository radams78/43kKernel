Require Import Vector.
Require Import Boundary.

Definition testBoundary : Boundary nat zero zero :=
 mkBoundary zero zero (0) (2) ((nil nat)) 
 ((nil nat)).

