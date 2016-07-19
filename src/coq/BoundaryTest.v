Require Import List.
Require Import Boundary.

Definition testBoundary_top_path : list nat :=
  0 :: 
  1 :: 
  2 :: 
  nil.

Definition testBoundary_bottom_path : list nat :=
  0 :: 
  2 :: 
  nil.

Definition testBoundary : Boundary :=
  mkBoundary nat 
  testBoundary_top_path 
  testBoundary_bottom_path.

