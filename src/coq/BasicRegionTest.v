Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBoundary_canon_app_testBoundary_top_path : list nat :=
  0 :: 
  1 :: 
  2 :: 
  nil.

Definition testBoundary_canon_app_testBoundary_bottom_path : list nat :=
  0 :: 
  2 :: 
  nil.

Definition testBoundary_canon_app_testBoundary : Boundary :=
  mkBoundary nat 
  testBoundary_canon_app_testBoundary_top_path 
  testBoundary_canon_app_testBoundary_bottom_path.
Definition null : BasicRegion :=
  mkBasicRegion testBoundary_canon_app_testBoundary  isolated top  true false.

