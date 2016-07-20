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

Definition testBasicRegionGenerator_br0 : BasicRegion :=
  mkBasicRegion testBoundary_canon_app_testBoundary  none none  false false.
Definition testBasicRegionGenerator_br1 : BasicRegion :=
  mkBasicRegion testBoundary_canon_app_testBoundary  none isolated  false false.
Definition testBasicRegionGenerator_br2 : BasicRegion :=
  mkBasicRegion testBoundary_canon_app_testBoundary  isolated none  false false.
Definition testBasicRegionGenerator_br3 : BasicRegion :=
  mkBasicRegion testBoundary_canon_app_testBoundary  isolated isolated  false false.
Definition testBasicRegionGenerator : list BasicRegion :=
  testBasicRegionGenerator_br0 :: 
  testBasicRegionGenerator_br1 :: 
  testBasicRegionGenerator_br2 :: 
  testBasicRegionGenerator_br3 :: 
  nil.


