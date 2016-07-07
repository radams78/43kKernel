Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegionGenerator_region0_boundary : Boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
Definition testBasicRegionGenerator_region0 : BasicRegion :=
  mkBasicRegion testBasicRegionGenerator_region0_boundary
  none none
  false false.

Definition testBasicRegionGenerator_region1_boundary : Boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
Definition testBasicRegionGenerator_region1 : BasicRegion :=
  mkBasicRegion testBasicRegionGenerator_region1_boundary
  none isolated
  false false.

Definition testBasicRegionGenerator_region2_boundary : Boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
Definition testBasicRegionGenerator_region2 : BasicRegion :=
  mkBasicRegion testBasicRegionGenerator_region2_boundary
  isolated none
  false false.

Definition testBasicRegionGenerator_region3_boundary : Boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
Definition testBasicRegionGenerator_region3 : BasicRegion :=
  mkBasicRegion testBasicRegionGenerator_region3_boundary
  isolated isolated
  false false.

Definition testBasicRegionGenerator : List BasicRegion := 
 [
  testBasicRegionGenerator_region0 ;
  testBasicRegionGenerator_region1 ;
  testBasicRegionGenerator_region2 ;
  testBasicRegionGenerator_region3 ;
].
