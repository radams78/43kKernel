Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegionGenerator : list BasicRegion :=
 mkBasicRegion ((mkBoundary nat
  (0 :: 1 :: 2 :: nil) 
  (0 :: 2 :: nil))) none none false false :: mkBasicRegion ((mkBoundary nat
  (0 :: 1 :: 2 :: nil) 
  (0 :: 2 :: nil))) none isolated false false :: mkBasicRegion ((mkBoundary nat
  (0 :: 1 :: 2 :: nil) 
  (0 :: 2 :: nil))) isolated none false false :: mkBasicRegion ((mkBoundary nat
  (0 :: 1 :: 2 :: nil) 
  (0 :: 2 :: nil))) isolated isolated false false :: nil.

