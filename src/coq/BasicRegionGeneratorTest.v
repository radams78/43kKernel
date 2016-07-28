Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegionGenerator : list BasicRegion :=
 mkBasicRegion (mkBoundary nat
  (nil) 
 (nil)) none none false false :: mkBasicRegion (mkBoundary nat
  (nil) 
 (nil)) none isolated false false :: mkBasicRegion (mkBoundary nat
  (nil) 
 (nil)) isolated none false false :: mkBasicRegion (mkBoundary nat
  (nil) 
 (nil)) isolated isolated false false :: nil.

