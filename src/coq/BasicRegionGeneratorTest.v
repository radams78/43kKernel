Require Import List.
Require Import Vector.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.
Import VectorNotations.

Definition testBasicRegionGenerator : list BasicRegion :=
 List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (top zero) (top zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (top zero) (isolated two zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (top zero) (none two zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (isolated two zero) (top zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (isolated two zero) (isolated two zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (isolated two zero) (none two zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (none two zero) (top zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (none two zero) (isolated two zero) false false) (List.cons (mkBasicRegion (mkBoundary two zero 0 3 (1 :: 2 :: (nil nat)) 
 ((nil nat))) (none two zero) (none two zero) false false) (List.nil))))))))).

