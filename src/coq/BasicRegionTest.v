Require Import List.
Require Import BasicRegion.
Require Import Boundary.
Require Import Region.

Definition testBasicRegion_boundary : Boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
Definition testBasicRegion : BasicRegion :=
  mkBasicRegion testBasicRegion_boundary
  isolated top
  true false.
