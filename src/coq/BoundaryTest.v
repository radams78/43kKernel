Require Import List.
Require Import Boundary.

Definition testBoundary : boundary :=
  mkBoundary nat (0 :: 1 :: 2 :: nil) (0 :: 2 :: nil).
