(* A boundary consists of a set of points,
and two paths out of that set. *)

Require Import List.

Record boundary : Type := mkBoundary
{points : Set;
 topPath : list points;
 bottomPath : list points}.