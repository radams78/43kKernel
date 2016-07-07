(* A boundary consists of a set of points,
and two paths out of that set. *)

Require Import List.

Record Boundary : Type := mkBoundary
{Points : Set;
 topPath : list Points;
 bottomPath : list Points}.