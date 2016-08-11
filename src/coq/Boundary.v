(* A boundary consists of a set of points, and two paths out of that set. *)

Set Implicit Arguments.

Require Import Vector.
Require Import Fin.

Inductive PathLength : Set :=
  zero : PathLength |
  one : PathLength |
  two : PathLength.

Definition PathLength2nat (l : PathLength) : nat := match l with
  zero => 0 |
  one => 1 |
  two => 2 end.

Coercion PathLength2nat : PathLength >-> nat.

Record Boundary (Vertex : Set) (l m : PathLength) : Set := mkBoundary
  {left : Vertex;
  right : Vertex;
  topPath : Vector.t Vertex l;
  bottomPath : Vector.t Vertex m}.

Inductive _Edge (Vertex : Set) (left right : Vertex) : forall n, Vector.t Vertex n -> Vertex -> Vertex -> Prop :=
  edge0 : forall (P : Vector.t Vertex 0), _Edge left right P left right |
  edge10 : forall (P : Vector.t Vertex 1), _Edge left right P left (nth P F1) |
  edge11 : forall (P : Vector.t Vertex 1), _Edge left right P (nth P F1) right |
  edge20 : forall (P : Vector.t Vertex 2), _Edge left right P left (nth P F1) |
  edge21 : forall (P : Vector.t Vertex 2), _Edge left right P (nth P F1) (nth P (FS F1)) |
  edge22 : forall (P : Vector.t Vertex 2), _Edge left right P (nth P (FS F1)) right.

Inductive Edge (Vertex : Set) (l m : PathLength) (B : Boundary Vertex l m) : Vertex -> Vertex -> Prop :=
  top : forall x y, _Edge (left B) (right B) (topPath B) x y -> Edge B x y |
  bottom : forall x y, _Edge (left B) (right B) (bottomPath B) x y -> Edge B x y.
(* TODO Refactor *)