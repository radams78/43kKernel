(* A boundary consists of a set of points,
and two paths out of that set. *)

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

Inductive Edge (Vertex : Set) : forall l m, Boundary Vertex l m -> Vertex -> Vertex -> Prop :=
  top0 : forall m (B : Boundary Vertex zero m), Edge B (left B) (right B) |
  top10 : forall m (B : Boundary Vertex one m), Edge B (left B) (nth (topPath B) F1) |
  top11 : forall m (B : Boundary Vertex one m), Edge B (nth (topPath B) F1) (right B) |
  top20 : forall m (B : Boundary Vertex two m), Edge B (left B) (nth (topPath B) F1) |
  top21 : forall m (B : Boundary Vertex two m), Edge B (nth (topPath B) F1) (nth (topPath B) (FS F1)) |
  top22 : forall m (B : Boundary Vertex two m), Edge B (nth (topPath B) (FS F1)) (right B) |
  bottom0 : forall l (B : Boundary Vertex l zero), Edge B (left B) (right B) |
  bottom10 : forall l (B : Boundary Vertex l one), Edge B (left B) (nth (bottomPath B) F1) |
  bottom11 : forall l (B : Boundary Vertex l one), Edge B (nth (bottomPath B) F1) (right B) |
  bottom20 : forall l (B : Boundary Vertex l two), Edge B (left B) (nth (bottomPath B) F1) |
  bottom21 : forall l (B : Boundary Vertex l two), Edge B (nth (bottomPath B) F1) (nth (bottomPath B) (FS F1)) |
  bottom22 : forall l (B : Boundary Vertex l two), Edge B (nth (bottomPath B) (FS F1)) (right B).
(* TODO Refactor *)