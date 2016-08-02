Set Implicit Arguments.

Require Import Boundary.
Require Import Region.
Require Import Vector.
Require Import Fin.

Inductive InternalType : PathLength -> PathLength -> Set :=
  none : forall l m, InternalType l m |
  isolated : forall l m, InternalType l m |
  top : forall m, InternalType two m |
  bottom : forall l, InternalType l two |
  universal : InternalType two two |
  bothTopAndBottom : InternalType two two.

Inductive InternalVertex : forall l m : PathLength, InternalType l m -> Set :=
  iso : forall l m, InternalVertex (isolated l m) |
  topV : forall m, InternalVertex (top m) |
  botV : forall l, InternalVertex (bottom l) |
  univ : InternalVertex universal |
  top' : InternalVertex bothTopAndBottom |
  bot' : InternalVertex bothTopAndBottom.

Record BasicRegion : Type := mkBasicRegion {
  Boundary_Vertex : Set;
  top_length : PathLength;
  bottom_length : PathLength;
  _boundary : Boundary Boundary_Vertex top_length bottom_length;
  left_internal_type : InternalType top_length bottom_length;
  right_internal_type : InternalType top_length bottom_length;
  hasLeftEdge : bool;
  hasRightEdge : bool}.

Inductive _Vertex (BV : Set) l m (s t : InternalType l m) : Set :=
  bv : BV -> _Vertex BV s t |
  liv : InternalVertex s -> _Vertex BV s t |
  riv : InternalVertex t -> _Vertex BV s t.

Definition Vertex (R : BasicRegion) : Set :=
  _Vertex (Boundary_Vertex R) (left_internal_type R) (right_internal_type R).

Definition boundary (R : BasicRegion) : Boundary (Vertex R) (top_length R) (bottom_length R) :=
  mkBoundary (top_length R) (bottom_length R) 
    (bv (left_internal_type R) (right_internal_type R) (left (_boundary R)))
    (bv (left_internal_type R) (right_internal_type R) (right (_boundary R)))
    (Vector.map (bv (left_internal_type R) (right_internal_type R)) (topPath (_boundary R)))
    (Vector.map (bv (left_internal_type R) (right_internal_type R)) (bottomPath (_boundary R))).

Inductive _Edge (BV : Set): forall l m (s t : InternalType l m) (B : Boundary BV l m), _Vertex BV s t -> _Vertex BV s t -> Prop :=
  be : forall l m (s t : InternalType l m) B x y, Boundary.Edge B x y -> _Edge B (bv s t x) (bv s t y) |
  left : forall l m (s t : InternalType l m) B x, _Edge B (bv s t (left B)) (liv BV t x). 
  

Definition BasicRegion2Region (R : BasicRegion) : Region (top_length R) (bottom_length R) := 
  mkRegion (top_length R) (bottom_length R) (Vertex R)
  (boundary R).