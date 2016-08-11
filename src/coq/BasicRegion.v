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
  left : forall l m (s t : InternalType l m) B x, _Edge B (bv s t (left B)) (liv BV t x) |
  right : forall l m (s t : InternalType l m) B y, _Edge B (bv s t (right B)) (riv BV s y) |
  ltopV : forall m t B, _Edge B (liv BV t (topV m)) (bv _ t (nth (topPath B) F1)) |
  lbotV : forall l t B, _Edge B (liv BV t (botV l)) (bv _ t (nth (bottomPath B) F1)) |
  lunivtop : forall t B, _Edge B (liv BV t univ) (bv _ t (nth (topPath B) F1)) |
  lunivbot : forall t B, _Edge B (liv BV t univ) (bv _ t (nth (bottomPath B) F1)) |
  ltop' : forall t B, _Edge B (liv BV t top') (bv _ t (nth (topPath B) F1)) |
  lbot' : forall t B, _Edge B (liv BV t bot') (bv _ t (nth (bottomPath B) F1)) |
  rtopV : forall m s B, _Edge B (riv BV s (topV m)) (bv s _ (nth (topPath B) (FS F1))) |
  rbotV : forall l s B, _Edge B (riv BV s (botV l)) (bv s _ (nth (bottomPath B) (FS F1))) |
  runivtop : forall s B, _Edge B (riv BV s univ) (bv s _ (nth (topPath B) (FS F1))) |
  runivbot : forall s B, _Edge B (riv BV s univ) (bv s _ (nth (bottomPath B) (FS F1))) |
  rtop' : forall s B, _Edge B (riv BV s top') (bv s _ (nth (topPath B) (FS F1))) |
  rbot' : forall s B, _Edge B (riv BV s bot') (bv s _ (nth (bottomPath B) (FS F1))).

Definition Edge (R : BasicRegion) : Vertex R -> Vertex R -> Prop :=
  @_Edge (Boundary_Vertex R) (top_length R) (bottom_length R) (left_internal_type R) (right_internal_type R) (_boundary R).

Definition BasicRegion2Region (R : BasicRegion) : Region (top_length R) (bottom_length R) := 
  mkRegion (top_length R) (bottom_length R) (Vertex R)
  (boundary R) (@Edge R).