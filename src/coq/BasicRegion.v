Require Import Boundary.

Inductive InternalType : Set :=
  none : InternalType |
  isolated : InternalType |
  top : InternalType |
  bottom : InternalType |
  universal : InternalType |
  bothTopAndBottom : InternalType.

Definition numVerticesByType (t : InternalType) : nat :=
  match t with
    none => 0 |
    isolated => 1 |
    top => 1 |
    bottom => 1 |
    universal => 1 |
    bothTopAndBottom => 2 end.

Record BasicRegion : Type := mkBasicRegion
  {boundary : Boundary;
  leftInternalType : InternalType;
  rightInternalType : InternalType;
  hasLeftEdge : bool;
  hasRightEdge : bool}.  