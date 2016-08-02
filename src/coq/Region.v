Require Import Boundary.

Record Region (l m : PathLength) : Type := mkRegion
  {Vertex : Set;
   boundary : Boundary Vertex l m;
   Edge : Vertex -> Vertex -> Prop}. (* Edges apart from those on the two paths of the boundary *)