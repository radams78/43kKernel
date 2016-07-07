Require Import Boundary.

Inductive Connection : Set :=
  left : Connection |
  right : Connection |
  both : Connection.

Record Region : Type := mkRegion
  {boundary : Boundary;
   Internal : Set;
   connect  : Internal -> Connection;
   edge     : (Internal + Points boundary) ->
              (Internal + Points boundary) ->
              Prop}.