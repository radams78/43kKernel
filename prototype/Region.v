Set Implicit Arguments.

Inductive Noose : Set :=
  one : Noose |
  two : Noose |
  three : Noose.

Definition points (N : Noose) : Set :=
  match N with
    one => Empty_set | two => unit | three => bool end.

Definition Boundary : Set := prod Noose Noose.

Inductive delta : Boundary -> Set :=
  left : forall B, delta B |
  right : forall B, delta B |
  top : forall i j, points i -> delta (i , j) |
  bottom : forall i j, points j -> delta (i , j).

Axiom unionB : Boundary -> Boundary -> Boundary.

Axiom Region : Boundary -> Set.

Axiom unionR : forall B B', Region B -> Region B' -> Region (unionB B B').

Inductive Sig_Output : Set := X : Sig_Output | S : Sig_Output | Neither : Sig_Output.

Definition Valid_Inputs (B : Boundary) : Set := delta B -> Sig_Output.
  
Axiom signature : forall B, Region B -> Valid_Inputs B -> nat.

Definition signature_equivalent B (R1 R2 : Region B) : Prop :=
  forall X, signature R1 X = signature R2 X.
Notation "R1 =sig R2" := (signature_equivalent R1 R2) (at level 50).

Axiom basic : forall B, Region B -> Prop.

Axiom size : forall B, Region B -> nat.

Definition signature_minimal B (R : Region B) := forall R', R =sig R' -> size R <= size R'.
