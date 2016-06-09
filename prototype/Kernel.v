(* A 43k Kernel for Planar Dominating Set *)

Require Import Region.
Require Import SMRegion.

Axiom max_size_lm : forall R : SMRegion, size (decode R) <= 12.

Theorem max_size : forall B (R : Region B), signature_minimal R -> size R <= 12.
Proof.
intros.
rewrite <- code_size with (p := H).
apply max_size_lm.
Qed.