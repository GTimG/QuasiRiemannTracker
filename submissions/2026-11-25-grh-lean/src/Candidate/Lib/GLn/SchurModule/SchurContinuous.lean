import Candidate.Lib.GLn.Branching.Branching

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Continuity of the Schur matrix in its argument. -/

/-- Over a topological commutative ring R, the map sending a tuple g of square matrices to its
Schur matrix S_κ(g) is continuous. -/
@[fun_prop] lemma continuous_schur {Φ n κ R} [Fintype Φ] [∀ τ, Fintype (n τ)] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Continuous (@schur Φ R _ _ n n _ _ κ) :=
  .congr (by simp [Matrix.map, MvPolynomial.eval_eq]; fun_prop) fun g ↦
  funext (PolyRep.genericMatrixAt_map_evalMat g) ▸ (schur_map .refl ..).symm
