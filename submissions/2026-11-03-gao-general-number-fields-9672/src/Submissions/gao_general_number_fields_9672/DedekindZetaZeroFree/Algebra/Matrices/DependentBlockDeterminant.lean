/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/Matrices/DependentBlockDeterminant.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/LinearAlgebra/Matrix/Block.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace Matrix

@[simp]
public theorem det_blockDiagonal' {o R : Type*} {m : o → Type*} [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [CommRing R] (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by

  let _ : LinearOrder o := Equiv.linearOrder (Fintype.equivFin o)
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← det_reindex_self (Equiv.sigmaSubtype i)]
  congr 1
  ext j k

  simp [toSquareBlock_def, Equiv.sigmaSubtype]

end Matrix
