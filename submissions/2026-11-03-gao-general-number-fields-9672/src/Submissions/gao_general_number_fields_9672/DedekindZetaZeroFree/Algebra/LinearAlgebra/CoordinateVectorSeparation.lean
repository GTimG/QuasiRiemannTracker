/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/LinearAlgebra/CoordinateVectorSeparation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Algebra.Matrices.DependentBlockDeterminant

/-
Vendored from https://github.com/TauCetiProject/TauCeti, commit
66f3330c1cbabafd0f5b3ea4a646c43e23105ee2; source `TauCeti/LinearAlgebra/Pi.lean`.
Original Apache-2.0 copyright/author notice retained; see vendor LICENSE.
-/

@[expose] public section

namespace LinearMap

public theorem toMatrix_piMap {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] {κ κ' : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Finite (κ' i)]
    (b : ∀ i, Module.Basis (κ i) R (M i)) (c : ∀ i, Module.Basis (κ' i) R (N i))
    (f : ∀ i, M i →ₗ[R] N i) :
    toMatrix (Pi.basis b) (Pi.basis c) (piMap f) =
      Matrix.blockDiagonal' fun i ↦ toMatrix (b i) (c i) (f i) := by
  ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
  simp only [toMatrix_apply', Pi.basis_apply, Matrix.blockDiagonal'_apply]
  split_ifs with h
  · subst h
    simp
  · simp [h]

@[simp]
public theorem det_piMap {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    (piMap f).det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  rw [← det_toMatrix (Pi.basis b), toMatrix_piMap b b, Matrix.det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ det_toMatrix (b i) (f i)

end LinearMap
