/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/Fields/NaturalInverseNonvanishing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector

theorem one_add_nat_inv_ne_zero (n : ℕ) : (1 + (n : ℂ)⁻¹) ≠ 0 := by
  have hcast : (1 + (n : ℂ)⁻¹) = ((1 + (n : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    simp
  rw [hcast, Complex.ofReal_ne_zero]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    norm_num
  · have hpos : (0 : ℝ) < n := by exact_mod_cast h
    have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hpos
    linarith

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.GoodSphericalVector
