/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Comparison/ContourExponentMargins.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

namespace DedekindZetaZeroFree

theorem comparisonE_shifted_z_margin :
    comparisonE comparisonSigma₁ (19 / 20) comparisonZeta₁ ≤ 7 / 15 - 1 / 2000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonZeta₁, comparisonDelta]
  norm_num

theorem comparisonE_w_residue_margin :
    comparisonE comparisonSigma₁ 1 (4 / 25) ≤ 7 / 15 - 1 / 2000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_first_dyadic_margin :
    comparisonE comparisonSigma₁ (3 / 1000) (2 / 5) +
      (9 / 100) * (11 / 10) ≤ 7 / 15 - 1 / 1000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_second_dyadic_margin :
    comparisonE comparisonSigma₁ (3 / 1000) (2 / 5) +
      (10001 / 100000) * (3 / 5) ≤ 7 / 15 - 1 / 1000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀, comparisonSigma₁,
    comparisonDelta]
  norm_num

theorem comparisonE_left_contour_margin :
    comparisonE (499 / 500) (3 / 1000) (2 / 5) +
      (10001 / 100000) * (11 / 10) = 7 / 15 - 377 / 300000 := by
  simp only [comparisonE, comparisonA, comparisonB, comparisonH₀]
  norm_num

end DedekindZetaZeroFree
