/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Exponents/InitialExponentTwo.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.CharacterBounds.InitialQuadraticHeckeEstimate

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Goldmakher–Louvel, A quadratic large sieve inequality over number fields (arXiv:1112.1642).
-/

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exponent_initial
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasExponent (Sieve.B1 F c 𝓕) 2 := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := Sieve.initialBound F hF c 𝓕 ε hε
  refine ⟨C + 1, by linarith, ?_⟩
  intro M N hM hN
  refine le_trans (hbound M N hM hN) ?_
  show C * Real.rpow (M * N) ε * (M + Real.rpow N 2) ≤
    (C + 1) * Real.rpow (M * N) ε * (M + Real.rpow N 2)
  have hX : (0 : ℝ) ≤ Real.rpow (M * N) ε := Real.rpow_nonneg (by positivity) ε
  have hY : (0 : ℝ) ≤ M + Real.rpow N 2 := by
    have : (0 : ℝ) ≤ Real.rpow N 2 := Real.rpow_nonneg (by linarith) 2
    linarith
  apply mul_le_mul_of_nonneg_right _ hY
  exact mul_le_mul_of_nonneg_right (by linarith) hX

end DedekindZetaZeroFree.LargeSieve
