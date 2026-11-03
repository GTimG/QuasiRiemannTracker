/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/Integration/UniformIntegralDetection.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory
namespace DedekindZetaZeroFree.KPLiteralPeriod

theorem nonzero_integral_detected_by_uniform_approximation
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hfinite : μ Set.univ ≠ ⊤) (hmass : 0 < μ.real Set.univ)
    (u χ : X → ℂ) (hχ : ∀ x, ‖χ x‖ = 1)
    (hu : Integrable (fun x => u x * χ x) μ)
    (hne : (∫ x, u x * χ x ∂μ) ≠ 0)
    {ι : Type*} (v : ι → X → ℂ)
    (hv : ∀ i, Integrable (fun x => v i x * χ x) μ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ i, ∀ x, ‖v i x - u x‖ < ε) :
    ∃ i, (∫ x, v i x * χ x ∂μ) ≠ 0 := by
  haveI : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hfinite⟩
  set I : ℂ := ∫ x, u x * χ x ∂μ with hI
  have hIpos : 0 < ‖I‖ := norm_pos_iff.mpr hne
  set ε : ℝ := ‖I‖ / (2 * μ.real Set.univ) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact div_pos hIpos (by positivity)
  obtain ⟨i, hi⟩ := happrox ε hεpos
  refine ⟨i, ?_⟩
  set J : ℂ := ∫ x, v i x * χ x ∂μ with hJ
  have hsub : J - I = ∫ x, (v i x - u x) * χ x ∂μ := by
    rw [hJ, hI, ← integral_sub (hv i) hu]
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  have hle : ∀ x, ‖(v i x - u x) * χ x‖ ≤ ε := by
    intro x
    rw [norm_mul, hχ x, mul_one]
    exact le_of_lt (hi x)
  have hbound : ‖J - I‖ ≤ ε * μ.real Set.univ := by
    rw [hsub]
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hle)
  have hεm : ε * μ.real Set.univ = ‖I‖ / 2 := by
    rw [hεdef]
    field_simp
  rw [hεm] at hbound
  intro hzero
  have hEq : ‖J - I‖ = ‖I‖ := by rw [hzero, zero_sub, norm_neg]
  rw [hEq] at hbound
  linarith

end DedekindZetaZeroFree.KPLiteralPeriod

end
