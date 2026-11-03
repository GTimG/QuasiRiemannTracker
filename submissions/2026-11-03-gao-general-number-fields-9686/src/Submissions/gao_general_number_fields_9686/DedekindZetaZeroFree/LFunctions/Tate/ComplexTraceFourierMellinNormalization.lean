/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Tate/ComplexTraceFourierMellinNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory
open scoped ContDiff InnerProductSpace

def complexTracePairing (x y : ℂ) : ℝ := 2 * (x * y).re

def complexTraceFourier (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  2 * ∫ x : ℂ, f x * Complex.exp (((-4 * Real.pi * (x * y).re : ℝ) : ℂ) * Complex.I)

def complexNormMellinIntegrand (f : ℂ → ℂ) (s : ℝ) (x : ℂ) : ℂ :=
  if x = 0 then 0 else f x * ((‖x‖ ^ 2) ^ (s - 1) : ℝ)

def complexNormMellin (f : ℂ → ℂ) (s : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ x : ℂ, complexNormMellinIntegrand f s x

def IsComplexAnnular (f : ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      tsupport f ⊆ {x : ℂ | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

theorem complexTraceFourier_eq_fourier (f : ℂ → ℂ) (y : ℂ) :
    complexTraceFourier f y =
      2 * FourierTransform.fourier f (2 * (starRingEnd ℂ) y) := by
  rw [complexTraceFourier, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards with v

  have hinner : ⟪v, 2 * (starRingEnd ℂ) y⟫_ℝ = 2 * (v * y).re := by
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    norm_num
    ring
  rw [hinner]
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

end
end DedekindZetaZeroFree
