/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Poisson.RadialFourier

/-!
# Inverse.Poisson.Separation — separation of the Poisson kernel and of the profile

* `radial_kernel_separation_pointwise`: the second-Poisson kernel `Ŵ = paperRadialFourier W` at
  `R·exp(∑ a_j y_j)` on bounded windows is `∫ ∏ (V_j(y_j) logPhase t (a_j y_j)) b_R(t) dt` with
  POINTWISE decay `(1+R)^A (1+|t|)^J |b_R(t)| ≤ C`, uniformly in `R > 0`. (The baseline
  `paperRadialFourier_log_separation_schwartz` gives the integrated moment; the pointwise form is
  needed because `R` depends on the labels of a fibre.) This gives both the main term and the
  rapid tail of the second Poisson step.
* `exists_profile_bump`: a real smooth bump `Φ = 1` on `[lo, hi]`, supported in `[lo/2, 2 hi]`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open MeasureTheory OAI
open scoped FourierTransform SchwartzMap ContDiff

theorem one_add_pow_le_two_pow (x : ℝ) (hx : 0 ≤ x) (J : ℕ) :
    (1 + x) ^ J ≤ 2 ^ J * (1 + x ^ J) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ J ≤ 2 ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
      _ ≤ 2 ^ J * (1 + x ^ J) :=
        le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hx J; linarith)
  · calc (1 + x) ^ J ≤ (2 * x) ^ J := pow_le_pow_left₀ (by linarith) (by linarith) J
      _ = 2 ^ J * x ^ J := mul_pow _ _ _
      _ ≤ 2 ^ J * (1 + x ^ J) := by gcongr; linarith

/-- Pointwise Fourier decay from the seminorm sources (`uniform_fourier_seminorm_transfer` at
`k = 0` and `k = J`). -/
theorem fourier_pointwise_of_source (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) (t : ℝ) :
    S * ((1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      2 ^ J * ((2 : ℝ) ^ 0 * (((0 : ℕ) : ℝ) + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ J * (J + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  have h0 := FourierBridge.uniform_fourier_seminorm_transfer g 0 S C hS hC
    (fun i hi => hsource i (by omega))
  have hJ := FourierBridge.uniform_fourier_seminorm_transfer g J S C hS hC hsource
  have p0 : ‖(𝓕 g) t‖ ≤ (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) := by
    have := SchwartzMap.le_seminorm ℝ 0 0 (𝓕 g) t
    simpa [norm_iteratedFDeriv_zero] using this
  have pJ : ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤ (SchwartzMap.seminorm ℝ J 0) (𝓕 g) := by
    have := SchwartzMap.le_seminorm ℝ J 0 (𝓕 g) t
    simpa [norm_iteratedFDeriv_zero] using this
  have hpow := one_add_pow_le_two_pow ‖t‖ (norm_nonneg t) J
  have hn := norm_nonneg ((𝓕 g) t)
  calc S * ((1 + ‖t‖) ^ J * ‖(𝓕 g) t‖)
      ≤ S * (2 ^ J * (1 + ‖t‖ ^ J) * ‖(𝓕 g) t‖) := by gcongr
    _ = 2 ^ J * (S * ‖(𝓕 g) t‖ + S * (‖t‖ ^ J * ‖(𝓕 g) t‖)) := by ring
    _ ≤ 2 ^ J * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          S * (SchwartzMap.seminorm ℝ J 0) (𝓕 g)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h0 hJ) (by positivity)

/-- Pointwise uniform separation of the radial Poisson kernel on bounded windows. -/
theorem radial_kernel_separation_pointwise
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            EisensteinSchwartzPoisson.paperRadialFourier W
              (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) * FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (∀ t : ℝ, (1 + R) ^ A * ((1 + ‖t‖) ^ J * ‖b t‖) ≤ C) := by
  classical
  let F : ℝ → ℂ := EisensteinSchwartzPoisson.paperRadialFourier W
  have hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0) :=
    EisensteinSchwartzPoisson.paperRadialFourier_contDiffOn W
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V', CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  obtain ⟨CF, hCF, hEuler⟩ := EisensteinSchwartzPoisson.paperRadialFourier_euler_bound W A K
  let C0 : ℝ := LocalLogFourier.momentConstant K Lwin CW CF
  have hC0 : 0 ≤ C0 := LocalLogFourier.momentConstant_nonneg K Lwin CW CF hL hCW hCF
  let Vv : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  let B : ℝ := 2 ^ J * ((2 : ℝ) ^ 0 * (((0 : ℕ) : ℝ) + 1) * Vv * C0 + (2 : ℝ) ^ J * (J + 1) * Vv * C0)
  have hVv : 0 ≤ Vv := by dsimp [Vv]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B / m ^ A, by positivity, ?_⟩
  intro R hR
  let g : 𝓢(ℝ, ℂ) := LocalLogFourier.positiveLogProfile V' F R hVc hVs hFpos hR
  refine ⟨𝓕 g, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, V j (y j)) ≠ 0 → V' (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active V V' a y M hVwindow (by simpa [T] using hVone)
    exact LocalLogFourier.coupled_positive_log_separation V F V' R a y hVc hVs hFpos hR hactive
  · intro t
    have hwindow' : ∀ s, (∃ i ≤ K, ‖iteratedFDeriv ℝ i V' s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource : ∀ i ≤ J,
        (m ^ A * (1 + R) ^ A) * ((SchwartzMap.seminorm ℝ 0 i) g +
          (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C0 := by
      intro i hi
      exact LocalLogFourier.positive_log_source_pair V' F R m Lwin CW CF C0 A K i
        hVc hVs hFpos hR hm hm1 hL hCW hCF hi hVderiv hwindow' hEuler
        (fun j hj => LocalLogFourier.momentConstant_dominates K j Lwin CW CF hL hCW hCF hj)
    have hp := fourier_pointwise_of_source g J (m ^ A * (1 + R) ^ A) C0 (by positivity) hC0
      hsource t
    have hmA : 0 < m ^ A := pow_pos hm _
    rw [le_div_iff₀ hmA]
    calc (1 + R) ^ A * ((1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) * m ^ A
        = (m ^ A * (1 + R) ^ A) * ((1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) := by ring
      _ ≤ B := by simpa [B, Vv] using hp

/-- A real smooth bump equal to `1` on `[lo, hi]` and supported in `[lo/2, 2 hi]`. -/
theorem exists_profile_bump (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) :
    ∃ Φ : ℝ → ℂ, ContDiff ℝ ∞ Φ ∧ Function.support Φ ⊆ Set.Icc (lo / 2) (2 * hi) ∧
      (∀ x ∈ Set.Icc lo hi, Φ x = 1) ∧ (∀ x, ‖Φ x‖ ≤ 1) ∧ (∀ x, star (Φ x) = Φ x) := by
  let c : ℝ := (lo + hi) / 2
  let bump : ContDiffBump c :=
    ⟨(hi - lo) / 2 + lo / 4, (hi - lo) / 2 + lo / 2, by linarith, by linarith⟩
  refine ⟨fun x => ((bump x : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp bump.contDiff
  · intro x hx
    have hx' : bump x ≠ 0 := by
      intro h0; exact hx (by simp [h0])
    have hmem : x ∈ Function.support bump := hx'
    rw [bump.support_eq, Metric.mem_ball, Real.dist_eq] at hmem
    have h := abs_lt.mp hmem
    simp only [bump, c] at h
    constructor <;> linarith [h.1, h.2]
  · intro x hx
    have hmem : x ∈ Metric.closedBall c ((hi - lo) / 2 + lo / 4) := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      simp only [c]
      constructor <;> linarith [hx.1, hx.2]
    have h1 := bump.one_of_mem_closedBall hmem
    simp [h1]
  · intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
    exact bump.le_one
  · intro x
    simp

end
end Qrh.MarkedAnchor.Inverse.Poisson
