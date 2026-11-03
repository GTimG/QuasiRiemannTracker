/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighSignalIdentity.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

def perturbedBoundary : ℝ := boundary

def perturbedContinuationMargin (β ω σ : ℝ) : ℝ :=
  min (β - perturbedBoundary - ω) σ

theorem perturbedContinuationMargin_pos {β ω σ : ℝ}
    (hω : ω < β - perturbedBoundary) (hσ : 0 < σ) :
    0 < perturbedContinuationMargin β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

theorem perturbed_continuation_boundary_gt {β ω σ : ℝ}
    (hω : 0 < ω) :
    perturbedBoundary < β - perturbedContinuationMargin β ω σ := by
  have h := min_le_left (β - perturbedBoundary - ω) σ
  dsimp [perturbedContinuationMargin]
  linarith

theorem nonzero_of_perturbed_probe_bounds
    (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (β ω σ c : ℝ) (hβ : β ≤ 1)
    (hω0 : 0 < ω) (hω : ω < β - perturbedBoundary) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | perturbedBoundary < s.re})
    (hb : ∀ s : ℂ, perturbedBoundary < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (perturbedBoundary + c + ω)))
    (herror : (fun x => J x - signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    {ρ : ℂ} (hρ : β - perturbedContinuationMargin β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - perturbedContinuationMargin β ω σ
  have hmargin := perturbedContinuationMargin_pos hω hσ
  have hboundary : perturbedBoundary < a :=
    perturbed_continuation_boundary_gt hω0
  have ha2 : a < 2 := by dsimp [a]; linarith
  have hH7 : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re} :=
    hH.mono (by
      intro s hs
      change 7 / 8 < s.re at hs
      change perturbedBoundary < s.re
      dsimp [perturbedBoundary, boundary]
      linarith)
  have hb7 : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2 := by
    intro s hs
    apply hb
    dsimp [perturbedBoundary, boundary]
    linarith
  have hHd := hH7.differentiableOn
  have hexp : max (perturbedBoundary + c + ω) (β + c - σ) = a + c := by
    dsimp [a, perturbedContinuationMargin]
    rcases le_total (β - perturbedBoundary - ω) σ with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
  have htop : signal χ H c =O[atTop] (fun x : ℝ => x ^ (a + c)) := by
    simpa only [hexp] using
      common_signal_bound J (signal χ H c)
        (perturbedBoundary + c + ω) (β + c - σ) hJ herror
  have hHan : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => hboundary.trans hs)
  apply nonzero_of_regularized_signal a 1 c (LFunction χ)
    (regularL χ) (targetRegularizer χ) (gaussianMultiplier H)
    (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (gaussianMultiplier_analytic hHan)
    (signal_locallyIntegrable χ H hHd hb7 c) htop
    (signal_rapidDecayAtZero χ H hHd hb7 c)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro h; norm_num [h] at hs1
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1),
      signalMellin_eq_amplitude χ H hHd hb7 c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · exact hρ
  · apply regularL_eq χ _ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    have hpos : 0 < a := by
      dsimp [perturbedBoundary, boundary] at hboundary
      linarith
    linarith
  · exact targetRegularizer_ne_zero χ hpole
  · exact gaussianMultiplier_ne_zero (hb ρ (hboundary.trans hρ))

end SevenEighths.HeckeSignal

end

end OAI
