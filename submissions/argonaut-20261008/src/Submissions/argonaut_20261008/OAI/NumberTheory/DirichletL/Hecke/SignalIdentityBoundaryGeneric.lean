import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.ContinuationBoundaryGeneric
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.SignalIdentity

namespace OAI

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical

namespace SevenEighths.HeckeSignal

open HeckeFamily Continuation

theorem analyticOnNhd_seven_eighths_of_boundary {b0 : ℝ} {H : ℂ → ℂ}
    (hb0 : b0 ≤ 7 / 8)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re}) :
    AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re} :=
  hH.mono (fun s hs => lt_of_le_of_lt hb0 hs)

theorem contract_seven_eighths_of_boundary {b0 : ℝ} {H : ℂ → ℂ}
    (hb0 : b0 ≤ 7 / 8)
    (hb : ∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) :
    ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ) := by
  intro s hs
  exact hb s (lt_of_le_of_lt hb0 hs)

theorem signalMellin_eq_amplitude_boundary (b0 : ℝ) (hb0 : b0 ≤ 7 / 8)
    (χ : Character) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re})
    (hb : ∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x ^ (a + c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal χ H c) c s = amplitude χ H s := by
  have hH' := analyticOnNhd_seven_eighths_of_boundary hb0 hH
  have hb' := contract_seven_eighths_of_boundary hb0 hb
  exact signalMellin_eq_amplitude χ H hH'.differentiableOn hb' c a ha htop hs

theorem poleRemoved_mul_signalMellin_boundary (b0 : ℝ) (hb0 : b0 ≤ 7 / 8)
    (χ : Character) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re})
    (hb : ∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (c a : ℝ) (ha : a < 2)
    (htop : signal χ H c =O[atTop] (fun x : ℝ => x ^ (a + c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    HeckeOrigin.poleRemoved χ s * signalMellin (signal χ H c) c s =
      (s - 1) * gaussianMultiplier H s := by
  have hH' := analyticOnNhd_seven_eighths_of_boundary hb0 hH
  have hb' := contract_seven_eighths_of_boundary hb0 hb
  exact poleRemoved_mul_signalMellin χ H hH'.differentiableOn hb' c a ha htop hs

theorem nonzero_of_probe_bounds_boundary (χ : Character) (H : ℂ → ℂ)
    (J : ℝ → ℂ) (b0 β ω σ c : ℝ)
    (hb0half : (1 / 2 : ℝ) < b0) (hb0seven : b0 ≤ 7 / 8)
    (hβ : β ≤ 1) (hω0 : 0 < ω) (hω : ω < β - b0) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re})
    (hb : ∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (b0 + c + ω)))
    (herror : (fun x => J x - signal χ H c x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    {ρ : ℂ}
    (hρ : β - Supremum.continuationMarginBoundary b0 β ω σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - Supremum.continuationMarginBoundary b0 β ω σ
  have ha2 : a < 2 := by
    have hp := Supremum.continuationMarginBoundary_pos hω hσ
    dsimp [a]
    linarith
  have htop : signal χ H c =O[atTop] (fun x : ℝ => x ^ (a + c)) := by
    have h := Continuation.common_signal_bound_with_margin_boundary
      J (signal χ H c) b0 β ω σ c hJ herror
    convert h using 1
    dsimp [a]
    ring_nf
  have hH78 := analyticOnNhd_seven_eighths_of_boundary hb0seven hH
  have hb78 := contract_seven_eighths_of_boundary hb0seven hb
  have hHd := hH78.differentiableOn
  apply Continuation.nonzero_of_common_signal_boundary b0 β ω σ c hω0
    (LFunction χ) (regularL χ) (targetRegularizer χ) H J (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    hH hb (signal_locallyIntegrable χ H hHd hb78 c)
    (signal_rapidDecayAtZero χ H hHd hb78 c)
    hJ herror _ hρ _ (targetRegularizer_ne_zero χ hpole)
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by
      intro h
      norm_num [h] at hs1
    have h1 : s ≠ 1 := by
      intro h
      norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1),
      signalMellin_eq_amplitude_boundary b0 hb0seven χ H hH hb c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply regularL_eq χ _ hpole
    intro h
    have hboundary := Supremum.continuation_boundary_gt_b0
      (b0 := b0) (β := β) (σ := σ) hω0
    rw [h] at hρ
    norm_num at hρ
    linarith

end SevenEighths.HeckeSignal

end

end OAI