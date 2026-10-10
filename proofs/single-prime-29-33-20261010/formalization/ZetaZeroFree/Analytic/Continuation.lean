import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity
import OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum
import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
import ZetaZeroFree.Exponent

/-!
The analytic closing step of §5, with the manuscript's boundary and power shift.

The estimates supplied to these theorems are explicit hypotheses.  In particular,
this file does not claim to have constructed the compensated probe, or to have
proved its error estimate.  It proves that a common error saving gives the
claimed half-plane, without requiring the supremum to be attained.  The proof
uses the regularized L-function, including at the principal character's pole.
No earlier terminal nonvanishing theorem is used.
-/

namespace ZetaZeroFree.Analytic

noncomputable section
open Filter Asymptotics MeasureTheory
open OAI.SevenEighths
open HeckeFamily Continuation

def continuationMargin (β ε σ : ℝ) : ℝ := min (β - Exponent.b - ε) σ

theorem continuationMargin_pos {β ε σ : ℝ}
    (hε : ε < β - Exponent.b) (hσ : 0 < σ) :
    0 < continuationMargin β ε σ := by
  exact lt_min (by linarith) hσ

theorem continuation_boundary_gt {β ε σ : ℝ} (hε : 0 < ε) :
    Exponent.b < β - continuationMargin β ε σ := by
  have hm := min_le_left (β - Exponent.b - ε) σ
  unfold continuationMargin
  linarith

theorem signal_exponents (β ε σ : ℝ) :
    max (Exponent.b - Exponent.k + ε) (β - Exponent.k - σ) =
      β - Exponent.k - continuationMargin β ε σ := by
  unfold continuationMargin
  by_cases h : β - Exponent.b - ε ≤ σ
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_right (by linarith)]

theorem signal_bound (J f : ℝ → ℂ) (β ε σ : ℝ)
    (hJ : J =O[atTop] (fun Z : ℝ => Z ^ (Exponent.b - Exponent.k + ε)))
    (herror : (fun Z => J Z - f Z) =O[atTop]
      (fun Z : ℝ => Z ^ (β - Exponent.k - σ))) :
    f =O[atTop]
      (fun Z : ℝ => Z ^ ((β - continuationMargin β ε σ) - Exponent.k)) := by
  have hh := common_signal_bound J f (Exponent.b - Exponent.k + ε)
    (β - Exponent.k - σ) hJ herror
  rw [signal_exponents] at hh
  convert hh using 1
  funext Z
  congr 1
  ring

/-- A boundary-specific continuation theorem; its analytic estimates are inputs. -/
theorem nonzero_of_probe_bounds (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (β ε σ : ℝ) (hβ : β ≤ 1) (hε0 : 0 < ε)
    (hε : ε < β - Exponent.b) (hσ : 0 < σ)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (hJ : J =O[atTop] (fun Z : ℝ => Z ^ (Exponent.b - Exponent.k + ε)))
    (herror : (fun Z => J Z - HeckeSignal.signal χ H (-Exponent.k) Z) =O[atTop]
      (fun Z : ℝ => Z ^ (β - Exponent.k - σ)))
    {ρ : ℂ} (hρ : β - continuationMargin β ε σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let a := β - continuationMargin β ε σ
  have hm := continuationMargin_pos hε hσ
  have ha2 : a < 2 := by dsimp [a]; linarith
  have hboundary := continuation_boundary_gt (β := β) (σ := σ) hε0
  have haold : (7 / 8 : ℝ) < a :=
    Exponent.original_boundary_comparison.trans hboundary
  have htop : HeckeSignal.signal χ H (-Exponent.k) =O[atTop]
      (fun Z : ℝ => Z ^ (a + -Exponent.k)) := by
    simpa only [a, sub_eq_add_neg] using signal_bound J _ β ε σ hJ herror
  have hH' : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun s hs => haold.trans hs)
  apply nonzero_of_regularized_signal a 1 (-Exponent.k) (LFunction χ)
    (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
    (gaussianMultiplier H) (HeckeSignal.signal χ H (-Exponent.k))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (gaussianMultiplier_analytic hH')
    (HeckeSignal.signal_locallyIntegrable χ H hH.differentiableOn hb (-Exponent.k))
    htop
    (HeckeSignal.signal_rapidDecayAtZero χ H hH.differentiableOn hb (-Exponent.k))
    _ hρ _ (HeckeSignal.targetRegularizer_ne_zero χ hpole)
    (gaussianMultiplier_ne_zero (hb ρ (haold.trans hρ)))
  · intro s hs
    have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
    have h0 : s ≠ 0 := by intro he; norm_num [he] at hs1
    have h1 : s ≠ 1 := by intro he; norm_num [he] at hs1
    rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
      HeckeSignal.signalMellin_eq_amplitude χ H hH.differentiableOn hb
        (-Exponent.k) a ha2 htop hs]
    unfold HeckeSignal.amplitude HeckeSignal.quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn := LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply HeckeSignal.regularL_eq χ _ hpole
    intro he
    rw [he] at hρ
    norm_num at hρ
    have hbpos : 0 < Exponent.b := by norm_num [Exponent.b]
    linarith

/-- Actual targets may have different constants and thresholds, but not savings. -/
structure PrimitiveProbeEstimates (χ : Character) (β ε σ : ℝ) where
  H : ℂ → ℂ
  J : ℝ → ℂ
  analytic : AnalyticOnNhd ℂ H {s : ℂ | 7 / 8 < s.re}
  correction : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2
  physical : J =O[atTop] (fun Z : ℝ => Z ^ (Exponent.b - Exponent.k + ε))
  error : (fun Z => J Z - HeckeSignal.signal χ H (-Exponent.k) Z) =O[atTop]
    (fun Z : ℝ => Z ^ (β - Exponent.k - σ))

/-- §5's nonattainment argument, conditional on the quantified analytic estimates. -/
theorem beta_le_of_common_probe
    (hprobe : Exponent.b < HeckeZeroSupremum.beta →
      ∃ ε σ : ℝ, 0 < ε ∧ ε < HeckeZeroSupremum.beta - Exponent.b ∧ 0 < σ ∧
        ∀ χ : Character, FiniteFourier.IsPrimitiveOnIdeals χ.residue →
          Nonempty (PrimitiveProbeEstimates χ HeckeZeroSupremum.beta ε σ)) :
    HeckeZeroSupremum.beta ≤ Exponent.b := by
  by_contra hn
  have hβ : Exponent.b < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨ε, σ, hε0, hε, hσ, hp⟩ := hprobe hβ
  let Δ := continuationMargin HeckeZeroSupremum.beta ε σ
  have hΔ : 0 < Δ := continuationMargin_pos hε hσ
  have hboundary := continuation_boundary_gt
    (β := HeckeZeroSupremum.beta) (σ := σ) hε0
  have hsmall : (1 / 2 : ℝ) ≤ HeckeZeroSupremum.beta - Δ / 2 := by
    have hbhalf : (1 / 2 : ℝ) < Exponent.b := by norm_num [Exponent.b]
    dsimp [Δ]
    linarith
  obtain ⟨χ, ρ, hprimitive, _, _, hpole, hzero, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta (by linarith : 0 < Δ / 2) hsmall
  obtain ⟨data⟩ := hp χ hprimitive
  have hρ : HeckeZeroSupremum.beta -
      continuationMargin HeckeZeroSupremum.beta ε σ < ρ.re := by
    change HeckeZeroSupremum.beta - Δ < ρ.re
    linarith
  exact nonzero_of_probe_bounds χ data.H data.J HeckeZeroSupremum.beta ε σ
    HeckeZeroSupremum.beta_le_one hε0 hε hσ data.analytic data.correction
    data.physical data.error hρ hpole hzero

/-- The physical probe naturally uses the target with a finite set of Euler
factors deleted. The deletion data and its actual estimates remain explicit. -/
structure DeletedProbeEstimates (χ : Character) (β ε σ : ℝ) where
  primes : Finset (Ideal HeckeFamily.O)
  prime : ∀ P ∈ primes, Prime P
  probe : PrimitiveProbeEstimates (χ.excludePrimes primes prime) β ε σ

/-- Nonvanishing of the deleted target transfers to the original target,
including a nonprincipal value at one. -/
theorem nonzero_of_deleted_probe_bounds (χ : Character) (β ε σ : ℝ)
    (hβ : β ≤ 1) (hε0 : 0 < ε) (hε : ε < β - Exponent.b) (hσ : 0 < σ)
    (data : DeletedProbeEstimates χ β ε σ)
    {ρ : ℂ} (hρ : β - continuationMargin β ε σ < ρ.re)
    (hpole : ρ ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ ρ ≠ 0 := by
  let ψ := χ.excludePrimes data.primes data.prime
  have hmask := excludePrimes_mask χ data.primes data.prime
  have hpole' : ρ ≠ 1 ∨ ψ.residue ≠ 1 := by
    rcases hpole with hρ | hχ
    · exact Or.inl hρ
    · exact Or.inr (fun hψ => hχ
        ((HeckeFiniteDeletion.principal_iff_of_mask ψ χ hmask).mp hψ))
  have hψ := nonzero_of_probe_bounds ψ data.probe.H data.probe.J β ε σ
    hβ hε0 hε hσ data.probe.analytic data.probe.correction
    data.probe.physical data.probe.error hρ hpole'
  have hpos : 0 < ρ.re := by
    have hb : 0 < Exponent.b := by norm_num [Exponent.b]
    exact hb.trans ((continuation_boundary_gt (β := β) (σ := σ) hε0).trans hρ)
  intro hzero
  have heq := HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole ψ χ hmask hpos hpole'
  rw [heq, hzero, zero_mul] at hψ
  exact hψ rfl

/-- The quantified closing step for the actual finitely deleted probes. -/
theorem beta_le_of_common_deleted_probe
    (hprobe : Exponent.b < HeckeZeroSupremum.beta →
      ∃ ε σ : ℝ, 0 < ε ∧ ε < HeckeZeroSupremum.beta - Exponent.b ∧ 0 < σ ∧
        ∀ χ : Character, FiniteFourier.IsPrimitiveOnIdeals χ.residue →
          Nonempty (DeletedProbeEstimates χ HeckeZeroSupremum.beta ε σ)) :
    HeckeZeroSupremum.beta ≤ Exponent.b := by
  by_contra hn
  have hβ : Exponent.b < HeckeZeroSupremum.beta := lt_of_not_ge hn
  obtain ⟨ε, σ, hε0, hε, hσ, hp⟩ := hprobe hβ
  let Δ := continuationMargin HeckeZeroSupremum.beta ε σ
  have hΔ : 0 < Δ := continuationMargin_pos hε hσ
  have hboundary := continuation_boundary_gt
    (β := HeckeZeroSupremum.beta) (σ := σ) hε0
  have hsmall : (1 / 2 : ℝ) ≤ HeckeZeroSupremum.beta - Δ / 2 := by
    have hbhalf : (1 / 2 : ℝ) < Exponent.b := by norm_num [Exponent.b]
    dsimp [Δ]
    linarith
  obtain ⟨χ, ρ, hprimitive, _, _, hpole, hzero, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta (by linarith : 0 < Δ / 2) hsmall
  obtain ⟨data⟩ := hp χ hprimitive
  have hρ : HeckeZeroSupremum.beta -
      continuationMargin HeckeZeroSupremum.beta ε σ < ρ.re := by
    change HeckeZeroSupremum.beta - Δ < ρ.re
    linarith
  exact nonzero_of_deleted_probe_bounds χ HeckeZeroSupremum.beta ε σ
    HeckeZeroSupremum.beta_le_one hε0 hε hσ data hρ hpole hzero

end
end ZetaZeroFree.Analytic
