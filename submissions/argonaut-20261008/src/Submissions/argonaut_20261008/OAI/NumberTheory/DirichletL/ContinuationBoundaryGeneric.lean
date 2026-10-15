import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Continuation

namespace OAI

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace SevenEighths.Supremum

/-- The continuation saving obtained from a common probe at an arbitrary boundary `b0`. -/
def continuationMarginBoundary (b0 β ω σ : ℝ) : ℝ :=
  min (β - b0 - ω) σ

theorem continuationMarginBoundary_pos {b0 β ω σ : ℝ}
    (hω : ω < β - b0) (hσ : 0 < σ) :
    0 < continuationMarginBoundary b0 β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

theorem continuationMarginBoundary_le_gap (b0 β ω σ : ℝ) :
    continuationMarginBoundary b0 β ω σ ≤ β - b0 - ω :=
  min_le_left _ _

theorem continuationMarginBoundary_le_sigma (b0 β ω σ : ℝ) :
    continuationMarginBoundary b0 β ω σ ≤ σ :=
  min_le_right _ _

theorem continuation_boundary_gt_b0 {b0 β ω σ : ℝ} (hω : 0 < ω) :
    b0 < β - continuationMarginBoundary b0 β ω σ := by
  have h := continuationMarginBoundary_le_gap b0 β ω σ
  linarith

theorem max_signal_exponents_boundary (b0 β ω σ c : ℝ) :
    max (b0 + c + ω) (β + c - σ) =
      β + c - continuationMarginBoundary b0 β ω σ := by
  unfold continuationMarginBoundary
  rcases le_total (β - b0 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem max_normalized_signal_exponents_boundary (b0 β ω σ : ℝ) :
    max (b0 - 11 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMarginBoundary b0 β ω σ := by
  convert max_signal_exponents_boundary b0 β ω σ (-(11 / 16)) using 1 <;> ring

/-- The concrete boundary requested in the application. -/
def targetBoundary : ℝ := 3499999 / 4000000

theorem targetBoundary_gt_half : (1 / 2 : ℝ) < targetBoundary := by
  norm_num [targetBoundary]

theorem targetBoundary_lt_seven_eighths : targetBoundary < (7 / 8 : ℝ) := by
  norm_num [targetBoundary]

theorem targetBoundary_gap :
    (7 / 8 : ℝ) - targetBoundary = 1 / 4000000 := by
  norm_num [targetBoundary]

theorem targetBoundary_normalized :
    targetBoundary - 11 / 16 = (749999 / 4000000 : ℝ) := by
  norm_num [targetBoundary]

theorem b0_of_uniform_margin {S : Set ℝ} {b0 : ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : b0 < sSup S →
      ∃ ω σ : ℝ, ω < sSup S - b0 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup S - continuationMarginBoundary b0 (sSup S) ω σ) :
    sSup S ≤ b0 := by
  by_contra h
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  exact uniform_bound_below_supremum_false hne hbounded
    (continuationMarginBoundary_pos hω hσ) hbound

theorem b0_of_uniform_margin_with_sentinel {S : Set ℝ} {b0 : ℝ}
    (hb0 : (1 / 2 : ℝ) < b0)
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : b0 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧
        ω < sSup (insert (1 / 2 : ℝ) S) - b0 ∧ 0 < σ ∧
        ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMarginBoundary b0 (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ b0 := by
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMarginBoundary_pos hω hσ
  have hboundary := continuation_boundary_gt_b0
    (b0 := b0) (β := sSup (insert (1 / 2 : ℝ) S)) (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMarginBoundary b0 (sSup (insert (1 / 2 : ℝ) S)) ω σ := by
    linarith
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt

end SevenEighths.Supremum

namespace SevenEighths.Continuation

theorem common_signal_bound_with_margin_boundary (J f : ℝ → ℂ)
    (b0 β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (b0 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Supremum.continuationMarginBoundary b0 β ω σ)) := by
  simpa only [Supremum.max_signal_exponents_boundary] using
    common_signal_bound J f (b0 + c + ω) (β + c - σ) hJ herror

theorem nonzero_of_common_signal_boundary (b0 β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | β - Supremum.continuationMarginBoundary b0 β ω σ < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | β - Supremum.continuationMarginBoundary b0 β ω σ < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | b0 < s.re})
    (hcontract : ∀ s : ℂ, b0 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (b0 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ,
      max (β - Supremum.continuationMarginBoundary b0 β ω σ) 1 < s.re →
        Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ}
    (hρ : β - Supremum.continuationMarginBoundary b0 β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by
  have hboundary := Supremum.continuation_boundary_gt_b0
    (b0 := b0) (β := β) (σ := σ) hω
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | β - Supremum.continuationMarginBoundary b0 β ω σ < s.re} :=
    hH.mono (fun s hs => lt_trans hboundary hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β - Supremum.continuationMarginBoundary b0 β ω σ) + c)) := by
    have hexp :
        (β - Supremum.continuationMarginBoundary b0 β ω σ) + c =
          β + c - Supremum.continuationMarginBoundary b0 β ω σ := by
      ring
    simpa only [hexp] using
      common_signal_bound_with_margin_boundary J f b0 β ω σ c hJ herror
  exact nonzero_of_regularized_signal _ 1 c L Lregular R (gaussianMultiplier H) f
    hL hR (gaussianMultiplier_analytic hH') hlocal htop hzero heq hρ hregular
    hRρ (gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hboundary hρ)))

end SevenEighths.Continuation

end

end OAI