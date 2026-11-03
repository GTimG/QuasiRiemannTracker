/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/Continuation.lean
Original SHA-256: 60ae6bd8f0dfd0cdc7e4c46157c4ca12d24e400bd970e4f911cf7e6c2e6ef622
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Continuation

/-!
# Continuation from a common probe at an arbitrary boundary

This module proves a conditional analytic bridge. The two estimates concern the
same probe `J`, and its comparison signal is `f`. The physical probe estimates,
the analytic multiplier on the enlarged half-plane, and the regularized Mellin
identity are explicit hypotheses. No Hecke or Dirichlet nonvanishing result is
asserted here without those inputs.

The unchanged continuation infrastructure is from the pinned OpenAI source;
see `upstream-config/source-manifest.json` and `upstream-config/LICENSE`.
-/

namespace LW56e2.Transport

noncomputable section

open Filter Asymptotics MeasureTheory
open OAI.SevenEighths.Continuation

/-- The rightmost exponent after combining the low bound and the comparison error. -/
def continuationBoundary (B β ω σ : ℝ) : ℝ := max (B + ω) (β - σ)

/-- The amount by which the common signal continues left of `β`. -/
def continuationMargin (B β ω σ : ℝ) : ℝ := min (β - B - ω) σ

theorem continuationBoundary_eq_sub_margin (B β ω σ : ℝ) :
    continuationBoundary B β ω σ = β - continuationMargin B β ω σ := by
  unfold continuationBoundary continuationMargin
  rcases le_total (β - B - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem continuationMargin_pos {B β ω σ : ℝ}
    (hω : ω < β - B) (hσ : 0 < σ) :
    0 < continuationMargin B β ω σ := by
  exact lt_min (sub_pos.mpr hω) hσ

theorem boundary_lt_supremum {B β ω σ : ℝ}
    (hω : ω < β - B) (hσ : 0 < σ) :
    continuationBoundary B β ω σ < β := by
  exact max_lt (by linarith) (by linarith)

theorem base_lt_boundary {B β ω σ : ℝ} (hω : 0 < ω) :
    B < continuationBoundary B β ω σ := by
  have h := le_max_left (B + ω) (β - σ)
  change B < max (B + ω) (β - σ)
  linarith

theorem common_signal_bound_at_boundary
    (J f : ℝ → ℂ) (B β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ => x ^ (continuationBoundary B β ω σ + c)) := by
  have hexp : max (B + c + ω) (β + c - σ) =
      continuationBoundary B β ω σ + c := by
    unfold continuationBoundary
    rcases le_total (B + ω) (β - σ) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      linarith
    · rw [max_eq_left h, max_eq_left (by linarith)]
      linarith
  simpa only [hexp] using
    common_signal_bound J f (B + c + ω) (β + c - σ) hJ herror

/-- A single common probe rules out a nonpole zero to the right of the combined
boundary. All analytic and physical inputs remain hypotheses. This statement
itself does not require `B > 1/2` or `β ≤ 1`. -/
theorem nonzero_of_common_probe
    (B β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | B < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | B < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | B < s.re})
    (hcontract : ∀ s : ℂ, B < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (B + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (continuationBoundary B β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : continuationBoundary B β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) :
    L ρ ≠ 0 := by
  have hbase : B < continuationBoundary B β ω σ := base_lt_boundary hω
  have hL' : AnalyticOnNhd ℂ Lregular
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hL.mono (fun _ hs => hbase.trans hs)
  have hR' : AnalyticOnNhd ℂ R
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hR.mono (fun _ hs => hbase.trans hs)
  have hH' : AnalyticOnNhd ℂ H
      {s : ℂ | continuationBoundary B β ω σ < s.re} :=
    hH.mono (fun _ hs => hbase.trans hs)
  exact nonzero_of_regularized_signal (continuationBoundary B β ω σ) 1 c
    L Lregular R (gaussianMultiplier H) f hL' hR'
    (gaussianMultiplier_analytic hH') hlocal
    (common_signal_bound_at_boundary J f B β ω σ c hJ herror) hzero
    heq hρ hregular hRρ
    (gaussianMultiplier_ne_zero (hcontract ρ (hbase.trans hρ)))

/-- Under the usual strip hypotheses the resulting boundary lies strictly
between `B` and `β`; thus a zero sufficiently close to `β` is contradicted. -/
theorem strip_boundary_margins {B β ω σ : ℝ}
    (hB : (1 / 2 : ℝ) < B) (hβ : β ≤ 1)
    (hω0 : 0 < ω) (hω : ω < β - B) (hσ : 0 < σ) :
    (1 / 2 : ℝ) < continuationBoundary B β ω σ ∧
      B < continuationBoundary B β ω σ ∧
      continuationBoundary B β ω σ < β ∧
      continuationBoundary B β ω σ < 1 ∧
      0 < continuationMargin B β ω σ := by
  have hleft := base_lt_boundary (B := B) (β := β) (σ := σ) hω0
  have hright := boundary_lt_supremum hω hσ
  exact ⟨hB.trans hleft, hleft, hright, hright.trans_le hβ,
    continuationMargin_pos hω hσ⟩

/-- Abstract final supremum step. A caller must provide the uniform zero bound;
the analytic bridge alone does not construct that bound. -/
theorem supremum_le_of_uniform_boundary (B : ℝ) (S : Set ℝ)
    (hne : S.Nonempty) (hbounded : BddAbove S)
    (hbound : B < sSup S → ∃ ω σ : ℝ,
      ω < sSup S - B ∧ 0 < σ ∧
      ∀ x ∈ S, x ≤ continuationBoundary B (sSup S) ω σ) :
    sSup S ≤ B := by
  by_contra hn
  obtain ⟨ω, σ, hω, hσ, hbound⟩ := hbound (lt_of_not_ge hn)
  apply OAI.SevenEighths.Supremum.uniform_bound_below_supremum_false hne hbounded
    (continuationMargin_pos hω hσ)
  intro x hx
  simpa only [continuationBoundary_eq_sub_margin] using hbound x hx

end

end LW56e2.Transport
