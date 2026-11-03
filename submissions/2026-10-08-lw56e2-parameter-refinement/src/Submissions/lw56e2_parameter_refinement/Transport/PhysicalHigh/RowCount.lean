/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/RowCount.lean
Original SHA-256: 42e8be6a17e7b8fadc2fc4e8b2d9ca59303e9d9215ba6ce71c876326453f7dd1
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCount
import Submissions.lw56e2_parameter_refinement.Transport.TunedEndpoint

/-!+# Actual detector-row counting at fixed plain-moment parameter 3/4

This module specializes the upstream arithmetic row-count theorem to Δ=0.
The conclusion counts the actual rows of a `HeckeDetectorBatch.Batch`, not
an abstract scalar standing for their number. The input `Moments F 0 ...`
retains the actual inverse/plain polynomials, original masks, strict inverse
widths, and the plain marked capacity with parameter 3/4.

This is not yet a producer of those moment hypotheses for the tuned probe,
nor an estimate for the compensated physical integral. Those interfaces are
kept explicit rather than replaced by an axiom or a scalar assumption.
-/

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorAdaptiveCutoff

/-- The source's complementary amplitude coordinate gives precisely the
full rational count used by the tuned endpoint certificate. -/
theorem balanced_count_eq (δ x : ℝ) :
    OAI.SevenEighths.Endpoint.balancedRowCount δ (1 / 2 - x) =
      LW56e2.Transport.Endpoint.adaptiveCount δ x := by
  have hJ : OAI.SevenEighths.Endpoint.balanceDenominator δ (1 / 2 - x) =
      LW56e2.Transport.Endpoint.countDenominator δ x := by
    unfold OAI.SevenEighths.Endpoint.balanceDenominator
      OAI.SevenEighths.Endpoint.denominator OAI.SevenEighths.Endpoint.primeWeight
      LW56e2.Transport.Endpoint.countDenominator
    ring
  have hP : OAI.SevenEighths.Endpoint.primeWeight (1 / 2 - x) =
      (2 - 8 * x / 9) * (1 - x) := by
    unfold OAI.SevenEighths.Endpoint.primeWeight
    ring
  unfold OAI.SevenEighths.Endpoint.balancedRowCount
    OAI.SevenEighths.Endpoint.balancedCutoff
  rw [hJ, hP]
  unfold LW56e2.Transport.Endpoint.adaptiveCount
  ring

/-- A genuine arithmetic cardinality estimate for nonfloor detector batches.

The only analytic estimate still assumed here is `Moments` on each actual
fiber, at Δ=0. In particular, no hypothesis β>7/8 is inherited from the
upstream final application. The explicit ceiling a≤7/8 ensures that all
bins use the balanced branch and lie in the tuned certificate's δ range.
-/
theorem actual_nonfloor_count_fixed_kappa
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance ν C height q : ℝ) (i : ℕ),
      1 < U → 51 / 100 < a → a ≤ 7 / 8 → 0 ≤ ε → ε ≤ 1 / 1000 →
      0 < ν → 0 ≤ C → 0 ≤ height →
      2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
      ∀ {Label Slot : Type*} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff (2 * a - 1) q) T allowance i),
      B.rows.Nonempty →
      (∀ u ∈ B.rows,
        rowMean B.slots U ((2 * a - 1) / 2) B.binWidth B.widths
          (physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external U) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) 0 c κ C height εm) →
      (B.rows.card : ℝ) ≤
        (Fintype.card Label : ℝ) * (dyadicLength U : ℝ) ^ 2 *
          fiberConstant C height K₀ * (Fintype.card B.Bin : ℝ) *
          U ^ (LW56e2.Transport.Endpoint.adaptiveCount (2 * a - 1) (q / (2 * a - 1)) +
            159 * ε + εm + B.mesh + 7 * ν) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ :=
    ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance ν C height q i hU ha ha' hε hε' hν hC hh hf
    Label Slot _ B hne hq hmom
  have hδ : 2 * a - 1 ≤ (5 / 6 : ℝ) := by linarith
  have hc' := hcount a ε T allowance 0 ν C height q i
    hU ha hδ hε hε' (by norm_num) (by norm_num) hν hC hh hf B hne hq hmom
  simpa only [balanced_count_eq, zero_div, add_zero] using hc'

end
end LW56e2.Transport.PhysicalHigh
