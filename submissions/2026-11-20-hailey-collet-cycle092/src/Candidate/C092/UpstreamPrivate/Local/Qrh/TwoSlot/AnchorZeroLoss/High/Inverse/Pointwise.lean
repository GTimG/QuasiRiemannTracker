/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference

/-!
# High.Inverse.Pointwise — the inverse spike of one HIGH row

The actual inverse factor of the child row is `polynomial χ true (childLogTest Φ θ) (Z^r) 0 0`.
* `polynomial_childLogTest` — the log phase of `childLogTest Φ θ` is a frequency shift:
  `polynomial χ inv (childLogTest Φ θ) D 0 0 = polynomial χ inv Φ D 0 (2πθ)` (`D > 0`).
* `inverse_row_pointwise` — the buffered dyadic bound (baseline `HeckeDyadic.source_dyadic_bounds`,
  `inverse := true`; the inverse case of HC `buffered_clipped_plain_bounds`) for the inverse factor of
  any member `χ j` of a family whose buffered zero maximum at height `3(i+1)Z^τ` is `< a + 2e`:
  `‖M_v‖² ≤ C (Z^d)^((2a-1) r + ε)`. The constant depends only on `Φ` (support `[ao,bo]`) and the
  budget; the height `θ` enters only through the frequency gate `|2πθ| + Z^τ/2 ≤ (3i+2) Z^τ`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section

open scoped Classical ContDiff
open Set
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic

/-- The height of `childLogTest` is a frequency. -/
theorem polynomial_childLogTest (χ : Character) (inv : Bool) (Φ : ℝ → ℂ) (θ D : ℝ)
    (hD : 0 < D) :
    polynomial χ inv (InverseMoment.childLogTest Φ θ) D 0 0 =
      polynomial χ inv Φ D 0 (2*Real.pi*θ) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold summand InverseMoment.childLogTest
  have hx : 0 < norm I / D := div_pos (norm_pos I) hD
  have e1 : (((norm I / D : ℝ)) : ℂ)^(-shift 0 0) = 1 := by simp [shift]
  have e2 : (((norm I / D : ℝ)) : ℂ)^(-shift 0 (2*Real.pi*θ)) =
      FourierBridge.logPhase θ (Real.log (norm I / D)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
    unfold FourierBridge.logPhase shift
    congr 1
    push_cast
    ring
  rw [e1, e2]
  ring

/-- **Pointwise bound of the actual inverse factor** under a buffered zero guard. -/
theorem inverse_row_pointwise (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao)
    (hΦs : Function.support Φ ⊆ Icc ao bo) (hΦ : ContDiff ℝ ∞ Φ)
    (R dmax τ ε e κ η : ℝ) (hR : 0 ≤ R) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hη : 0 ≤ η)
    (hbudget : 12*e*(R+2)+8*κ+2*η ≤ ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Z d : ℝ), 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 < Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (a : ℝ) (i : ℕ),
      51/100 ≤ a → a ≤ 1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ)) < a+2*e →
    ∀ (j : ι) (r θ : ℝ), (χ j).modulus.absNorm ≤ Z^d → 0 ≤ r → r ≤ R →
      |2*Real.pi*θ| + (Z^τ)/2 ≤ (3*i+2 : ℕ)*(Z^τ) →
      (3+(3*i+2 : ℕ)*(Z^τ))^4 ≤ (Z^d)^η →
      ‖polynomial (χ j) true (InverseMoment.childLogTest Φ θ) ((Z^d)^r) 0 0‖^2 ≤
        C*(Z^d)^((2*a-1)*r+ε) := by
  let pb : ℕ → ℝ := fun k =>
    Classical.choose (CubicReflectionKernel.compact_source_mellin_strip_decay Φ ao bo hao hΦs hΦ
      (-2) 2 k)
  have hpb : ∀ k, 0 < pb k ∧ ∀ σ ∈ Icc (-2 : ℝ) 2, ∀ t : ℝ,
      (1 + |t|) ^ k * ‖mellin Φ ((σ : ℂ) + t * Complex.I)‖ ≤ pb k := fun k =>
    Classical.choose_spec (CubicReflectionKernel.compact_source_mellin_strip_decay Φ ao bo hao hΦs
      hΦ (-2) 2 k)
  obtain ⟨n, C, hC, hsrc⟩ := source_dyadic_bounds R dmax τ ε e κ η hR hdmax hτ hε he he' hκ hκ'
    hη hbudget pb (fun k => (hpb k).1.le)
  refine ⟨C, hC, ?_⟩
  intro Z d hZ hd hd' hT ι _ χ hχ a i ha ha' hmax j r θ hQ hr hrR hfreq hheight
  have hD : 0 < (Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by linarith) _) _
  have hstrip : Icc (1-a-6*e-0) (2-0) ⊆ Icc (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hb := hsrc Z d hZ hd hd' hT χ hχ a i ha ha' hmax j true Φ ao bo hao hΦs hΦ r 0
    (2*Real.pi*θ) hQ hr hrR hfreq hheight
    (fun x hx t => (hpb 2).2 x (hstrip hx) t)
    (fun x hx t => (hpb (n+2)).2 x (hstrip hx) t)
  rw [polynomial_childLogTest _ _ _ _ _ hD]
  exact hb.1

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.inverse_row_pointwise
