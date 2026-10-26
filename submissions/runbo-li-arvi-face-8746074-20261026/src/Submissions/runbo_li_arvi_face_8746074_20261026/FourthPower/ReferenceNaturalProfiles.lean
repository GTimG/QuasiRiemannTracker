/- Copyright (c) 2026 Sil. Apache-2.0.
Reuse the baseline common-profile and logarithmic scale separation. Only
common test profiles enter the energy premise. The actual annular factors,
with row-dependent Fourier height and scale, occur in the conclusion.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceNaturalProfiles
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentReflectedNormalization CenteredMomentReflectedUniformPair
open CenteredMomentScaleSupremum (scaleTest)

/-- The physical multiplier P is arbitrary (and may contain the square root
of a nonnegative row weight). Annular mass stays inside that multiplier.
The common-profile energy premise is explicit and is not asserted here. -/
theorem actual_annular_energy (a b : ℝ) (ha : 0 < a) (B J : ℕ) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι],
        ∀ (χ : ι → Character) (P : ι → ℂ) (k : ι → ℤ)
          (t lx ly omega : ι → ℝ) (Wshort : ℝ → ℂ) (c d lo hi low high E T : ℝ),
        0 ≤ d → Function.support Wshort ⊆ Icc c d → ContDiff ℝ ∞ Wshort →
        lo ≤ hi → low ≤ high → (∀ i, lx i ∈ Icc lo hi) →
        (∀ i, ly i ∈ Icc low high) → 0 ≤ E → 0 ≤ T → (∀ i, 1+‖t i‖ ≤ T) →
        (∀ v : ℝ, ∀ j h : Fin 2, ∀ x ∈ Icc lo hi, ∀ y ∈ Icc low high,
          (∑ i, ‖polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z : ℂ)) j)
              (Real.exp x) 0 (-2*Real.pi*v) *
            polynomial (χ i) false (scaleTest Wshort h) (Real.exp y) 0 (omega i) *
            ((annularMass B (k i) : ℂ)*P i)‖^2) ≤ E*(1+‖v‖)^(2*J)) →
        (∑ i, ‖(Real.sqrt (dyadicScale (k i)) : ℂ) *
            polynomial (χ i).inverse false
              (annularProfile (paperRadialFourier (CompletedHeight.normTwistedSource Wlong (t i)))
                (dyadicScale (k i))) (Real.exp (lx i)) 0 0 *
            polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2) ≤
          C*T^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionScaleEnergy.actual_one_rowwise_scales a b ha B J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P k t lx ly omega Wshort c d lo hi low high E T
    hd hshort hshortsmooth hlo hlow hlx hly hE hT ht henergy
  have hbase := hb χ (fun i => (annularMass B (k i) : ℂ)*P i)
    (fun i => dyadicScale (k i)) t lx ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlo hlow hlx hly (fun i => dyadicScale_pos (k i)) hE henergy
  let F (i : ι) : ℂ := polynomial (χ i).inverse false
    (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong B n
      (dyadicScale (k i)) (t i)) (Real.exp (lx i)) 0 0 *
    polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*
    ((annularMass B (k i) : ℂ)*P i)
  have he (i : ι) :
      (Real.sqrt (dyadicScale (k i)) : ℂ) *
        polynomial (χ i).inverse false
          (annularProfile (paperRadialFourier (CompletedHeight.normTwistedSource Wlong (t i)))
            (dyadicScale (k i))) (Real.exp (lx i)) 0 0 *
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i =
      (((1+‖t i‖)^n : ℝ) : ℂ)*F i := by
    have hh := actual_annular_normalization (χ i).inverse Wlong B n (k i) (t i)
      (Real.exp (lx i)/dyadicScale (k i))
    rw [mul_div_cancel₀ _ (dyadicScale_pos (k i)).ne'] at hh
    rw [hh]
    dsimp only [F]
    ring
  simp_rw [he]
  calc
    _ ≤ ∑ i, T^(2*n)*‖F i‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
        ← pow_mul, Nat.mul_comm n 2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (ht i) _) (sq_nonneg _)
    _ = T^(2*n)*∑ i, ‖F i‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ T^(2*n)*(C*(1+2*(hi-lo))*(1+2*(high-low))*E) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hT _)
    _ = _ := by ring

end
end Candidate.FourthPower.ReferenceNaturalProfiles
