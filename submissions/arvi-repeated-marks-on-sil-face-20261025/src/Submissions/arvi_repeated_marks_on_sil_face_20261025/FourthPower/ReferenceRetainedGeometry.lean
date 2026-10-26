/- Copyright (c) 2026 Sil. Apache-2.0.
Actual retained natural-reflection scales, including the empty range below
one. Reuses the pinned finite-annular identity, without new reflection data.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceRetainedGeometry
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentRetainedWeightedSource
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation CenteredMomentSectorLocalization
open CenteredMomentReflectionRetainedLength
open CenteredMomentReflectionTailMass

theorem dualScale_bound (χ ψ : Character) (X U : ℝ) (hX : 0 < X)
    (hc : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm)
    (hm : (χ.modulus.absNorm : ℝ) ≤ U)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    dualScale χ ψ X D H ≤ U/X := by
  have hp : 0 < (ψ.modulus.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap : (ψ.modulus.absNorm : ℝ)*(Ideal.absNorm (∏ P ∈ sourcePrimes χ ψ, P) : ℝ) ≤ U := by
    have hh : (ψ.modulus.absNorm : ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus) : ℝ) ≤
        (χ.modulus.absNorm : ℝ) := by exact_mod_cast hc
    exact hh.trans hm
  exact (dual_scale_bounds _ D.val (redundantSet_prime _ _) (Finset.mem_powerset.mp D.property)
    H (ψ.modulus.absNorm : ℝ) X (U/X) hp hX (by rwa [div_mul_cancel₀ _ hX.ne'])).2

theorem retained_bounds (χ ψ : Character) (X U A : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hc : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm)
    (hm : (χ.modulus.absNorm : ℝ) ≤ U) (u : Index (sourcePrimes χ ψ))
    (hY : 0 < dualScale χ ψ X u.1.1 u.1.2)
    (hu : u.2 ∈ retainedAnnuli A (dualScale χ ψ X u.1.1 u.1.2) hY) :
    1 ≤ dyadicScale u.2*dualScale χ ψ X u.1.1 u.1.2 ∧
    dyadicScale u.2*dualScale χ ψ X u.1.1 u.1.2 ≤ 4*A*(U/X) := by
  refine ⟨retained_scale_lower A _ hY u.2 hu,?_⟩
  exact mul_le_mul (retained_scale_le A u.2 ((retainedAnnuli_mem _ _ hY u.2).mp hu).1)
    (dualScale_bound χ ψ X U hX hc hm u.1.1 u.1.2) hY.le (by positivity)

theorem retained_log_box (χ ψ : Character) (X U A Y : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hc : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm)
    (hm : (χ.modulus.absNorm : ℝ) ≤ U) (hcap : 4*A*(U/X) ≤ Y)
    (u : Index (sourcePrimes χ ψ)) (hY : 0 < dualScale χ ψ X u.1.1 u.1.2)
    (hu : u.2 ∈ retainedAnnuli A (dualScale χ ψ X u.1.1 u.1.2) hY) :
    Real.log (dyadicScale u.2*dualScale χ ψ X u.1.1 u.1.2) ∈ Icc 0 (Real.log Y) := by
  have hh := retained_bounds χ ψ X U A hX hA hc hm u hY hu
  exact ⟨Real.log_nonneg hh.1,
    Real.log_le_log (zero_lt_one.trans_le hh.1) (hh.2.trans hcap)⟩

/-- If the entire actual reflected range is shorter than one, there are no
retained annuli. This case must not be replaced by enlarging its length to one. -/
theorem retainedOriginal_zero (χ ψ : Character) (W : ℝ → ℂ) (X U A t : ℝ)
    (hX : 0 < X) (hA : 0 ≤ A)
    (hc : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm ≤ χ.modulus.absNorm)
    (hm : (χ.modulus.absNorm : ℝ) ≤ U) (hsmall : 4*A*(U/X) < 1) :
    retainedOriginal χ ψ W X A t = 0 := by
  have hempty (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
      retainedAnnuli A (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hh := retained_bounds χ ψ X U A hX hA hc hm ((D,H),k) _ hk
    exact (not_le_of_gt hsmall) (hh.1.trans hh.2)
  unfold retainedOriginal
  apply Finset.sum_eq_zero
  intro D hD
  have hh (H : SmoothIdeal (sourcePrimes χ ψ)) :
      finiteAnnularColumn χ.inverse
        (EisensteinSchwartzPoisson.paperRadialFourier (CompletedHeight.normTwistedSource W t)) A
        (dualScale χ ψ X ⟨D,hD⟩ H) = 0 := by
    rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX ⟨D,hD⟩ H),hempty]
    exact Finset.sum_empty
  have hz : ∀ H : SmoothIdeal (sourcePrimes χ ψ),
      CenteredMomentReflectionMass.coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
        finiteAnnularColumn χ.inverse
          (EisensteinSchwartzPoisson.paperRadialFourier (CompletedHeight.normTwistedSource W t)) A
          (dualScale χ ψ X ⟨D,hD⟩ H) = 0 := fun H => by rw [hh H,mul_zero]
  exact (tsum_congr hz).trans tsum_zero

end
end Candidate.FourthPower.ReferenceRetainedGeometry
