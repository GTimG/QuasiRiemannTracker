/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact ordinary height transport with the full original row filter. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Reference.MaskTransfer
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge CenteredMomentLattice
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentSecondHeightFamily CenteredMomentTwist CenteredMomentOriginalRadialComparison
open QRH.Record1252270103Reference
local notation "O" => HeckeFamily.O

/-- The outer height is an exact unit phase. This equality retains the mask,
the full row filter, both raw scales and every marked coefficient. -/
theorem energy_height {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (R : Ideal O) (hR : R≠0) (t : ℝ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (keep : O→Prop) (hkeep : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ pool β P X₁ X₂ keep Φ K =
      energy η (fixedBadMask*idealGenerator R) 1 0
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t)
        pool (fun i=>heightCoefficient (β i) t) P X₁ X₂ keep Φ K := by
  rw [energy_eq_masked_radial η R hR _ _ a b ha
    ((normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁)
    ((normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂)
    pool (fun i=>heightCoefficient (β i) t) P hP X₁ X₂ hX₁ hX₂ keep hkeep Φ K]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz,ite_true]
    rw [original_positive_normalized (naturalRow η z (hkeep z hz)) R hR
      W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
      pool β P hP t X₁ X₂ hX₁ hX₂]
    rw [naturalCharacter_eq η z (hkeep z hz)]
    simp only [norm_mul,positive_height_phase_norm X₁ t hX₁,
      positive_height_phase_norm X₂ t hX₂,one_mul]
  · simp only [hz,ite_false]

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.energy_height
