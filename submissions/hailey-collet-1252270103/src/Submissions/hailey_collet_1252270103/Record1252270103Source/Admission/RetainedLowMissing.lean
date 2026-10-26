/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowMissingGrouping
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment CompletedGauss RayFourExpansion
local notation "O" => HeckeFamily.O
variable {left : Bool} {u₀ : O} {unit : FirstSourceLabel→O}
local notation "Key" => NonzeroJointSourceLabel left u₀ unit

theorem missing_ray_sum
    (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (cost : Key→ℝ) (R : Ideal O) (hR : R≠0)
    (Z hi ε E : ℝ) (hZ : 0<Z) (hε : 0≤ε) (hE : 0≤E)
    (hsupported : ∀l∈labels,Supported l.val.1.1.1)
    (hhi : ∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi)
    (hfiber : ∀H∈labels.image (fun l=>firstSourceMissing left l.val.1),
      ∀r ψ : RayCharacter,
      (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,cost l)≤
        E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε) :
    (∑l∈labels,cost l)≤
      128*(Fintype.card RayCharacter:ℝ)^2*E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*
        Z^(hi*(1+ε)) := by
  have hlo (l : Key) (hl : l∈labels) : Z^(0:ℝ)≤((firstSourceMissing left l.val.1).absNorm:ℝ) := by
    rw [Real.rpow_zero]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (missing_nonzero labels hsupported l hl))
  simpa only [neg_zero,Real.rpow_zero,mul_one,zero_mul,sub_zero] using
    missing_ray_weighted_sum labels ray₁ ray₂ cost R hR Z 0 hi ε 0 E hZ hε
      (le_refl 0) hE hsupported hlo hhi hfiber

/-- Apply the uniform fixed-H/ray source estimate after its controls have been
chosen, preserving the existing row weight and the missing-norm normalization. -/
theorem missing_ray_weighted_energy
    (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (value : Key→ℂ) (weight : Key→ℝ) (R : Ideal O) (hR : R≠0)
    (Z lo hi ε γ E : ℝ) (hZ : 0<Z) (hε : 0≤ε) (hγ : 0≤γ) (hE : 0≤E)
    (hsupported : ∀l∈labels,Supported l.val.1.1.1)
    (hlo : ∀l∈labels,Z^lo≤((firstSourceMissing left l.val.1).absNorm:ℝ))
    (hhi : ∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi)
    (hfiber : ∀H∈labels.image (fun l=>firstSourceMissing left l.val.1),
      ∀r ψ : RayCharacter,
      (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,‖value l‖^2*weight l)≤
        E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε) :
    (∑l∈labels,‖value l‖^2*(weight l*((firstSourceMissing left l.val.1).absNorm:ℝ)^(-γ)))≤
      128*(Fintype.card RayCharacter:ℝ)^2*E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*
        Z^(hi*(1+ε)-γ*lo) := by
  simpa only [mul_assoc] using missing_ray_weighted_sum labels ray₁ ray₂
    (fun l=>‖value l‖^2*weight l) R hR Z lo hi ε γ E hZ hε hγ hE hsupported hlo hhi hfiber

end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.missing_ray_sum
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.missing_ray_weighted_energy
