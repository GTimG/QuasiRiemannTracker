/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowMissing
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment CompletedGauss RayFourExpansion
local notation "O"=>HeckeFamily.O
variable {left : Bool} {u₀ : O} {unit : FirstSourceLabel→O}
local notation "Key"=>NonzeroJointSourceLabel left u₀ unit

def fiberInclusion (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (H : Ideal O) (r ψ : RayCharacter)
    (l : missingRayFiber labels ray₁ ray₂ H r ψ) : labels :=
  ⟨l.val,((mem_missingRayFiber labels ray₁ ray₂ H r ψ l.val).mp l.property).1⟩

theorem missing_ray_subtype_energy
    (labels : Finset Key) (ray₁ ray₂ : Key→RayCharacter)
    (value : labels→ℂ) (weight : labels→ℝ) (R : Ideal O) (hR : R≠0)
    (Z lo hi ε γ E : ℝ) (hZ : 0<Z) (hε : 0≤ε) (hγ : 0≤γ) (hE : 0≤E)
    (hsupported : ∀l∈labels,Supported l.val.1.1.1)
    (hlo : ∀l∈labels,Z^lo≤((firstSourceMissing left l.val.1).absNorm:ℝ))
    (hhi : ∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi)
    (hfiber : ∀H∈labels.image (fun l=>firstSourceMissing left l.val.1),
      ∀r ψ : RayCharacter,
      (∑l : missingRayFiber labels ray₁ ray₂ H r ψ,
        ‖value (fiberInclusion labels ray₁ ray₂ H r ψ l)‖^2*
          weight (fiberInclusion labels ray₁ ray₂ H r ψ l))≤
        E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε) :
    (∑l : labels,‖value l‖^2*(weight l*
      ((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)))≤
      128*(Fintype.card RayCharacter:ℝ)^2*E*((∏I∈primeSupport R,I).absNorm:ℝ)^ε*
        Z^(hi*(1+ε)-γ*lo) := by
  let v : Key→ℂ:=fun l=>if h:l∈labels then value ⟨l,h⟩ else 0
  let w : Key→ℝ:=fun l=>if h:l∈labels then weight ⟨l,h⟩ else 0
  have hf (H : Ideal O) (hH : H∈labels.image (fun l=>firstSourceMissing left l.val.1))
      (r ψ : RayCharacter) :
      (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,‖v l‖^2*w l)≤
        E*((∏I∈primeSupport (R*H),I).absNorm:ℝ)^ε := by
    have he : (∑l∈missingRayFiber labels ray₁ ray₂ H r ψ,‖v l‖^2*w l)=
        ∑l : missingRayFiber labels ray₁ ray₂ H r ψ,
          ‖value (fiberInclusion labels ray₁ ray₂ H r ψ l)‖^2*
            weight (fiberInclusion labels ray₁ ray₂ H r ψ l) := by
      rw [←Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro l _
      have hl:=((mem_missingRayFiber labels ray₁ ray₂ H r ψ l.val).mp l.property).1
      simp only [v,w,dif_pos hl,fiberInclusion]
    rw [he]
    exact hfiber H hH r ψ
  have hh:=missing_ray_weighted_energy labels ray₁ ray₂ v w R hR
    Z lo hi ε γ E hZ hε hγ hE hsupported hlo hhi hf
  have he : (∑l∈labels,‖v l‖^2*(w l*((firstSourceMissing left l.val.1).absNorm:ℝ)^(-γ)))=
      ∑l : labels,‖value l‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)) := by
    rw [←Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro l _
    simp only [v,w,dif_pos l.property]
  rwa [he] at hh
end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.missing_ray_subtype_energy
