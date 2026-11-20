/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact homogeneous restoration on the original independent ordinary columns.
All heights, row coefficients, marks and finite retained rows are unchanged. -/
import Candidate.C092.transport.TerminalProfileUniformGates
import Candidate.C092.transport.OrdinaryColumn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeHeight
open CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles
open QRH.Cycle092.OrdinaryColumn
local notation "O" => HeckeFamily.O

def actualShort (V W : ℝ→ℂ) (opened : Bool) (R : ℝ) : ℝ→ℂ :=
  if opened then ratioProfile V W R else W

theorem original_profile_mul (η : Character) (m A z : O) (W : ℝ→ℂ)
    (c : ℝ) (t X : ℝ) :
    original η m A z (fun x => (c:ℂ)*W x) t X = (c:ℂ)*original η m A z W t X := by
  have he : rowTwistedSum η m A z (fun x => (c:ℂ)*W x) t X =
      (c:ℂ)*rowTwistedSum η m A z W t X := by
    unfold rowTwistedSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro I
    ring
  unfold original
  rw [he]
  ring

theorem actualShort_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S)
    {C : ℝ} (hC : 0 < C) (V : ℝ→ℂ) (W : 𝓢(ℝ,ℂ)) (opened : Bool) (R x : ℝ) :
    actualShort V W opened R x = ((C*sourceControl S W:ℝ):ℂ)*
      actualShort V (unitProfile S C W) opened R x := by
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (unitProfile_reconstruct S hS hC W)
  have hp : W x = ((C*sourceControl S W:ℝ):ℂ)*unitProfile S C W x := by
    simpa only [smul_apply,Complex.real_smul] using he.symm
  cases opened <;> simp only [actualShort,Bool.false_eq_true,↓reduceIte,ratioProfile] <;> rw [hp] <;> ring

def actualEnergy {ρ : Type} (rows : Finset ρ) (η₁ η₂ : Character)
    (m₁ A₁ m₂ A₂ z : ρ→O) (t₁ t₂ X₁ X₂ : ρ→ℝ)
    (V : ℝ→ℂ) (W₁ W₂ : 𝓢(ℝ,ℂ)) (opened : ρ→Bool) (R : ρ→ℝ)
    (marks : ρ→ℂ) : ℝ :=
  ∑ r ∈ rows, ‖original η₁ (m₁ r) (A₁ r) (z r) (W₁:ℝ→ℂ) (t₁ r) (X₁ r)*
    original η₂ (m₂ r) (A₂ r) (z r) (actualShort V W₂ (opened r) (R r)) (t₂ r) (X₂ r)*marks r‖^2

/-- The exponent of EACH original profile norm is exactly two. No fourth
power from the long-source unit estimate is paid a second time. -/
theorem actualEnergy_reconstruct {ρ : Type} (rows : Finset ρ) (η₁ η₂ : Character)
    (m₁ A₁ m₂ A₂ z : ρ→O) (t₁ t₂ X₁ X₂ : ρ→ℝ)
    (V : ℝ→ℂ) (W₁ W₂ : 𝓢(ℝ,ℂ)) (opened : ρ→Bool) (R : ρ→ℝ) (marks : ρ→ℂ)
    (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S) {C : ℝ} (hC : 0 < C) :
    actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V W₁ W₂ opened R marks =
    C^4*(sourceControl S W₁*sourceControl S W₂)^2*
      actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
        (unitProfile S C W₁) (unitProfile S C W₂) opened R marks := by
  let c₁ := C*sourceControl S W₁
  let c₂ := C*sourceControl S W₂
  have hc₁ : 0 ≤ c₁ := mul_nonneg hC.le (sourceControl_nonneg _ _)
  have hc₂ : 0 ≤ c₂ := mul_nonneg hC.le (sourceControl_nonneg _ _)
  have hlong : (W₁:ℝ→ℂ) = fun x => (c₁:ℂ)*unitProfile S C W₁ x := by
    funext x
    have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (unitProfile_reconstruct S hS hC W₁)
    simpa only [smul_apply,Complex.real_smul] using he.symm
  have hshort (r : ρ) : actualShort V W₂ (opened r) (R r) =
      fun x => (c₂:ℂ)*actualShort V (unitProfile S C W₂) (opened r) (R r) x :=
    funext (actualShort_reconstruct S hS hC V W₂ (opened r) (R r))
  unfold actualEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hlong,hshort,original_profile_mul,original_profile_mul]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc₁,abs_of_nonneg hc₂]
  dsimp [c₁,c₂]
  ring

#print axioms actualEnergy_reconstruct
end
end QRH.Cycle092.TerminalProfileUniform
