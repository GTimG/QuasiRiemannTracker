import Candidate.Target830.Source.Assembly.InitialHeight
set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R≤H)

/-- A proved smaller source error is enlarged only after the finite
parameters, mesh and controls have been fixed. -/
theorem initial_affine_error_mono (plane : SourcePlane)
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax εsmall εbig Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hC : 0≤C) (hZ : 1<Z) (he : εsmall≤εbig)
    (h : Physical.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εsmall Z η η₀ Q degree S C) :
    Physical.InitialAffineAt (P:=plane) (α:=α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
      εbig Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hb:=h T θ w σ v t height hw hwm hσlo hσhi hh hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by have hd:=diagonalControl_nonneg Φ; positivity)
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.initial_affine_error_mono
