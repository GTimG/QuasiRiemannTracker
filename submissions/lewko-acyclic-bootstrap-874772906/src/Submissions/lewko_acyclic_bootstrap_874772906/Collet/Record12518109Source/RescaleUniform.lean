/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Source.Rescale
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace QRH.Record12518109Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot Filter
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)


/-- The threshold and controls are uniform on a fixed positive interval of
root exponents. Constants remain fixed before all live rows and heights. -/
theorem initialAffineAt_uniform_rescale (face : SourceFace) (W : ℝ→ℂ)
    (bslot a b bΦ mesh unitMesh σlo σhi Mmin Mmax ε unitε : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ)
    (hMmin : 0<Mmin) (hC : 0≤C) (hunitMesh : 0≤unitMesh)
    (hmesh : mesh≤unitMesh*Mmin) (hunitε : 0≤unitε)
    (hε : Mmax*unitε≤ε)
    (hsource : ∀ᶠU : ℝ in atTop,
      InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ unitMesh
        σlo σhi 1 1 unitε U η η₀ Q degree S C) :
    ∀ᶠZ : ℝ in atTop,
      InitialAffineAt (α:=α) rayM H hH face W bslot a b bΦ mesh
        σlo σhi Mmin Mmax ε Z η η₀ Q degree S C := by
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hsource
  filter_upwards [(tendsto_rpow_atTop hMmin).eventually (eventually_ge_atTop U₀),
    eventually_gt_atTop (1:ℝ)] with Z hscale hZ
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm
  have hM : 0<M := hMmin.trans_le hMlo
  have hsrc := hU₀ (Z^M)
    (hscale.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hMlo))
  have hfixed := initialAffineAt_rescale (α:=α) rayM H hH face W
    bslot a b bΦ mesh unitMesh σlo σhi M ε unitε Z η η₀ Q degree S C
    hZ hM hC (hmesh.trans (mul_le_mul_of_nonneg_left hMlo hunitMesh))
    ((mul_le_mul_of_nonneg_right hMhi hunitε).trans hε) hsrc
  exact hfixed T θ w σ v t height hw hwm hσlo hσhi hh hv M le_rfl le_rfl
    Φ hΦ hpΦ p X₁ X₂ hX₁ hX₂ hadm
end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.initialAffineAt_uniform_rescale
