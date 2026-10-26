import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical SchwartzMap
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- A fixed parent has no moving anchor. The existing state API records the
fixed conductor by its exact logarithmic width rather than setting it to zero. -/
def fixedParentState (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ Z M : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) : NaturalState Z 0 bΦ where
  character := η
  fixedModulus := Q
  puncture := 1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := Z^M
    scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    nonneg := fun _ => hp _ }
  rowWidth := M
  characterWidth := Real.logb Z (η.modulus.absNorm : ℝ)
  base_ge_one := hZ.le
  row_nonneg := hM
  character_nonneg := Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
  scale_eq := rfl
  modulus_bound := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))]
  puncture_ne_zero := one_ne_zero
  puncture_bound := by simp
  radial_support := hs
  row_ne_zero := fun _ h => h.1
  nonexceptional := fun _ h => h.2

theorem fixedParentState_width (η : Character) (Q : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (bΦ Z M : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ)
    (hp : ∀ x, 0 ≤ (Φ x).re) :
    (fixedParentState η Q Φ bΦ Z M hZ hM hs hp).width =
      M + Real.logb Z (η.modulus.absNorm : ℝ) := rfl

/-- One scale threshold works for the fixed finite anchor dictionary and
every row width above a fixed positive lower bound, before any live heights. -/
theorem fixed_anchor_width_uniform {Label : Type*} [Fintype Label]
    (η : Label → Character) (Mmin ε : ℝ) (hMmin : 0 < Mmin) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ j : Label, ∀ M : ℝ, Mmin ≤ M →
      Real.logb Z ((η j).modulus.absNorm : ℝ) ≤ ε*M := by
  have hfixed (j : Label) : ∀ᶠ Z : ℝ in atTop,
      ((η j).modulus.absNorm : ℝ) ≤ Z^(ε*Mmin) :=
    (tendsto_rpow_atTop (mul_pos hε hMmin)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr hfixed, eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ, ?_⟩
  intro j M hM
  have hn : 0 < ((η j).modulus.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (η j).modulus_ne_bot)
  apply (Real.logb_le_iff_le_rpow hZ hn).mpr
  exact (hz j).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (mul_le_mul_of_nonneg_left hM hε.le))

theorem fixedParentState_twists
    (rayModulus : Ideal O) [NeZero rayModulus]
    (H : Subgroup (O ⧸ rayModulus)ˣ)
    (hH : RayOrthogonality.globalUnits rayModulus ≤ H)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q ≤ rayModulus)
    (hQη : Q ≤ η₀.modulus) (z : O)
    (hz : initialKeep η Q z) :
    ∀ θ : RayQuotient.Characters rayModulus H,
      ((naturalRow η z hz.1).character.product
        (relativeCharacter rayModulus H hH η₀ θ)).residue ≠ 1 := by
  intro θ
  exact sector_nonprincipal rayModulus H hH (naturalRow η z hz.1)
    η₀ θ Q 1 hQM hQη one_ne_zero hz.1 hz.2

#print axioms fixedParentState
#print axioms fixed_anchor_width_uniform
#print axioms fixedParentState_twists
end
end OAI.SevenEighths.Cycle61Moment
