/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.GeometryMask
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.ClippedProfiles

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option quotPrecheck false

namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic ConcreteTraceCRT
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentNaturalRowSource CenteredMomentFirstPhysicalSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCommonRadialData CenteredExceptionalProfile
open CenteredMomentDetectorEnergyInitialState Cycle61InitialMass
local notation "O" => HeckeFamily.O

section Actual
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (reflected : Bool) (η₀ : Character) (u₀ : O)
  (F₀ : NaturalRow η₀ u₀) (R₀ : Ideal O) (hu₀ : u₀ ≠ 0)
  (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1 < Z) (bin : ℤ × (Fin 5 → ℤ))
  (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
  (hw₁ : s.W₁ 0 = 0) (hw₂ : s.W₂ 0 = 0)
  (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q)
local notation "datum" => geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n
local notation "Kpos" => (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow)
local notation "firstLabel" => geometryFirstLabel s R seed (Z^Mrow) Z ξ Kpos bin q.1.val
local notation "unitMap" => (fun l => (firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l : O))
local notation "baseRay" => geometryDictionaryRay reflected s R seed (Z^Mrow) Z ξ Kpos bin q.1.val

local notation "rawKey" => geometryLowRawKey reflected η₀ u₀ F₀ R₀ hu₀ s R seed Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n

/-- The literal retained second-row product is controlled by one common
original profile pair on the actual reconstructed raw row. The moving mask is
reduced using the actual geometry constructor, and clipping is removed by its
whole-product normalization inequality. This holds in both orientations. -/
theorem actual_geometry_low_retained_common_profile
    (hη : s.η = excluded F₀.character R₀) (hR : R ≠ 0)
    (r : secondLiveRows (fun _ : Unit => (datum).block)) (second : Bool) (ψ : RayCharacter)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a₁ b₁ : ℝ) (ha₁ : 0 < a₁)
    (hs₁ : Function.support (W₁ : ℝ→ℂ) ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support (W₂ : ℝ→ℂ) ⊆ Set.Icc a₁ b₁)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i, 0 < P i) (height X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    let key := rawKey r second
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let puncture := (datum).R * (if second then (datum).D else (datum).C)
    let commonMask := geometryRawFixedMask s R * firstSourceMissing (!reflected) firstLabel
    let Fraw := naturalRow (secondFixedDictionary η₀ (baseRay, ψ))
      (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property
    ‖CenteredMomentRetainedEnergy.retainedPositiveRow ((datum).τ ψ)
      (fixedBadMask*idealGenerator puncture) 1 z W₁ W₂ pool β P height X₁ X₂‖^2 ≤
    ‖HeckeDyadic.polynomial (excluded Fraw.character commonMask) false
        (CenteredMomentLattice.normPowerProfile W₁ a₁ b₁ ha₁ hs₁ (W₁.smooth ⊤) height) X₁ 0 0 *
      HeckeDyadic.polynomial (excluded Fraw.character commonMask) false
        (CenteredMomentLattice.normPowerProfile W₂ a₁ b₁ ha₁ hs₂ (W₂.smooth ⊤) height) X₂ 0 0 *
      ∏ i, CenteredMomentCommonMaskExpansion.naturalSlot (excluded Fraw.character commonMask)
        (pool i) (CenteredMomentCommonMaskEnergy.heightCoefficient (β i) height) (P i)‖^2 := by
  intro key z puncture commonMask Fraw
  have hz : z ≠ 0 := by
    cases second
    · exact (datum).rows_ne _ r.val.2.2.2.property
    · exact neg_ne_zero.mpr ((datum).rows_ne _ r.val.2.2.2.property)
  have hp := actual_geometry_low_second_puncture reflected s R seed Z Mrow amp ξ reserve
    b t N hZ bin q hw₁ hw₂ n hR second
  have hm := actual_geometry_low_common_mask reflected η₀ u₀ F₀ R₀ hu₀ s R seed
    Z Mrow amp ξ reserve b t N hZ bin q hw₁ hw₂ n hη hR r second ψ
  have he := retained_natural_common_profile (naturalRow ((datum).τ ψ) z hz)
    puncture hp W₁ W₂ a₁ b₁ ha₁ hs₁ hs₂ pool β P hP height X₁ X₂ hX₁ hX₂
  have hcoeff : ∀ I : Ideal O,
      idealCoeff (excluded (naturalRow ((datum).τ ψ) z hz).character puncture) I =
      idealCoeff (excluded Fraw.character commonMask) I := hm.2
  have hpoly := HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff
    (excluded (naturalRow ((datum).τ ψ) z hz).character puncture)
    (excluded Fraw.character commonMask) hcoeff
  have hslot (i : ι) :
      CenteredMomentCommonMaskExpansion.naturalSlot
        (excluded (naturalRow ((datum).τ ψ) z hz).character puncture)
        (pool i) (CenteredMomentCommonMaskEnergy.heightCoefficient (β i) height) (P i) =
      CenteredMomentCommonMaskExpansion.naturalSlot (excluded Fraw.character commonMask)
        (pool i) (CenteredMomentCommonMaskEnergy.heightCoefficient (β i) height) (P i) := by
    simp only [CenteredMomentCommonMaskExpansion.naturalSlot,hcoeff]
  simpa only [hpoly,hslot] using he

end Actual
end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.actual_geometry_low_retained_common_profile
