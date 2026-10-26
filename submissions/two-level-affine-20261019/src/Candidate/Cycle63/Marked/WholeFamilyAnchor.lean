import Candidate.Cycle63.Moment.WholeSourceFamily
import Candidate.Cycle63.Marked.NaturalSlotAnchor

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion Cycle63Moment

/-- A fixed ideal records primes at which every row coefficient vanishes. -/
def Avoids (χ : Character) (R : Ideal O) : Prop :=
  ∀ I : Ideal O, ¬IsCoprime I R → idealCoeff χ I=0

theorem excluded_avoids (η : Character) (R : Ideal O) (hR : R≠0) :
    Avoids (excluded η R) R := by
  intro I hI
  rw [excluded_ideal _ _ hR,ite_eq_right hI]

theorem avoids_product {η : Character} {R : Ideal O} (hη : Avoids η R) (ν : Character) :
    Avoids (η.product ν) R := by
  intro I hI
  rw [idealCoeff_product,hη I hI,zero_mul]

theorem avoids_natural {η : Character} {R : Ideal O} (hη : Avoids η R)
    {u : O} (F : NaturalRow η u) : Avoids F.character R := by
  intro I hI
  rw [F.ideal,hη I hI,zero_mul]

theorem avoids_excluded_redundant {χ : Character} {R : Ideal O} (hχ : Avoids χ R)
    (S : Ideal O) (hS : S≠0) (hSR : S∣R) (I : Ideal O) :
    idealCoeff (excluded χ S) I=idealCoeff χ I := by
  rw [excluded_ideal _ _ hS]
  by_cases hc : IsCoprime I S
  · exact ite_eq_left hc
  · rw [ite_eq_right hc]
    exact (hχ I (fun h=>hc (h.of_isCoprime_of_dvd_right hSR))).symm

theorem avoids_slot_excluded_redundant {χ : Character} {R : Ideal O} (hχ : Avoids χ R)
    (S : Ideal O) (hS : S≠0) (hSR : S∣R)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (excluded χ S) pool β P=naturalSlot χ pool β P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [avoids_excluded_redundant hχ S hS hSR]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

abbrev RayPair := RayQuotient.Characters M H × RayQuotient.Characters M H

def firstTwist (η₀ : Character) (j : RayPair M H) : Character :=
  (relativeCharacter M H hH η₀ j.1).inverse.inverse

def secondTwist (j : RayPair M H) : Character := HeckeRayQuotient.character M H hH j.2

/-- This ideal is fixed before the scale and the chosen zero label. -/
def wholeAnchorMask (η₀ : Character) : Ideal O :=
  ∏j : RayPair M H,(firstTwist M H hH η₀ j).modulus*(secondTwist M H hH j).modulus

theorem wholeAnchorMask_ne_zero (η₀ : Character) : wholeAnchorMask M H hH η₀≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact mul_ne_zero (firstTwist M H hH η₀ j).modulus_ne_bot (secondTwist M H hH j).modulus_ne_bot

theorem firstTwist_divides_mask (η₀ : Character) (j : RayPair M H) :
    (firstTwist M H hH η₀ j).modulus∣wholeAnchorMask M H hH η₀ :=
  (dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

theorem secondTwist_divides_mask (η₀ : Character) (j : RayPair M H) :
    (secondTwist M H hH j).modulus∣wholeAnchorMask M H hH η₀ :=
  (dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

def wholeSourceAnchor (η₀ : Character) : WholeSourceIndex M H→ Character :=
  Sum.elim (fun _=>η₀) (fun j=>(η₀.product (firstTwist M H hH η₀ j)).product (secondTwist M H hH j))

/-- Every member of the actual whole zero family uses the same marked slot
amplitude. The fixed anchor changes with its zero label, while its common
slot base has one fixed conductor deletion. -/
theorem whole_family_common_slot (η η₀ : Character) (u : O) (hu : u≠0)
    (j : WholeSourceIndex M H) (θ : RayQuotient.Characters M H)
    (pool : Finset (Ideal O)) (weight : Ideal O→ℂ) (P : ℝ) :
    let base := excluded η (wholeAnchorMask M H hH η₀)
    naturalSlot (naturalRow (wholeSourceBase M H hH η₀ base j) u hu).character pool
      (fun I=>idealCoeff (relativeCharacter M H hH (wholeSourceAnchor M H hH η₀ j) θ) I*weight I) P=
    naturalSlot (naturalRow base u hu).character pool
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  intro base
  have hb : Avoids base (wholeAnchorMask M H hH η₀) :=
    excluded_avoids η _ (wholeAnchorMask_ne_zero M H hH η₀)
  cases j with
  | inl j => rfl
  | inr j =>
    let ν₁ := firstTwist M H hH η₀ j
    let ν₂ := secondTwist M H hH j
    let F := naturalRow base u hu
    let G := naturalRow (base.product ν₁) u hu
    let K := naturalRow ((base.product ν₁).product ν₂) u hu
    change naturalSlot K.character pool
      (fun I=>idealCoeff (relativeCharacter M H hH ((η₀.product ν₁).product ν₂) θ) I*weight I) P=_
    rw [shifted_anchor_slot M H hH (base.product ν₁) (η₀.product ν₁) ν₂ u G K θ]
    rw [avoids_slot_excluded_redundant (avoids_natural (avoids_product hb ν₁) G)
      ν₂.modulus ν₂.modulus_ne_bot (secondTwist_divides_mask M H hH η₀ j)]
    rw [shifted_anchor_slot M H hH base η₀ ν₁ u F G θ]
    exact avoids_slot_excluded_redundant (avoids_natural hb F)
      ν₁.modulus ν₁.modulus_ne_bot (firstTwist_divides_mask M H hH η₀ j) _ _ _

end
end OAI.SevenEighths.Cycle63MarkedPlain
