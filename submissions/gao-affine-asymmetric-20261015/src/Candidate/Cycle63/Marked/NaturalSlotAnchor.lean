import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentExceptionalPair
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Moving a fixed dictionary twist from the row character to the relative
anchor preserves every prime coefficient after deleting its fixed conductor. -/
theorem shifted_anchor_coefficient (η η₀ ν : Character) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff G.character I*idealCoeff (relativeCharacter M H hH (η₀.product ν) θ) I=
      idealCoeff (excluded F.character ν.modulus) I*
        idealCoeff (relativeCharacter M H hH η₀ θ) I := by
  rw [G.ideal,excluded_ideal _ _ ν.modulus_ne_bot,F.ideal]
  by_cases hI : I=0
  · subst I
    simp only [show (⊥ : Ideal O)=0 from rfl,map_zero,zero_mul,ite_self]
  by_cases hc : IsCoprime I ν.modulus
  · rw [if_pos hc]
    have hn := HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime ν I hI hc
    simp only [relativeCharacter_ideal,idealCoeff_product,
      HeckeDetectorRelativePrime.idealCoeff_inverse,mul_inv_rev]
    field_simp
  · rw [if_neg hc,zero_mul]
    have hn : idealCoeff ν I=0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff ν I).mp hn).2
    simp only [idealCoeff_product,hn,mul_zero,zero_mul]

/-- Exact natural-slot form of the fixed-anchor transfer; it is uniform over
all pools, profiles and frequencies. -/
theorem shifted_anchor_slot (η η₀ ν : Character) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (pool : Finset (Ideal O))
    (weight : Ideal O→ℂ) (P : ℝ) :
    naturalSlot G.character pool
      (fun I=>idealCoeff (relativeCharacter M H hH (η₀.product ν) θ) I*weight I) P=
    naturalSlot (excluded F.character ν.modulus) pool
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*weight I) P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simpa only [←mul_assoc] using congrArg (fun c : ℂ=>c*weight I)
    (shifted_anchor_coefficient M H hH η η₀ ν u F G θ I)

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.shifted_anchor_slot
