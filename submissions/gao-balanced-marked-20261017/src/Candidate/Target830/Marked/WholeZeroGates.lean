import Candidate.Cycle63.Marked.WholeRawGates
import Candidate.Target830.Marked.Density.NaturalEndpoint

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace OAI.SevenEighths.Marked830Plain
open Cycle63MarkedPlain HeckeFamily HeckeInverseAmplification HeckeDetectorZeros ProbePhysical LocalMoment
open ProbeHighRowFamily Cycle63Moment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
theorem whole_maximum_to_actual_zero_row (η η₀ χ : Character) (u : NonzeroFrequency)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀K,idealCoeff χ K=idealCoeff (excluded (naturalRow η u.val u.property).character R) K)
    (hχ : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1)
    (a T height : ℝ) (ha : 81/100≤ a) (hmax : a≤ zeroMaximum (wholeSourceFamily M H hH η₀ χ) hχ T)
    (hT : T≤ height) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)).data
      (fun _=>false) a height u := by
  obtain ⟨hc,he⟩ := whole_family_clean_maximum M H hH η η₀ χ u.val u.property R hR hcoeff hχ
  have hm := hmax.trans_eq (he T).symm
  obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained _ hc T (by linarith)
  apply Target830MarkedDensity.natural_zero_to_literal_dictionary _ (fun _=>false) a height ha u
  refine ⟨j,s,?_,?_,?_,ht.trans hT⟩
  · simpa only [Bool.false_eq_true,ite_false,naturalRawFamily,cleanWholeBase] using hz
  · exact Or.inr (hc j)
  · rw [hs];exact hm


end OAI.SevenEighths.Marked830Plain
#print axioms OAI.SevenEighths.Marked830Plain.whole_maximum_to_actual_zero_row
