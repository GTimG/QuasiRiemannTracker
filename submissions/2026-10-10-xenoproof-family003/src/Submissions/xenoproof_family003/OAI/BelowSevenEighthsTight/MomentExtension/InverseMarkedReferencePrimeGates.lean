/- UNVERIFIED adapters of original physical inverse moment estimates. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.DetectorMomentPrimeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O

theorem deleted_source_live_prime_retuned {Δ total margin mesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin mesh}
    (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact ProbeHighRowFamily.sourceMoment_primeProfile_norm_retuned F X ζ hζ P

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI

#print axioms OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.deleted_source_live_prime_retuned
