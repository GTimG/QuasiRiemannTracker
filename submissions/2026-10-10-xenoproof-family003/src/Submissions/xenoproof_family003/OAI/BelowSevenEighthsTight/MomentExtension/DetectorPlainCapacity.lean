/- UNVERIFIED adapters retaining original physical plain moment objects. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {Δ total margin recordMesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}

theorem physical_annular_all_retuned (S:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

end SevenEighths.CenteredMomentDetectorPlainCapacity

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainCapacity.physical_annular_all_retuned
