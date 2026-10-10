import OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Cycle25.Assembly.Count.MomentDetectorPlainSlotProfile
import OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainCapacity Cycle25ProbeFinalAssembly
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {D:Cycle25.Weighted.MomentData}

theorem weighted_physical_annular_all (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
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

end SevenEighths.Cycle25CenteredMomentDetectorPlainCapacity

end

end OAI
