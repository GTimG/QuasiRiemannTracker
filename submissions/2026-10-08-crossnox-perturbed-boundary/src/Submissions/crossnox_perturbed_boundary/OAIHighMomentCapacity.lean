/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighMomentCapacity.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.crossnox_perturbed_boundary.OAIHighMomentSlotProfile

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.PerturbedMomentTransport
open CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {gap:ℝ}{D:Parameters.PerturbedHighData gap}

theorem physical_annular_all (S:ProbeFinalAssembly.PerturbedSourceData D)(η₀:Character)
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

end SevenEighths.PerturbedMomentTransport

end

end OAI
