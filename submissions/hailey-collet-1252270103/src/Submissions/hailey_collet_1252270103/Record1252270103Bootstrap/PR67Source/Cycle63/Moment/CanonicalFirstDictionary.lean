import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.CanonicalFirstSigned
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ChildRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstColumns CenteredMomentFixedRay
open CenteredMomentChildRows
open RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The table varies with live labels; the sixteen-character index set does not. -/
def firstPhaseTable (C D : Ideal O) (t : ActiveIndex C D → ℕ) (r : RayRing) : ℂ :=
  ∏ P, (QuadraticAllOddCRT.quadraticRaySign
    (ActualEisensteinCoordinates.residue (firstSignedPrime C D P))
    (QuadraticGaussRay.residueQuotientFour r) : ℂ)^(t P)

theorem firstPhaseTable_mk (C D : Ideal O) (t : ActiveIndex C D → ℕ) (n : O) :
    firstPhaseTable C D t (Ideal.Quotient.mk _ n) =
      ∏ P, sexticReciprocityPhase (firstSignedPrime C D P) n^(t P) := by
  simp only [firstPhaseTable, sexticReciprocityPhase,
    QuadraticGaussRay.residueQuotientFour_mk]

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
