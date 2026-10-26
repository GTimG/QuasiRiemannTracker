import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.WholeNaturalBatch
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.WholeFamilyMaximum
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualWitnesses
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionMaxAmplitude
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle63Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def wholeCleanFamily (η η₀ : Character) (u : FreeRow) : WholeSourceIndex M H→ Character :=
  fun j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character

def wholeCleanSlot {Slot : Type} (η η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (w σ v : Slot→ℝ) (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (u : FreeRow) (s : Slot) : ℂ :=
  naturalSlot (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
    (primePool M H 2 (U^(w s)))
    (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
