import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.Route.ActualMarkedGates
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.AnnularPool
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualWeighted
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles
open DetectorDictionaryInverseRawInitialGates LocalMoment Cycle63MarkedAssembly Cycle63ActualMarked
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentDetectorPlainFiberSource
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition HeckeDetectorWitnessRows
local notation "O" => HeckeFamily.O
variable {Label Slot : Type} [Fintype Label] [Nonempty Label] [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance actualWeightedCountFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Literal finite source data. The two representations identify the same
amplitude with the annular inverse pool and the canonical plain source pool;
no moment estimate is included among the fields. -/
structure NaturalBatch (base anchor : Label→ Character) (bad : Label→ Ideal O)
    (W : ℝ→ℂ) (lo hi U : ℝ) where
  rows : Finset FreeRow
  family : FreeRow→Label→ Character
  slots : Finset Slot
  widths : Slot→ℝ
  sigma : Slot→ℝ
  relativeHeight : Slot→ℝ
  commonHeight : FreeRow→ℝ
  Q : FreeRow→Slot→ℂ
  rays : Label→Slot→RayQuotient.Characters M H
  inversePools : Slot→Finset (Ideal O)
  inverseBase : Character
  inverseCoefficients : Slot→ Character
  widthsPositive : ∀s∈slots,0<widths s
  sigmaLower : ∀s∈slots,lo≤ sigma s
  sigmaUpper : ∀s∈slots,sigma s≤hi
  rowNorm : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U
  embeddingNorm : ∀u∈rows,‖eisEmbedding u.val‖^2≤U
  idealCoefficients : ∀u∈rows,∀j I,idealCoeff (family u j) I=
    idealCoeff ((momentData (base j)).character (momentElement u)) I
  elementCoefficients : ∀u∈rows,∀j n,elementCoeff (family u j) n=
    rowTwist (HeckeRowClosure.elementHom (base j))
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (1*u.val) n
  retained : ∀u∈rows,∀j,initialKeep (base j) (internalQ (bad j) (anchor j)) u.val
  inversePrime : ∀s∈slots,∀P∈inversePools s,Prime P
  inverseRatios : ∀s∈slots,∀P∈inversePools s,((P.absNorm:ℝ)/U^(widths s))∈Icc (1:ℝ) 2
  inverseLarge : ∀s∈slots,∀j,((deletedBase (momentData (base j))).modulus.absNorm:ℝ)<U^(widths s)
  inverseIdentity : ∀u∈rows,∀s∈slots,Q u s=
    naturalSlot (naturalRow inverseBase u.val u.property.1).character (inversePools s)
      (fun I=>idealCoeff (inverseCoefficients s) I*HeckePrimeAnnular.annularWeight W (U^(widths s))
        (sigma s) (commonHeight u+relativeHeight s) I) (U^(widths s))
  plainIdentity : ∀u∈rows,∀j,∀s∈slots,Q u s=
    naturalSlot (family u j) (primePool M H 2 (U^(widths s)))
      (fun I=>idealCoeff (relativeCharacter M H hH (anchor j) (rays j s)) I*
        HeckePrimeAnnular.annularWeight W (U^(widths s)) (sigma s)
          (commonHeight u+relativeHeight s) I) (U^(widths s))

/-- Restricting the live slot set preserves all literal source certificates. -/
def NaturalBatch.restrictSlots {base anchor : Label→ Character} {bad : Label→ Ideal O}
    {W : ℝ→ℂ} {lo hi U : ℝ}
    (B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U)
    (selected : Finset Slot) (hs : selected⊆B.slots) :
    NaturalBatch (Slot:=Slot) M H hH base anchor bad W lo hi U :=
  { B with
    slots := selected
    widthsPositive := fun s h=>B.widthsPositive s (hs h)
    sigmaLower := fun s h=>B.sigmaLower s (hs h)
    sigmaUpper := fun s h=>B.sigmaUpper s (hs h)
    inversePrime := fun s h=>B.inversePrime s (hs h)
    inverseRatios := fun s h=>B.inverseRatios s (hs h)
    inverseLarge := fun s h=>B.inverseLarge s (hs h)
    inverseIdentity := fun u hu s h=>B.inverseIdentity u hu s (hs h)
    plainIdentity := fun u hu j s h=>B.plainIdentity u hu j s (hs h) }

end OAI.SevenEighths.Cycle63ActualWeighted

end
end Record1252270103Bootstrap.PR67
