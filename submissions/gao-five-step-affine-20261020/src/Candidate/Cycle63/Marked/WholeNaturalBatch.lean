import Candidate.Cycle63.Marked.Route.ActualWeightedCount
import Candidate.Cycle63.Marked.WholeFamilyZeros

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Set HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState Cycle63Moment

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def cleanWholeBase (η η₀ : Character) : WholeSourceIndex M H→ Character :=
  wholeSourceBase M H hH η₀ (excluded η (wholeAnchorMask M H hH η₀))

theorem natural_initial_element (η : Character) (u : O) (hu : u≠0) (n : O) :
    elementCoeff (naturalRow η u hu).character n=
      CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (1*u) n := by
  have hh:=(naturalRow η u hu).masked_element 1 one_ne_zero n
  rw [excluded_element _ (naturalRow η u hu).element_zero 1 one_ne_zero,
    ite_eq_left (isCoprime_one_right)] at hh
  simpa only [one_mul] using hh

/-- The actual common relative-ray amplitudes give the literal source batch
for every member of the whole zero family. The fixed conductor mask is
independent of the moving rows and of their selected zero labels. -/
def wholeNaturalBatch {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→ Ideal O)
    (W : ℝ→ℂ) (lo hi U : ℝ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (rows : Finset FreeRow) (slots : Finset Slot) (w σ v : Slot→ℝ)
    (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (hw : ∀s∈slots,0<w s) (hσlo : ∀s∈slots,lo≤σ s) (hσhi : ∀s∈slots,σ s≤hi)
    (hrow : ∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U)
    (hnorm : ∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤U)
    (hkeep : ∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val)
    (hlarge : ∀s∈slots,∀j,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<U^(w s)) :
    Cycle63ActualWeighted.NaturalBatch (Slot:=Slot) M H hH (cleanWholeBase M H hH η η₀)
      (wholeSourceAnchor M H hH η₀) bad W lo hi U where
  rows:=rows
  family:=fun u j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character
  slots:=slots
  widths:=w
  sigma:=σ
  relativeHeight:=v
  commonHeight:=t
  Q:=fun u s=>naturalSlot
    (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
      (primePool M H 2 (U^(w s)))
      (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))
  rays:=fun _=>θ
  inversePools:=fun s=>annularPool (primePool M H 2 (U^(w s))) (U^(w s))
  inverseBase:=excluded η (wholeAnchorMask M H hH η₀)
  inverseCoefficients:=fun s=>relativeCharacter M H hH η₀ (θ s)
  widthsPositive:=hw
  sigmaLower:=hσlo
  sigmaUpper:=hσhi
  rowNorm:=hrow
  embeddingNorm:=hnorm
  idealCoefficients:=by
    intro u hu j I
    exact natural_raw_coefficients _ (momentElement u) I
  elementCoefficients:=by
    intro u hu j n
    exact natural_initial_element _ u.val u.property.1 n
  retained:=hkeep
  inversePrime:=by
    intro s hs I hI
    exact (Finset.mem_filter.mp (annularPool_subset _ _ hI)).2.1
  inverseRatios:=fun s hs I hI=>annularPool_ratio _ _ _ hI
  inverseLarge:=hlarge
  inverseIdentity:=by
    intro u hu s hs
    exact (naturalSlot_annular_filter _ _ _ W hWs _ _ _).symm
  plainIdentity:=by
    intro u hu j s hs
    exact (whole_family_common_slot M H hH η η₀ u.val u.property.1 j (θ s)
      (primePool M H 2 (U^(w s)))
      (fun I=>HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))).symm

end
end OAI.SevenEighths.Cycle63MarkedPlain
