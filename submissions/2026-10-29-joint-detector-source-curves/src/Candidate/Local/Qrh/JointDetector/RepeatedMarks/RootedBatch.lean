/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseAllSlots
import Submissions.hailey_collet_1252270103.Cycle61.Density.ActualMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePhysical

/-! Literal rooted source data. These fields contain arithmetic identities,
source eligibility and support only. No moment or cardinality estimate is
included in this interface. The original slot Q is common to all zero labels. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentSecondHeightFamily CenteredMomentCommonMaskExpansion
open CenteredMomentDetectorEnergyInitialState CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

structure RootedBatch {Label Slot : Type*} (M : Ideal O) [NeZero M]
    (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (base anchor : Label→Character) (bad : Label→Ideal O)
    (W : ℝ→ℂ) (U Aroot : ℝ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  slots : Finset Slot
  widths : Slot→ℝ
  sigma : Slot→ℝ
  relativeHeight : Slot→ℝ
  commonHeight : ℝ
  Q : FreeRow→Slot→ℂ
  rays : Label→Slot→RayQuotient.Characters M H
  root : Label→Ideal O
  root_ne_zero : ∀ j,root j≠0
  root_norm : ∀ j,(root j).absNorm≤U^Aroot
  rowNorm : ∀ u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U
  embeddingNorm : ∀ u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤U
  widthsNonneg : ∀ s∈slots,0≤widths s
  sigmaLower : ∀ s∈slots,(33/50:ℝ)≤sigma s
  sigmaUpper : ∀ s∈slots,sigma s≤33/50
  idealCoefficients : ∀ u∈rows,∀ j I,idealCoeff (family u j) I=
    idealCoeff ((ProbeHighRowFamily.momentData (base j)).character (ProbeHighRowFamily.momentElement u)) I
  elementCoefficients : ∀ u∈rows,∀ j n,elementCoeff (family u j) n=
    rowTwist (HeckeRowClosure.elementHom (base j))
      (fixedBadMask*idealGenerator 1) 1 (1*u.val) n
  retained : ∀ u∈rows,∀ j,initialKeep (base j) (internalQ (bad j) (anchor j)) u.val
  plainIdentity : ∀ u∈rows,∀ j,∀ s∈slots,‖Q u s‖=
    ‖naturalSlot (excluded (family u j) (root j)) (primePool M H 2 (U^(widths s)))
      (fun I=>idealCoeff (relativeCharacter M H hH (anchor j) (rays j s)) I*
        HeckePrimeAnnular.annularWeight W (U^(widths s)) (sigma s)
          (commonHeight+relativeHeight s) I) (U^(widths s))‖
  inverseBase : Character
  inverseMask : O
  inverseAux : O
  inverseRoot : O
  inversePools : Slot→Finset (Ideal O)
  inverseCoefficients : Slot→Character
  inversePrime : ∀ s∈slots,∀ P∈inversePools s,Prime P
  inverseRatios : ∀ s∈slots,∀ P∈inversePools s,
    ((P.absNorm:ℝ)/U^(widths s))∈Icc (1:ℝ) 2
  inverseIdentity : ∀ u∈rows,∀ s∈slots,Q u s=
    normalizedSlot inverseBase inverseMask inverseAux (u.val*inverseRoot^6) (inversePools s)
      (fun I=>idealCoeff (inverseCoefficients s) I*
        HeckePrimeAnnular.annularWeight W (U^(widths s)) (sigma s)
          (relativeHeight s) I) commonHeight (U^(widths s))

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification

/-- Literal finite slot copies. Every copy keeps its original coefficients,
width, relative ray, root hole and natural zero. The source later charges
each selected copy separately. -/
def RootedBatch.copy {Label Slot : Type*} [DecidableEq Slot]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {U Aroot : ℝ}
    (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot) (K : ℕ) :
    RootedBatch (Slot:=Slot×Fin K) M H hH base anchor bad W U Aroot where
  rows := B.rows
  family := B.family
  slots := B.slots.product Finset.univ
  widths := fun s => B.widths s.1
  sigma := fun s => B.sigma s.1
  relativeHeight := fun s => B.relativeHeight s.1
  commonHeight := B.commonHeight
  Q := fun u s => B.Q u s.1
  rays := fun j s => B.rays j s.1
  root := B.root
  root_ne_zero := B.root_ne_zero
  root_norm := B.root_norm
  rowNorm := B.rowNorm
  embeddingNorm := B.embeddingNorm
  widthsNonneg := fun s hs => B.widthsNonneg s.1 (Finset.mem_product.mp hs).1
  sigmaLower := fun s hs => B.sigmaLower s.1 (Finset.mem_product.mp hs).1
  sigmaUpper := fun s hs => B.sigmaUpper s.1 (Finset.mem_product.mp hs).1
  idealCoefficients := B.idealCoefficients
  elementCoefficients := B.elementCoefficients
  retained := B.retained
  plainIdentity := fun u hu j s hs => B.plainIdentity u hu j s.1 (Finset.mem_product.mp hs).1
  inverseBase := B.inverseBase
  inverseMask := B.inverseMask
  inverseAux := B.inverseAux
  inverseRoot := B.inverseRoot
  inversePools := fun s => B.inversePools s.1
  inverseCoefficients := fun s => B.inverseCoefficients s.1
  inversePrime := fun s hs => B.inversePrime s.1 (Finset.mem_product.mp hs).1
  inverseRatios := fun s hs => B.inverseRatios s.1 (Finset.mem_product.mp hs).1
  inverseIdentity := fun u hu s hs => B.inverseIdentity u hu s.1 (Finset.mem_product.mp hs).1

end
end Qrh.JointDetector.RepeatedMarks
