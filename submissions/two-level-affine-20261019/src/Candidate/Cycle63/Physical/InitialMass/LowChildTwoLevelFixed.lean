/- The bound of the normalized columns of one final daughter of a first-level LOW child with the second step, with the
fixed source-profile factors extracted: the wrapper of the final daughter composed with the generic rows 1-4. Released
under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildTwoLevel
import Candidate.Cycle63.Physical.InitialMass.LowChildColumns

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCompleteCommon CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalLedger
open CenteredMomentRankinRadical CenteredMomentPartitionNorm CenteredMomentFirstMixedRoot
open CenteredMomentFirstSourceConductorCaps CenteredMomentSecondMovingSupport CenteredMomentSupport
open CenteredMomentFirstCanonicalFamily
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity CenteredMomentEnergyInputParentCapacity

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The bound of the normalized columns of one final daughter of a first-level LOW child with the second step, with the
fixed source-profile factors `2 b² Cs^(4N)` extracted: `LowFixedColumnsStmt` for the units `unit = 1`, the frequency
losses at most `ωmax`, the rate `q/(6 slotPrice)` of the padding, the reflection loss `εR`, the allowance `lowAllowance`
of the labels and the returned part of the second step. It is `two_level_low_profiles` (the bound with the original
plain profiles of the class `(a, b)`), composed with `lowCommon_of_profiles`, `lowColumn_of_common` and
`lowFixedColumns_of_column`. The second step is `stepTwo` at the class `(a, b)` of the original plain profiles. The
bound `N` of the number of slots is not the grid of the second step: the grid has mesh `1/G`. -/
theorem two_level_low_fixed_columns [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger] {Base : Type}
    (W : ℝ→ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hLslot : Lslot≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin εshell : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin) (heshell : 0<εshell)
    (N G : ℕ) (Cs ωmax ξR δR εR lossFloor gridSlack ampSlack Bnorm : ℝ) (hCs : 1≤Cs)
    (hξR : 0<ξR) (hδR : 0≤δR) (hεR : 0<εR) (hL1 : 1≤L)
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (base : Character → Base → Character)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (stepTwo : SecondStepReturnAt (α:=α) M H hH base W B a b 2 Bmask L Lslot lo hi Mcap εold Bnorm
      (SecondApplicable G lossFloor Presented)) :
    LowFixedColumnsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs
      (fun u om _ => u=1 ∧ om≤ωmax) True (Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)) εR
      (fun Z C₁ D₁ C₂ D₂ E₂ => lowAllowance Z C₁ D₁ C₂ D₂ E₂) base Bnorm lossFloor gridSlack ampSlack Presented := by
  have hprofiles := two_level_low_profiles (α:=α) M H hH W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB
    ha ha' hb hBmask hMcap hεold hLslot hbeta Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget
    hmargin hd hdsupply hdm bs εwidth εpad Mmin hbs hew hep hmin G ωmax ξR δR εR lossFloor gridSlack ampSlack Bnorm
    hξR hδR hεR hL1 hcert base Presented stepTwo
  exact lowFixedColumns_of_column (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth
    εpad Mmin εshell N Cs _ _ _ _ _ base Bnorm lossFloor gridSlack ampSlack Presented hCs hb
    (lowColumn_of_common (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell
      _ _ _ _ _ base Bnorm lossFloor gridSlack ampSlack Presented heshell
      (lowCommon_of_profiles (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
        _ _ _ _ _ base Bnorm lossFloor gridSlack ampSlack Presented εshell heshell hprofiles))

end
end OAI.SevenEighths.Cycle63InitialMass
