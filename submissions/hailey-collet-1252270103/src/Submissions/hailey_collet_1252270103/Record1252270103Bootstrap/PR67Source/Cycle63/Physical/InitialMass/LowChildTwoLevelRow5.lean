import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildTwoLevelFixed
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSelectedJoined
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The selected low frequency columns of the final daughters of the LOW children of the first step of the two-level
ledger: the wrapper of the final daughter with the generic rows 1-4, joined with the returned parts of the second step.
Released under Apache 2.0. -/
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

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Row 5 of the first step of the two-level ledger: the selected low frequency columns of the final daughters of the
LOW children are paid by the finite supported label budget, with the allowance of the labels and the returned HIGH
parts of the second step. This is `LowSelectedStmt` for the units `unit = 1`, the frequency losses at most `ωmax`, the
exponent `lowSideExponent` of the labels and the presentation `Presented` of the children, from
`two_level_low_fixed_columns` (the wrapper of the final daughter with the rows 1-4, at rate `q/(6 slotPrice)` and
reflection loss `εR`) and `lowSelectedStmt_joined` (the old part with the allowance and the returned parts). The
hypotheses besides those of the wrapper are the facts of the first level that pay the returned parts (`hfacts`), the
range `0 ≤ Tz ≤ Z^τT` of the zero height of `Presented` (`hPres`), the smallness `J τT ≤ εlabels/6` of the degree `J`
of the height (`hJτ`), and the absorption of the rate and of the reflection loss in the rate `lowRate` of the ledger
(`hrate`, `hεX`: for example `εR = (lowRate - q/(6 slotPrice)) εpad Mmin`, which is positive when the price of the
ledger is below `slotPrice`). The second step `stepTwo` serves the children presented by `Presented` whose multipliers
have norm at most `Z^(Mcap + 5 Bnorm + ε + 1)`, and its returned records have the label cap `Bret ≥ Bnorm`. -/
theorem lowSelectedStmt_two_level [IsTwoLevelFirstStep Cycle63.Arithmetic.firstLevelLedger] {α : Type} [Fintype α]
    [DecidableEq α] {Base : Type} [Fintype Base]
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
    (N G : ℕ) (Cs supply εv Bnorm εlabels ωmax ξR δR εR lossFloor gridSlack ampSlack : ℝ) (hCs : 1≤Cs)
    (hsupply : 0<supply) (hev : 0<εv) (hBnorm : 0≤Bnorm) (hel : 0<εlabels)
    (hξR : 0<ξR) (hδR : 0≤δR) (hεR : 0<εR) (hL1 : 1≤L)
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (base : Character → Base → Character)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) (Bret : ℝ) (hBret : Bnorm≤Bret)
    (stepTwo : SecondStepReturnAt (α:=α) M H hH base W B a b 2 Bmask L Lslot lo hi Mcap εold Bret
      (SecondApplicable G lossFloor
        (fun η Z s v T => Presented η Z s v T ∧ ((Ideal.span {v}).absNorm:ℝ)≤Z^(Mcap+5*Bnorm+ε+1))))
    (τT : ℝ) (hPres : ∀ η Z (st : NaturalState Z Bmask 2) v Tz, Presented η Z st v Tz → 0≤Tz ∧ Tz≤Z^τT)
    (hJτ : (returnedHeightDegree Base M H hH Bret (εlabels/6) (εlabels/(6*(3+4*Bret))) : ℝ)*τT ≤ εlabels/6)
    (hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)≤Cycle63.AffineLedger.lowRate)
    (hεX : εR≤(Cycle63.AffineLedger.lowRate-Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice))*(εpad*Mmin))
    (hfacts : LowReturnedFactsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad
      Mmin εshell N Cs supply εv Bnorm εlabels (fun u om _ => u=1 ∧ om≤ωmax) lowSideExponent Presented lossFloor
      gridSlack ampSlack) :
    LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N
      Cs supply εv Bnorm εlabels (fun u om _ => u=1 ∧ om≤ωmax) lowSideExponent Presented :=
  lowSelectedStmt_joined (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
    εshell hep.le heshell.le N Cs supply εv Bnorm εlabels hsupply hev hBnorm hel ωmax
    (Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)) εR base lossFloor gridSlack ampSlack Presented Bret hBret
    τT hPres hJτ hrate hεX
    (two_level_low_fixed_columns (α:=α) M H hH W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask
      hMcap hεold hLslot hbeta Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd
      hdsupply hdm bs εwidth εpad Mmin εshell hbs hew hep hmin heshell N G Cs ωmax ξR δR εR lossFloor gridSlack
      ampSlack Bret hCs hξR hδR hεR hL1 hcert base
      (fun η Z s v T => Presented η Z s v T ∧ ((Ideal.span {v}).absNorm:ℝ)≤Z^(Mcap+5*Bnorm+ε+1)) stepTwo)
    hfacts

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
