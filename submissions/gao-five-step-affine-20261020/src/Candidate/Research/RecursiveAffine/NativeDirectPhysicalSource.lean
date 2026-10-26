/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeDirectSourceFacts
import Candidate.Research.RecursiveAffine.TerminalLow.Direct
import Candidate.Cycle63.Moment.LowBranch.DirectMain

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcreteTraceCRT
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentAllocatedRayDictionary CenteredMomentCanonicalFirst
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy CenteredMomentEligibleEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyPaidBands
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentAllocatedChildCapacity CenteredMomentAllocatedNaturalSource
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity Cycle63InitialMass
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical CenteredMomentSupport
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)


/-- Source-level direct branch at the actual live regional geometry. All
prime, nonunit and retained-capacity inequalities are obtained internally
from the SAME live row. The scalar room is the checked regional/root cell
certificate. This is a literal finalPositiveEnergy bound, with the
original profiles and original LOW predicate. -/
theorem actual_live_direct_physical_daughter [Cycle63.AffineLedger]
    (W : ℝ → ℂ) (Bmask L Mcap εold : ℝ)
    (hWs : Function.support W ⊆ Icc 1 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d q : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ),
    ∀ (η₀ : Character) (Qfixed : Ideal O), Qfixed ≤ M →
    internalQ Qfixed η₀ ≠ 0 → internalQ Qfixed η₀ ≠ ⊤ →
    internalQ Qfixed η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C C₀ C₁ : ℝ, 1 ≤ C ∧ 0 < C₀ ∧ 0 < C₁ ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (hZ : 1 < Z) (s : Input α) (θ : α → RayQuotient.Characters M H)
        (w σ freq : α → ℝ) (t height mesh a : ℝ) (i : ℕ),
      Matches M H hH s η₀ θ w σ freq W 2 Z →
      (∀ j, 0 ≤ w j) →
      (∀ j, w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      0 ≤ mesh → (∀ j, w j ≤ mesh) →
      (∀ j, w j/d ≤ Rwidth) →
      (∀ j, (33/50:ℝ) ≤ σ j) → (∀ j, σ j ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ j, |freq j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ (ch : Chain s) (Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax leastWidth : ℝ)
        (budget : ℕ) (g : LiveMainGeometry s ch Z Mrow amp omega xi bs budget)
        (ray : RayFourExpansion.RayCharacter) (Q : Ideal O) (hP : ch.R₂*ch.E₂ ≠ 0)
        (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Z^Bmask)
        (second : Bool) (Lres : Ideal O)
        (alloc : Allocation Lres (Finset.univ : Finset
          (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2))),
      let chi := g.datum.τ ray
      let st := retainedState Z Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
        g.datum.radius g.datum.C g.datum.D g.datum.inactive
      let src := ch.final chi t
      let nominal := secondNominal 1 Z amp omega ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
      st.fixedModulus = internalQ Qfixed η₀ → st.width ≤ Mcap →
      ∀ (p : Profiles (1/4) (9/4)), s.W₁ = (p.profile 0 : ℝ → ℂ) → s.W₂ = (p.profile 1 : ℝ → ℂ) →
      rawDaughterScale src second Lres alloc 0 ≤ Z^L →
      rawDaughterScale src second Lres alloc 1 ≤ Z^L →
      1 ≤ bs → s.upper ≤ bs →
      (Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop) →
      (length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤
        Cycle63.AffineLedger.B) →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+epsWidth/2 →
      Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(budget:ℝ)*Real.logb Z bs+Real.logb Z 1+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ epsWidth/2 →
      0 ≤ epsWidth → 0 ≤ xi → 0 ≤ omega → 0 ≤ epsPad →
      supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z ≤ epsPad →
      omega ≤ omegaMax → epsWidth+xi/2 ≤ deltaMax →
      q/(6*Cycle63.Optimization.slotPrice) ≤ 1/2 →
      Cycle63.AffineLedger.lowReserve ≤ amp →
      nominal+(epsWidth+xi/2) < leastWidth →
      (q/(6*Cycle63.Optimization.slotPrice)*
        (Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))+6*amp)-amp)+
        Cycle63.AffineLedger.lowReserve+
        q/(6*Cycle63.Optimization.slotPrice)*(deltaMax+epsPad)+
        2*(q/(6*Cycle63.Optimization.slotPrice))*omegaMax ≤
          q/(6*Cycle63.Optimization.slotPrice)*(1-6*amp-2*leastWidth) →
      ∀ (row : O), Cycle63.Physical.sourcePositiveRow src.toSource second Lres alloc row ≠ 0 →
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus),
      let low := ActualLow M H hH st η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      finalPositiveEnergy src second Lres alloc (fun z => st.radial.keep z ∧ low z)
          st.radial.profile st.radial.scale ≤
        C^(Fintype.card α)*((C₀+C₁)*diagonalControl st.radial.profile*
          (p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+(epsWidth+xi/2)+amp-Cycle63.AffineLedger.lowReserve+
            lowAllowance Z ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂+
            εold+2*ε*d*(Fintype.card α:ℝ)+
            q/(6*Cycle63.Optimization.slotPrice)*(omega+epsPad)+q*mesh) := by
  obtain ⟨degree,S,hsource⟩ := Cycle153TerminalLow.actual_direct_physical_daughter (α:=α) M H hH
    W Bmask L Mcap εold hWs hW hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d q hRw hdmax hτ hε he he' hκ hη hbudget
    hmargin hd hdsupply hdm hq₀ hq₁
  refine ⟨degree,S,?_⟩
  intro η₀ Qfixed hQfixedM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hsource η₀ Qfixed hQfixedM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,hC,hC₀,hC₁,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq t height mesh a i hmatch hw hwL hmesh hwm hwr hσlo hσhi
    hheight hfreq ha ha' hfreqbin hhigh ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax
    leastWidth budget g ray Q hP hPN second Lres alloc chi st src nominal
    hfixed hcap p hp1 hp2 hX1 hX2 hb hs hslots haff hfit hconstants hepsWidth hxi homega hepsPad
    hpad homegaMax hdeltaMax hrateHalf hreserve hnarrow hcert row hrow hQM hQη low
  have hrate0 : 0 ≤ q/(6*Cycle63.Optimization.slotPrice) :=
    div_nonneg hq₀ (by norm_num [Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound])
  have hP1 : ∀j,1 ≤ s.P j := fun j => by
    rw [hmatch.scale j]
    exact Real.one_le_rpow hZ.le (hw j)
  obtain ⟨hG,htotal,hpay⟩ := actual_regional_direct_source g hb hs hZ hP1 hslots haff
    hfit (by simpa only [Real.logb_one,add_zero] using hconstants)
    hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate0 hrateHalf hreserve
    chi t second Lres alloc row hrow hnarrow hcert
  let G := max (Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))+6*amp-
      (min (Real.logb Z (ch.C₁.absNorm:ℝ)) (Real.logb Z (g.D₁.absNorm:ℝ))+
        ((Real.logb Z (ch.E₂.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator g.datum.C g.datum.D)))+
            Real.logb Z ((∏j∈g.datum.inactive,j.val).absNorm:ℝ)))) 0
  have hraw0 : length Z (rawDaughterScale src second Lres alloc 0)=
      length Z (finalPlain src second Lres alloc 0) := by
    exact (length_clippedScale Z _).symm
  have hraw1 : length Z (rawDaughterScale src second Lres alloc 1)=
      length Z (finalPlain src second Lres alloc 1) := by
    exact (length_clippedScale Z _).symm
  have htotalOriginal : length Z (rawDaughterScale src second Lres alloc 0)+
      length Z (rawDaughterScale src second Lres alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑j∈ch.indices Lres alloc,w j)-nominal ≤ G+(omega+epsPad) := by
    rw [hraw0,hraw1]
    rw [original_slot_sum s ch chi t Z hZ w hmatch.scale Lres alloc] at htotal
    exact htotal
  have hwidth := live_main_state_width_unit (unit:=1) g Bmask hZ (zero_lt_one.trans_le hb)
    ray Q hP hPN (by simpa only [mul_one] using hfit)
    (by simpa only [mul_one] using hconstants)
  simp only [mul_one] at hwidth
  exact hz.2 hZ s θ w σ freq t height mesh a i hmatch hw hwL hmesh hwm hwr hσlo hσhi
    hheight hfreq ha ha' hfreqbin hhigh ch chi Q hP hPN g.datum.radius g.datum.C g.datum.D
    g.datum.inactive second Lres alloc hfixed hcap p hp1 hp2 hX1 hX2 nominal (epsWidth+xi/2)
    (omega+epsPad) amp Cycle63.AffineLedger.lowReserve
    (lowAllowance Z ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂) G hwidth
    (by positivity) (add_nonneg homega hepsPad) hG htotalOriginal hpay hQM hQη
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_live_direct_physical_daughter
