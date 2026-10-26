/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalDaughterSource
import Candidate.Cycle63.Moment.LowBranch.DirectMain

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153TerminalLow
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
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass
open Cycle153RegionalLow
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine direct OLD-only bound for the original physical daughter.
The native direct LOW theorem selects its own terminal deletion; that is
legitimate because this branch returns no recursive source. The actual
LOW predicate, both original profiles, raw scales and radial measure are
preserved through the exact source reindexing and clipping comparison.
Only literal scalar capacity/amplifier inequalities are required. -/
theorem actual_direct_physical_daughter
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
      ∀ (ch : Chain s) (χ : Character) (Q : Ideal O) (hP : ch.R₂*ch.E₂ ≠ 0)
        (hPN : ((ch.R₂*ch.E₂).absNorm : ℝ) ≤ Z^Bmask) (radius : ℝ)
        (Ccommon Dcommon : Ideal O) (Ucommon : Finset (CommonIndex Ccommon Dcommon))
        (second : Bool) (Lres : Ideal O)
        (alloc : Allocation Lres (Finset.univ : Finset
          (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2))),
      let st := retainedState Z Bmask hZ χ Q (ch.R₂*ch.E₂) hP hPN radius Ccommon Dcommon Ucommon
      let src := ch.final χ t
      let J := ch.indices Lres alloc
      st.fixedModulus = internalQ Qfixed η₀ → st.width ≤ Mcap →
      ∀ (p : Profiles (1/4) (9/4)), s.W₁ = (p.profile 0 : ℝ → ℂ) → s.W₂ = (p.profile 1 : ℝ → ℂ) →
      rawDaughterScale src second Lres alloc 0 ≤ Z^L →
      rawDaughterScale src second Lres alloc 1 ≤ Z^L →
      ∀ (nominal δ padding amp reserve X G : ℝ),
      st.width-nominal ≤ δ → 0 ≤ δ → 0 ≤ padding → 0 ≤ G →
      length Z (rawDaughterScale src second Lres alloc 0)+
        length Z (rawDaughterScale src second Lres alloc 1)+
        6*Cycle63.Optimization.slotPrice*(∑ j ∈ J,w j)-nominal ≤ G+padding →
      q/(6*Cycle63.Optimization.slotPrice)*G ≤ amp+X-reserve →
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus),
      let low := ActualLow M H hH st η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      finalPositiveEnergy src second Lres alloc (fun z => st.radial.keep z ∧ low z)
          st.radial.profile st.radial.scale ≤
        C^(Fintype.card α)*((C₀+C₁)*diagonalControl st.radial.profile*
          (p.control S)^2*(1+|t|+height)^degree)*
          Z^(nominal+δ+amp-reserve+X+εold+2*ε*d*(Fintype.card α : ℝ)+
            q/(6*Cycle63.Optimization.slotPrice)*padding+q*mesh) := by
  obtain ⟨degree,S,hsource⟩ := actual_direct_low_main (α:=α) M H hH
    W 1 2 (1/4) (9/4) 2 Bmask L (33/50) (33/50) Mcap εold
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget
    hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨degree,S,?_⟩
  intro η₀ Qfixed hQfixedM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hbound⟩ := hsource η₀ Qfixed hQfixedM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,hC,hC₀,hC₁,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq t height mesh a i hmatch hw hwL hmesh hwm hwr hσlo hσhi
    hheight hfreq ha ha' hfreqbin hhigh ch χ Q hP hPN radius Ccommon Dcommon Ucommon
    second Lres alloc st src J hfixed hcap p hp1 hp2 hX₁L hX₂L nominal δ padding amp reserve X G
    hwidth hδ hpad hG htotal hpay hQM hQη low
  obtain ⟨R,hR,hOld,hraw⟩ := hz.2 J θ w σ freq t height mesh a i hw hwL
    (fun j _ => hwr j) hmesh (fun j _ => hwm j) hσlo hσhi hheight hfreq ha ha' hfreqbin hhigh
    st hfixed hcap p (rawDaughterScale src second Lres alloc 0)
    (rawDaughterScale src second Lres alloc 1)
    (raw_daughter_scale_pos src second Lres alloc 0) (raw_daughter_scale_pos src second Lres alloc 1)
    hX₁L hX₂L nominal δ padding amp reserve X G hwidth hδ hpad hG htotal hpay
  rw [original_low_energy M H hH s η₀ θ w σ freq W 2 Z Bmask hZ hmatch ch χ t Q hP hPN
    radius Ccommon Dcommon Ucommon second Lres alloc low]
  rw [hp1,hp2]
  exact energy_clipped_le_of_le _ _ _ _ _ _ _ _ _
    (fun j => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    _ _ (raw_daughter_scale_pos src second Lres alloc 0) (raw_daughter_scale_pos src second Lres alloc 1)
    _ _ _ _ (natural_energy_nonneg st _ _ _ _ _ _ _ _ _) hraw
end
end OAI.SevenEighths.Cycle153TerminalLow
#print axioms OAI.SevenEighths.Cycle153TerminalLow.actual_direct_physical_daughter
