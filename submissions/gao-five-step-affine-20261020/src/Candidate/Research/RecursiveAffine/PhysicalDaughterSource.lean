/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLowSource
import Candidate.Research.RecursiveAffine.RetainedFTwoStage
import Candidate.Cycle63.Physical.FinalLow.Chain
import Candidate.Cycle63.Physical.InitialMass.LowChildEnergyClip

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
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle63InitialMass

variable {α : Type*} [Fintype α]
local instance physicalDaughterSourceDecidableEq {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The two oriented source scales are positive before residual clipping. -/
theorem source_plain_scale_pos {ι : Type*} [Fintype ι] (s : Data ι) (second : Bool) (j : Fin 2) :
    0 < Cycle63.Physical.sourcePlainScales s.toSource second j := by
  cases second <;> fin_cases j
  · exact s.X₁_pos
  · exact s.X₂_pos
  · exact s.Y₁_pos
  · exact s.Y₂_pos

/-- The literal residual source plain quotient before clipping. -/
def rawDaughterScale {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : ℝ :=
  Cycle63.Physical.sourcePlainScales src.toSource second j/(selectedPlain L alloc j).absNorm

theorem raw_daughter_scale_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : 0 < rawDaughterScale src second L alloc j := by
  apply div_pos (source_plain_scale_pos src second j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero L Finset.univ alloc (Sum.inr j)))

/-- The native regional LOW operator on a literal physical daughter after
two actual common allocations and a residual allocation. The original ray
dictionary is reconstructed by `original_low_energy`; actual clipping is
removed with its nonnegative exact energy comparison. Thus the result is
about `finalPositiveEnergy`, rather than a surrogate energy assumed equal
to it. The remaining source retains all original profiles, masks, heights
and reciprocal normalization (no sum over residual ideals is taken here).

No bound of the remaining energy or terminating old-region hypothesis is
assumed. The attaining deletion can be consumed by the next depth. -/
theorem actual_regional_daughter_source
    (W : ℝ → ℂ) (A B : ℝ) (hA : 0 < A)
    (hWs : Function.support W ⊆ Icc A B) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τ ε e κ η σmin σmax Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∃ Cpay : ℝ, 1 ≤ Cpay ∧ ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (hZ : 1 < Z) (s : Input α) (θ : α → RayQuotient.Characters M H)
        (w σ freq : α → ℝ) (t height mesh a del : ℝ) (i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z →
      (∀ j, 0 ≤ w j) → (∀ j, w j/d ≤ Rwidth) →
      0 ≤ mesh → (∀ j, w j ≤ mesh) →
      (∀ j, σmin ≤ σ j) → (∀ j, σ j ≤ σmax) →
      0 ≤ height → (∀ j, |freq j| ≤ height) →
      51/100 ≤ a → a ≤ (1+q)/2 → 0 ≤ del →
      |t|+height+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^η →
      ∀ (ch : Chain s) (χ : Character) (Q : Ideal O) (hP : ch.R₂*ch.E₂ ≠ 0)
        (hPN : ((ch.R₂*ch.E₂).absNorm : ℝ) ≤ Z^Bmask) (radius : ℝ)
        (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L : Ideal O)
        (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2))),
      let st := retainedState Z Bmask hZ χ Q (ch.R₂*ch.E₂) hP hPN radius C D U
      let src := ch.final χ t
      let J := ch.indices L alloc
      st.width ≤ Mcap →
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus),
      let low := ActualLow M H hH st η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ)
      ∃ R : Finset α, R ⊆ J ∧ (∑ j ∈ R, w j) ≤ del+mesh ∧
        (R = J ∨ del ≤ ∑ j ∈ R, w j) ∧
        finalPositiveEnergy src second L alloc (fun z => st.radial.keep z ∧ low z)
          st.radial.profile st.radial.scale ≤
        Cpay^(Fintype.card α)*Z^(2*ε*d*(Fintype.card α : ℝ)+q*(del+mesh)) *
          energy st.character st.mask 1 t s.W₁ s.W₂
            (fun j : ↥(J \ R) => primePool M H B (Z^(w j)))
            (fun (j : ↥(J \ R)) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I *
              annularWeight W (Z^(w j)) (σ j) (freq j) I)
            (fun j : ↥(J \ R) => Z^(w j))
            (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
            st.radial.keep st.radial.profile st.radial.scale := by
  obtain ⟨Cpay,hCpay,hsource⟩ := actual_regional_low_source (α:=α) M H hH W A B hA hWs hW
    Rwidth dmax τ ε e κ η σmin σmax 2 Mcap Bmask margin d
    hRw hdmax hτ hε he he' hκ hη hbudget (by norm_num) hmargin hd hdsupply hdm q hq₀ hq₁
  refine ⟨Cpay,hCpay,?_⟩
  intro η₀
  filter_upwards [hsource η₀] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq t height mesh a del i hm hw hwr hmesh hwm hσlo hσhi hheight hfreq ha ha' hdel
    hfreqbin hhigh ch χ Q hP hPN radius C D U second L alloc st src J hs hQM hQη low
  obtain ⟨R,hR,hsum,hcover,hbound⟩ := hz.2 J θ w σ freq t height mesh a del i hw (fun j _ => hwr j)
    hmesh (fun j _ => hwm j) hσlo hσhi hheight hfreq ha ha' hdel hfreqbin hhigh st hs hQM hQη
    s.W₁ s.W₂ (rawDaughterScale src second L alloc 0) (rawDaughterScale src second L alloc 1)
    (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
  refine ⟨R,hR,hsum,hcover,?_⟩
  rw [original_low_energy M H hH s η₀ θ w σ freq W B Z Bmask hZ hm ch χ t Q hP hPN
    radius C D U second L alloc low]
  exact energy_clipped_le_of_le _ _ _ _ _ _ _ _ _
    (fun j => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    _ _ (raw_daughter_scale_pos src second L alloc 0) (raw_daughter_scale_pos src second L alloc 1)
    _ _ _ _ (natural_energy_nonneg st _ _ _ _ _ _ _ _ _) hbound

/-- The retained formal reduction of that same literal physical daughter
is available at every slot price at least `1/6`, in the same original ray
dictionary used by the actual regional source inequality above. This is a
source identity and supported-row bound; no returned record length is set
to the desired right side by definition. -/
theorem actual_daughter_affine_capacity_with_F
    (s : Input α) (ch : Chain s) (χ : Character) (t Z κ nominal : ℝ)
    (hZ : 1 < Z) (hκ : (1/6 : ℝ) ≤ κ) (hP : ∀ j, 1 ≤ s.P j)
    (w : α → ℝ) (hscale : ∀ j, s.P j = Z^(w j))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices ch.B₂.val ⊕ Fin 2)))
    (z : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc z ≠ 0) :
    let src := ch.final χ t
    length Z (finalPlain src second L alloc 0)+length Z (finalPlain src second L alloc 1)+
      6*κ*(∑ j ∈ ch.indices L alloc,w j)-nominal ≤
    Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction ch.B₁.val s.P)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction ch.B₂.val ch.first.P)-
      Real.logb Z (formalReductionFactor L alloc src.P)-nominal+
      (6*κ-1)*(∑ j,Real.logb Z (s.P j))+Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  let src := ch.final χ t
  let X := Cycle63.Physical.sourcePlainScales src.toSource second
  have hp : X 0*X 1 = src.X₁*src.X₂ := by
    cases second
    · rfl
    · exact src.same_product
  have hcap := Cycle152RetainedFReturn.two_stage_affine_capacity_retained_F
    s ch.C₁ ch.R₁ ch.B₁ χ t ch.E₂ ch.R₂ ch.B₂ L alloc Z κ nominal hZ hκ hP
    (X 0) (X 1) (source_plain_scale_pos src second 0) (source_plain_scale_pos src second 1) hp z hne
  have hplain : length Z (finalPlain src second L alloc 0)+length Z (finalPlain src second L alloc 1) =
      plainLogs L alloc Z (X 0) (X 1) := by
    change Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_)))+
      Real.logb Z (max 1 (CenteredMomentRetainedProfile.clippedScale (_/_))) = _
    rw [max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _),
      max_eq_right (CenteredMomentRetainedProfile.clippedScale_ge_one _)]
    rfl
  have hslots := original_slot_sum s ch χ t Z hZ w hscale L alloc
  dsimp only at hcap ⊢
  rw [hplain,←hslots]
  exact hcap

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_regional_daughter_source
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_daughter_affine_capacity_with_F
