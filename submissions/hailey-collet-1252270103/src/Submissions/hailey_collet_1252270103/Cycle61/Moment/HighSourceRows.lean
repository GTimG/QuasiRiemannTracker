import Submissions.hailey_collet_1252270103.Cycle61.Moment.FinalRowDictionary
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighAllocationLedger

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDetectorZeros
open HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open LowBranch CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Genuine high-bin estimates for the literal second retained allocation.
All structural equalities are exact source data; no energy envelope is assumed. -/
theorem actual_high_source_row
    (Wslot : ℝ → ℂ) (A₀ B₀ : ℝ) (hA₀ : 0 < A₀)
    (hWs : Function.support Wslot ⊆ Icc A₀ B₀) (hW : ContDiff ℝ ∞ Wslot)
    (Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax
      bΦ Mcap Bmask margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hRp : 0 ≤ Rplain) (hdmax : 0 ≤ dmax)
    (hτ : 0 < τ) (hεs : 0 < εslot) (hεp : 0 < εplain)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hvp : 0 ≤ vplain) (hvs : 0 ≤ vslot)
    (hslotBudget : 8*e*Rwidth+κ ≤ εslot)
    (hplainBudget : 12*e*(Rplain+2)+8*κ+2*vplain ≤ εplain)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) (hd : 0 < d)
    (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ Cp Cs : ℝ, 0 < Cp ∧ 0 < Cs ∧
    ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (s : NaturalState Z Bmask bΦ), s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
    ∀ z : O, ∀ hz : s.radial.keep z, ∀ F : NaturalRow s.character z,
    ActualLow M H hH s η₀ hQM hQη a e (3*(i+1 : ℕ)*Z^τ) z →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (j : Dict),
    χ j = excluded F.character s.puncture →
    zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    (χ j).modulus.absNorm ≤ Z^d →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (t : ℝ)
      (src : Data ι) (second : Bool) (L : Ideal O)
      (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))),
    src.η = s.character → src.m = s.mask → src.A = 1 → src.t = t →
    (∀ k, src.slots k = primePool M H B₀ (Z^(w k))) →
    (∀ k I, src.coefficient k I = idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I) →
    (∀ k, src.P k = Z^(w k)) →
    (∀ k, 0 ≤ w k) → (∀ k, w k/d ≤ Rwidth) →
    (∀ k, σmin ≤ σ k) → (∀ k, σ k ≤ σmax) →
    (∀ k, |t+v k|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
    (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^vslot →
    |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
    (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^vplain →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ),
    src.W₁ = W 0 → src.W₂ = W 1 →
    (∀ k, Cycle61.Physical.postPlainScale L alloc
      (Cycle61.Physical.sourcePlainScales src.toSource second) k = X k) →
    (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
    (∀ k, 0 < A k) →
    (∀ k, Function.support (dilated (W k) (clipDilation (X k))) ⊆ Icc (A k) (B k)) →
    (∀ k, ContDiff ℝ ∞ (dilated (W k) (clipDilation (X k)))) →
    (∀ k, 0 ≤ r k) → (∀ k, r k ≤ Rplain) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^2*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
    (∀ k, ∀ x ∈ Icc (1-a-6*e) 2, ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (dilated (W k) (clipDilation (X k)))
        ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
    ‖Cycle61.Physical.sourcePositiveRow src.toSource second L alloc z‖^2 ≤
      Cp^2*Cs^((liveIndices L alloc).card)*
        Z^((2*a-1)*(
          (∑ j, Real.logb Z (clippedScale (Cycle61.Physical.sourcePlainScales src.toSource second j)))+
          (∑ k, w k)-Cycle61.Physical.clippedReduction
            (Real.logb Z (formalReductionFactor L alloc src.P))
            (fun j => Real.logb Z (Cycle61.Physical.sourcePlainScales src.toSource second j))
            (Cycle61.Physical.actualPlainReduction Z L alloc))+
          2*εplain*d+2*εslot*d*((liveIndices L alloc).card)) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hbound⟩ := actual_high_retained_row M H hH Wslot A₀ B₀ hA₀ hWs hW
    Rwidth Rplain dmax τ εslot εplain e κ vplain vslot σmin σmax bΦ Mcap Bmask margin d
    hRw hRp hdmax hτ hεs hεp he he' hκ hκ' hvp hvs hslotBudget hplainBudget
    hbΦ hmargin hd hdsupply hdm profileBound hprofile
  refine ⟨n,Cp,Cs,hCp,hCs,?_⟩
  intro η₀
  filter_upwards [hbound η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s hs hQM hQη a i ha ha' z hz F hbin Dict _ χ hχ j hj hzero hmod
    ι _ _ w σ v θ t src second L alloc hchar hmask hA' ht hpool hcoeff hP
    hw hwr hσ hσ' hfreq hheight hfreqP hheightP W X r A B hW₁ hW₂ hpost
    hX hscale hA hsupport hsmooth hr hrR hm₂ hmn
  have hb := hZ.2 s hs hQM hQη a i ha ha' z hz F hbin χ hχ j hj hzero hmod
    (fun k : liveIndices L alloc => w k) (fun k : liveIndices L alloc => σ k)
    (fun k : liveIndices L alloc => v k) (fun k : liveIndices L alloc => θ k) t
    (fun k => hw k) (fun k => hwr k) (fun k => hσ k) (fun k => hσ' k)
    (fun k => hfreq k) hheight hfreqP hheightP W X r A B hX hscale hA hsupport
    hsmooth hr hrR hm₂ hmn
  have hrow := final_source_row_eq s src second L alloc
    (fun k => primePool M H B₀ (Z^(w k)))
    (fun k I => idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight Wslot (Z^(w k)) (σ k) (v k) I)
    (fun k => Z^(w k)) t z hchar hmask hA' ht hpool hcoeff hP
  rw [hW₁,hW₂,hpost 0,hpost 1] at hrow
  have hpreX : ∀ j, 0 < Cycle61.Physical.sourcePlainScales src.toSource second j := by
    intro j
    cases second <;> fin_cases j
    · exact src.X₁_pos
    · exact src.X₂_pos
    · exact src.Y₁_pos
    · exact src.Y₂_pos
  have he := actual_high_allocation_exponent Z hZ.1 L alloc
    (Cycle61.Physical.sourcePlainScales src.toSource second) hpreX w d r
    (fun j => by rw [hpost j]; exact hscale j)
  rw [←funext hP] at he
  rw [hrow]
  have hb' := hb
  simp only [Fintype.card_coe,Finset.sum_coe_sort] at hb'
  rw [he] at hb'
  exact hb' 

#print axioms actual_high_source_row
end
end OAI.SevenEighths.Cycle61Moment
