import Candidate.Uneven.AuxiliaryAffineLowPayment
set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.AuxiliaryLow
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
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
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open CenteredMomentNaturalRowSource
open Cycle63InitialSource
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local notation "O" => HeckeFamily.O
local instance geometryAffineLowDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable



open AuxiliaryPhysical
omit [DecidableEq α] in
/-- All added source gates come from the actual affine constructor. -/
theorem actual_affine_low_source_gates 
    (η₀ : Character)(θ : α→ RayQuotient.Characters M H)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (w σ freq : α→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    {Z bΦ : ℝ}(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂)(Cs : ℝ)(hZ : 1 < Z)
    (hw : ∀i,0 ≤ w i)(hslots : (∑i,w i) ≤ 1/25)
    (hhi₁ : length Z X₁ ≤ 45/100)(hhi₂ : length Z X₂ ≤ 45/100) :
    let inp:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates inp p (Fintype.card α) Cs Z →
    GeometryAffineLowSourceGates inp p Cs Z ∧ Matches M H hH inp η₀ θ w σ freq W 2 Z := by
  intro inp caps
  have hplain:=affine_plain_caps M H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hZ (by norm_num) le_rfl (by simpa using hhi₁) (by simpa using hhi₂)
  refine ⟨⟨caps,rfl,rfl,hplain,?_,?_⟩,?_⟩
  · intro i
    have hi : w i ≤ 1 := (Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)).trans
      (hslots.trans (by norm_num))
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hi
  · intro i
    change max |Real.log (1:ℝ)| |Real.log (2:ℝ)| ≤ Real.log 2
    simp only [Real.log_one,abs_zero,abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)),
      max_eq_right (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
    exact le_rfl
  · constructor <;> intros <;> rfl

set_option linter.defProp false in
def GeometryAffineSourceCapsSpec 
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Cs Z : ℝ) : Prop :=
  ∀(θ : α→ RayQuotient.Characters M H)(η₀ : Character)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (tplain X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂),
    (∀i,0 ≤ w i) → (81/200:ℝ) ≤ length Z X₁ → (81/200:ℝ) ≤ length Z X₂ →
    length Z X₁ ≤ (45/100:ℝ) → length Z X₂ ≤ (45/100:ℝ) → (∑i,w i) ≤ 1/25 →
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 tplain X₁ X₂ hX₁ hX₂
    GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z


end
end OAI.SevenEighths.MainPhysical
