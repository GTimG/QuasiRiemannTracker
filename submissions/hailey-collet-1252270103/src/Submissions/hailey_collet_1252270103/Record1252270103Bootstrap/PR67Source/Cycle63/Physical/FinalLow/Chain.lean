import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ChildMatches
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalCapacity.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalNatural.Energy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalLow
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
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Actual two-stage allocation dictionary. No capacity or moment field. -/
structure Chain (s : Input α) where
  C₁ : Ideal O
  R₁ : Ideal O
  B₁ : actualAllocations s.pools C₁
  η₁ : Character
  t₁ : ℝ
  E₂ : Ideal O
  R₂ : Ideal O
  B₂ : actualAllocations (child s C₁ R₁ B₁ η₁ t₁).pools E₂

def Chain.first {s : Input α} (q : Chain s) : Input (CenteredMomentCommonProfile.liveIndices q.B₁.val) :=
  child s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁

def Chain.final {s : Input α} (q : Chain s) (η : Character) (v : ℝ) :=
  commonData (withHeight q.first η v) q.E₂ q.R₂ q.B₂

def Chain.embedding {s : Input α} (q : Chain s) :
    CenteredMomentCommonProfile.liveIndices q.B₂.val ↪ α :=
  (originalEmbedding q.first q.E₂ q.B₂).trans (originalEmbedding s q.C₁ q.B₁)

def Chain.indices {s : Input α} (q : Chain s) (L₂ : Ideal O)
    (a : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :=
  (CenteredMomentDivisorRaw.liveIndices L₂ a).map q.embedding

/-- Literal low energy reindexed into the fixed original ambient family. -/
theorem original_low_energy (M : Ideal O) [NeZero M]
    (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1<Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (q : Chain s)
    (η : Character) (v : ℝ) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) (R : ℝ)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L₂ : Ideal O)
    (a : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2)))
    (low : O→Prop) :
    let st := retainedState Z Bmask hZ η Q (q.R₂*q.E₂) hP hPN R C D U
    let src := q.final η v
    let J := q.indices L₂ a
    let X₁ := finalPlain src second L₂ a 0
    let X₂ := finalPlain src second L₂ a 1
    finalPositiveEnergy src second L₂ a (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
          (Ideal.absNorm (selectedPlain L₂ a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
          (Ideal.absNorm (selectedPlain L₂ a 1):ℝ))))
        (fun j : J=>primePool M H bslot (Z^(w j)))
        (fun (j : J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : J=>Z^(w j)) X₁ X₂ (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale := by
  dsimp only
  have hc := Cycle63ChildMatches.actual_child_matches M H hH s η₀ θ w σ freq W bslot Z hm
    q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
  unfold Chain.final
  erw [actual_positive_natural_energy M H hH q.first η₀
    (fun j=>θ j.val) (fun j=>w j.val) (fun j=>σ j.val) (fun j=>freq j.val)
    W bslot Z Bmask hZ hc q.E₂ q.R₂ q.B₂ η v Q hP hPN R C D U second L₂ a low]
  exact CenteredMomentEnergyReindex.energy_subset_map q.embedding
    (CenteredMomentDivisorRaw.liveIndices L₂ a) η (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1
    _ _ (fun j=>primePool M H bslot (Z^(w j)))
    (fun j I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (freq j) I)
    (fun j=>Z^(w j)) v _ _ _ _ _

/-- The residual slot sum uses the same fixed ambient labels as the bound. -/
theorem original_slot_sum (s : Input α) (q : Chain s) (η : Character) (v Z : ℝ) (hZ : 1<Z)
    (w : α→ℝ) (hP : ∀j,s.P j=Z^(w j)) (L₂ : Ideal O)
    (a : Allocation L₂ (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    CenteredMomentAllocatedChildCapacity.remainingLogs L₂ a Z (q.final η v).P = ∑j∈q.indices L₂ a,w j := by
  rw [Chain.indices,Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  change Real.logb Z (s.P j.val.val)=w j.val.val
  rw [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

/-- If all literal positive rows vanish, the entire retained low energy is zero. -/
theorem zero_low_energy {ι : Type*} [Fintype ι] [DecidableEq ι] (src : Data ι)
    (second : Bool) (L₂ : Ideal O) (a : Allocation L₂ (Finset.univ : Finset (ι⊕Fin 2)))
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hz : ∀z,Cycle63.Physical.sourcePositiveRow src.toSource second L₂ a z=0) :
    finalPositiveEnergy src second L₂ a keep Φ K=0 := by
  unfold finalPositiveEnergy
  simp only [hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul,ite_self,tsum_zero]

end
end OAI.SevenEighths.Cycle63FinalLow

end Record1252270103Bootstrap.PR67
