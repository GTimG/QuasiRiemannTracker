import Candidate.Cycle63.Physical.ChildMatches
import Candidate.Cycle63.Physical.FinalErrorCapacity.Capacity
import Candidate.Cycle63.Physical.FinalNatural.Energy

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalError
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
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentAllocatedChildCapacity
open CenteredMomentAmplificationChildSourceCaps
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity Cycle63FinalErrorCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

structure Chain (s : Input α) where
  C₁ : Ideal O
  R₁ : Ideal O
  B₁ : actualAllocations s.pools C₁
  η₁ : Character
  t₁ : ℝ
  p : O
  hp : p≠0
  k : ℕ
  hk : 1≤k
  coprime : ∀i,∀I∈(child s C₁ R₁ B₁ η₁ t₁).slots i,IsCoprime (Ideal.span {p}) I
  Bp : actualAllocations (child s C₁ R₁ B₁ η₁ t₁).pools ((Ideal.span {p})^k)
  υ : Character
  t₂ : ℝ
  E₂ : Ideal O
  R₂ : Ideal O
  B₂ : actualAllocations (twiceChild s C₁ R₁ B₁ η₁ t₁ (Ideal.span {p}) k Bp υ t₂).pools E₂

def Chain.first {s : Input α} (q : Chain s) := child s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁
def Chain.extracted {s : Input α} (q : Chain s) :=
  twiceChild s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ (Ideal.span {q.p}) q.k q.Bp q.υ q.t₂
def Chain.final {s : Input α} (q : Chain s) (η : Character) (v : ℝ) :=
  commonData (withHeight q.extracted η v) q.E₂ q.R₂ q.B₂
def Chain.embedding {s : Input α} (q : Chain s) :
    CenteredMomentCommonProfile.liveIndices q.B₂.val ↪ α :=
  ((originalEmbedding q.extracted q.E₂ q.B₂).trans
    (originalEmbedding q.first ((Ideal.span {q.p})^q.k) q.Bp)).trans
    (originalEmbedding s q.C₁ q.B₁)
def Chain.indices {s : Input α} (q : Chain s) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :=
  (CenteredMomentDivisorRaw.liveIndices L a).map q.embedding

theorem original_positive_energy (M : Ideal O) [NeZero M]
    (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (s : Input α) (η₀ : Character) (θ : α→RayQuotient.Characters M H)
    (w σ freq : α→ℝ) (W : ℝ→ℂ) (bslot Z Bmask : ℝ) (hZ : 1<Z)
    (hm : Matches M H hH s η₀ θ w σ freq W bslot Z) (q : Chain s)
    (η : Character) (v : ℝ) (Q : Ideal O) (hP : q.R₂*q.E₂≠0)
    (hPN : ((q.R₂*q.E₂).absNorm:ℝ)≤Z^Bmask) (R : ℝ)
    (C D : Ideal O) (U : Finset (CommonIndex C D)) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    let st := retainedState Z Bmask hZ η Q (q.R₂*q.E₂) hP hPN R C D U
    let src := q.final η v
    let J := q.indices L a
    finalPositiveEnergy src second L a st.radial.keep st.radial.profile st.radial.scale =
      energy st.character st.mask 1 v
        (dilated s.W₁ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 0/
          (Ideal.absNorm (selectedPlain L a 0):ℝ))))
        (dilated s.W₂ (clipDilation (Cycle63.Physical.sourcePlainScales src.toSource second 1/
          (Ideal.absNorm (selectedPlain L a 1):ℝ))))
        (fun j : J=>primePool M H bslot (Z^(w j)))
        (fun (j : J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
          annularWeight W (Z^(w j)) (σ j) (freq j) I)
        (fun j : J=>Z^(w j)) (finalPlain src second L a 0) (finalPlain src second L a 1)
        st.radial.keep st.radial.profile st.radial.scale := by
  dsimp only
  have hc := Cycle63ChildMatches.actual_twice_child_matches M H hH s η₀ θ w σ freq W bslot Z hm
    q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ (Ideal.span {q.p}) q.k q.Bp q.υ q.t₂
  unfold Chain.final
  have he := actual_positive_natural_energy M H hH q.extracted η₀
    (fun j=>θ j.val.val) (fun j=>w j.val.val) (fun j=>σ j.val.val) (fun j=>freq j.val.val)
    W bslot Z Bmask hZ hc q.E₂ q.R₂ q.B₂ η v Q hP hPN R C D U second L a (fun _=>True)
  simp only [and_true] at he
  rw [he]
  exact CenteredMomentEnergyReindex.energy_subset_map q.embedding
    (CenteredMomentDivisorRaw.liveIndices L a) η (fixedBadMask*idealGenerator (q.R₂*q.E₂)) 1
    _ _ (fun j=>primePool M H bslot (Z^(w j)))
    (fun j I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
      annularWeight W (Z^(w j)) (σ j) (freq j) I)
    (fun j=>Z^(w j)) v _ _ _ _ _

theorem original_slot_sum (s : Input α) (q : Chain s) (η : Character) (v Z : ℝ) (hZ : 1<Z)
    (w : α→ℝ) (hP : ∀j,s.P j=Z^(w j)) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2))) :
    remainingLogs L a Z (q.final η v).P = ∑j∈q.indices L a,w j := by
  rw [Chain.indices,Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  change Real.logb Z (s.P j.val.val.val)=w j.val.val.val
  rw [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem allocated_plain_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (η : Character) (v : ℝ) (second : Bool) (j : Fin 2) :
    Cycle63.Physical.sourcePlainScales (commonData (withHeight s η v) C R B).toSource second j ≤
      Cycle63.Physical.sourcePlainScales s.toData.toSource second j := by
  have hn (i : Fin 2) : (1:ℝ)≤(B.val (Sum.inr i)).absNorm := norm_ge_one _ (alloc_ne s C B _)
  cases second <;> fin_cases j
  · exact div_le_self s.X₁_pos.le (hn 0)
  · exact div_le_self s.X₂_pos.le (hn 1)
  · exact div_le_self s.Y₁_pos.le (hn 0)
  · exact div_le_self s.Y₂_pos.le (hn 1)

theorem final_plain_cap (s : Input α) (q : Chain s) (η : Character) (v Z Lbound : ℝ)
    (hZ : 1<Z) (hL : 0≤Lbound)
    (hcap : ∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^Lbound)
    (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices q.B₂.val⊕Fin 2)))
    (j : Fin 2) : finalPlain (q.final η v) second L a j≤Z^Lbound := by
  have h₁ := allocated_plain_le s q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ second j
  have hp := allocated_plain_le q.first ((Ideal.span {q.p})^q.k) (q.R₁*q.C₁) q.Bp q.υ q.t₂ second j
  have h₂ := allocated_plain_le q.extracted q.E₂ q.R₂ q.B₂ η v second j
  have hsrc : Cycle63.Physical.sourcePlainScales (q.final η v).toSource second j≤Z^Lbound :=
    (h₂.trans (hp.trans h₁)).trans (hcap second j)
  have hx := source_plain_positive (q.final η v) second j
  have hn : (1:ℝ)≤(selectedPlain L a j).absNorm := norm_ge_one _
    (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero L Finset.univ a (Sum.inr j))
  change max 1 (_/_)≤_
  exact max_le (Real.one_le_rpow hZ.le hL) ((div_le_self hx.le hn).trans hsrc)

end
end OAI.SevenEighths.Cycle63FinalError
