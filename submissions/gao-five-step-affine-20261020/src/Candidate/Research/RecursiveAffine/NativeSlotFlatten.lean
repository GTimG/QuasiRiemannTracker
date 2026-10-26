/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeAffineContinuation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Reindex

set_option autoImplicit false
set_option maxHeartbeats 450000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentInductionEnergy CenteredMomentEnergyReindex
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open HeckePrimeRay HeckePrimeAnnular Cycle63InitialSource Cycle63FirstActual Cycle63FirstGeometry

variable {alpha : Type} [DecidableEq alpha]

/-- Literal inclusion of a current surviving slot in the original ray
index set. This is an embedding, so no multiplicity is introduced. -/
def nativeSlotEmbedding (T : Finset alpha) : T↪alpha :=
  ⟨Subtype.val,Subtype.val_injective⟩

/-- The original ray indices left by the actual active set and the
attaining LOW deletion. No fresh or freely chosen index is added. -/
def nativeSurvivingSlots (T : Finset alpha) (J deleted : Finset T) : Finset alpha :=
  (J\deleted).map (nativeSlotEmbedding T)

def nativeSurvivingEquiv (T : Finset alpha) (J deleted : Finset T) :
    ↥(J\deleted) ≃ nativeSurvivingSlots T J deleted :=
  Finset.equivMap (nativeSlotEmbedding T) (J\deleted)

@[simp] theorem nativeSurvivingEquiv_val
    (T : Finset alpha) (J deleted : Finset T) (i : ↥(J\deleted)) :
    ((nativeSurvivingEquiv T J deleted i).val : alpha) = i.val.val := rfl

@[simp] theorem nativeSurvivingEquiv_symm_val
    (T : Finset alpha) (J deleted : Finset T) (i : nativeSurvivingSlots T J deleted) :
    ((nativeSurvivingEquiv T J deleted).symm i).val.val = i.val := by
  have h := congrArg Subtype.val ((nativeSurvivingEquiv T J deleted).apply_symm_apply i)
  exact h

theorem nativeSurvivingSlots_subset
    (T : Finset alpha) (J deleted : Finset T) : nativeSurvivingSlots T J deleted ⊆ T := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  exact j.property

theorem nativeSurvivingSlots_mem
    (T : Finset alpha) (J deleted : Finset T) (i : alpha) :
    i∈nativeSurvivingSlots T J deleted ↔ ∃j : T,j∈J ∧ j∉deleted ∧ j.val=i := by
  simp only [nativeSurvivingSlots,Finset.mem_map,Finset.mem_sdiff,nativeSlotEmbedding]
  aesop

/-- Actual original exponents sum exactly across the nested surviving
subtype and its flattened original ray index set. -/
theorem native_surviving_sum (T : Finset alpha) (J deleted : Finset T) (f : alpha→ℝ) :
    (∑i : nativeSurvivingSlots T J deleted,f i.val) =
      ∑i : ↥(J\deleted),f i.val.val := by
  exact ((nativeSurvivingEquiv T J deleted).sum_comp
    (fun i : nativeSurvivingSlots T J deleted=>f i.val)).symm

/-- Dividing original slot weights by each licensed physical unit is
exactly division by their product. No width or frequency exponent is
silently enlarged during the source rebase. -/
theorem native_original_weight_relative
    (weight parentUnit childRelative : ℝ) (hparent : parentUnit≠0) (hchild : childRelative≠0) :
    (weight/parentUnit)/childRelative = weight/(parentUnit*childRelative) := by
  field_simp

/-- Exact actual remaining-source energy under slot flattening. The prime
pools, coefficient dictionary, prime scales, masks, radial function and
plain scales remain literal. This is the source equality used by the
reachable child constructor before invoking the strict-depth IH. -/
theorem native_surviving_energy
    (T : Finset alpha) (J deleted : Finset T) (eta : Character) (mask A : O)
    (W1 W2 : ℝ→ℂ) (pool : alpha→Finset (Ideal O)) (coefficient : alpha→Ideal O→ℂ)
    (P : alpha→ℝ) (t X1 X2 : ℝ) (keep : O→Prop) (Phi : 𝓢(ℝ,ℂ)) (scale : ℝ) :
    energy eta mask A t W1 W2 (fun i : ↥(J\deleted)=>pool i.val.val)
      (fun i : ↥(J\deleted)=>coefficient i.val.val) (fun i : ↥(J\deleted)=>P i.val.val)
      X1 X2 keep Phi scale =
    energy eta mask A t W1 W2 (fun i : nativeSurvivingSlots T J deleted=>pool i.val)
      (fun i : nativeSurvivingSlots T J deleted=>coefficient i.val)
      (fun i : nativeSurvivingSlots T J deleted=>P i.val) X1 X2 keep Phi scale :=
  energy_subset_map (nativeSlotEmbedding T) (J\deleted) eta mask A W1 W2 pool coefficient P
    t X1 X2 keep Phi scale

/-- Reindex the actual constructed affine input at the exact flattening
map. Its coefficients and original columns are transported by the native
source reindexer. -/
def nativeFlattenedInput (T : Finset alpha) (J deleted : Finset T)
    (s : Input ↥(J\deleted)) : Input (nativeSurvivingSlots T J deleted) :=
  CenteredMomentSourceInputReindex.reindex (nativeSurvivingEquiv T J deleted) s

/-- The literal energy of the reindexed input equals the literal native
remaining input energy. In particular there is no assumed energy estimate
or replacement by a source capacity in this bridge. -/
theorem nativeFlattenedInput_energy
    (T : Finset alpha) (J deleted : Finset T) (s : Input ↥(J\deleted))
    (mask : O) (keep : O→Prop) (Phi : 𝓢(ℝ,ℂ)) (scale : ℝ) :
    let next := nativeFlattenedInput T J deleted s
    energy next.η mask next.A next.t next.W₁ next.W₂ next.slots next.coefficient next.P
      next.X₁ next.X₂ keep Phi scale =
    energy s.η mask s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P s.X₁ s.X₂ keep Phi scale := by
  intro next
  exact energy_reindex (nativeSurvivingEquiv T J deleted).symm s.η mask s.A s.W₁ s.W₂
    s.slots s.coefficient s.P s.t s.X₁ s.X₂ keep Phi scale

variable [Cycle63.AffineLedger] in
/-- The actual remaining affine continuation over nested original slots
has exactly the same energy as its flattened original-dictionary source.
Both comparisons are the actual next regional comparison; their plain
product is preserved by the native continuation theorem, so no independent
comparison or source-energy assumption is required. -/
theorem native_regional_surviving_energy
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (T : Finset alpha) (J deleted : Finset T)
    (eta : Character) (theta : alpha→RayQuotient.Characters M H)
    (W : ℝ→ℂ) (hW : Continuous W)
    (aSlot bSlot lo hi : ℝ) (haSlot : 0<aSlot)
    (hWs : Function.support W ⊆ Set.Icc aSlot bSlot)
    (w sigma freq : alpha→ℝ) (hsigma : ∀i,sigma i∈Set.Icc lo hi)
    {Z oldMask bPhi ap bp : ℝ} (st : CenteredMomentEnergyState.NaturalState Z oldMask bPhi)
    (unit : ℝ) (hunit : 0<unit) (hwide : st.width ≤ unit)
    (hmask : (st.puncture.absNorm:ℝ) ≤ (Z^unit)^(20:ℝ))
    (p : CenteredMomentFiniteProfileExceptional.Profiles ap bp) (hap : 0<ap)
    (t X1 X2 : ℝ) (hX1 : 0<X1) (hX2 : 0<X2) :
    let state := nativeContinuationState st unit hunit hwide hmask
    let nested := nativeRegionalContinuationInput M H hH eta
      (fun i : ↥(J\deleted)=>theta i.val.val) W hW aSlot bSlot lo hi haSlot hWs
      (fun i=>w i.val.val) (fun i=>sigma i.val.val) (fun i=>freq i.val.val)
      (fun i=>hsigma i.val.val) st unit hunit hwide hmask p hap t X1 X2 hX1 hX2
    let flat := nativeRegionalContinuationInput M H hH eta
      (fun i : nativeSurvivingSlots T J deleted=>theta i.val) W hW aSlot bSlot lo hi haSlot hWs
      (fun i=>w i.val) (fun i=>sigma i.val) (fun i=>freq i.val)
      (fun i=>hsigma i.val) st unit hunit hwide hmask p hap t X1 X2 hX1 hX2
    energy nested.η state.mask 1 nested.t nested.W₁ nested.W₂
      nested.slots nested.coefficient nested.P nested.X₁ nested.X₂
      state.radial.keep state.radial.profile state.radial.scale =
    energy flat.η state.mask 1 flat.t flat.W₁ flat.W₂ flat.slots flat.coefficient flat.P flat.X₁ flat.X₂
      state.radial.keep state.radial.profile state.radial.scale := by
  intro state nested flat
  have hn := nativeRegionalContinuationInput_energy M H hH eta
    (fun i : ↥(J\deleted)=>theta i.val.val) W hW aSlot bSlot lo hi haSlot hWs
    (fun i=>w i.val.val) (fun i=>sigma i.val.val) (fun i=>freq i.val.val)
    (fun i=>hsigma i.val.val) st unit hunit hwide hmask p hap t X1 X2 hX1 hX2
  have hf := nativeRegionalContinuationInput_energy M H hH eta
    (fun i : nativeSurvivingSlots T J deleted=>theta i.val) W hW aSlot bSlot lo hi haSlot hWs
    (fun i=>w i.val) (fun i=>sigma i.val) (fun i=>freq i.val)
    (fun i=>hsigma i.val) st unit hunit hwide hmask p hap t X1 X2 hX1 hX2
  exact hn.trans ((native_surviving_energy T J deleted st.character st.mask 1
    (p.profile 0) (p.profile 1) (fun i=>CenteredMomentPrimeSlot.primePool M H bSlot (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter M H hH eta (theta i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (sigma i) (freq i) I)
    (fun i=>Z^(w i)) t X1 X2 st.radial.keep st.radial.profile st.radial.scale).trans hf.symm)

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_surviving_energy
#print axioms OAI.SevenEighths.Cycle153RegionalLow.nativeFlattenedInput_energy

#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_regional_surviving_energy
