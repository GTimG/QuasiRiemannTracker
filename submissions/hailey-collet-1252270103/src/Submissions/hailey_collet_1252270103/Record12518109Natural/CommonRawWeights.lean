/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original-slot and common-height normalization for the raw-root inlet. -/
import Submissions.hailey_collet_1252270103.Record12518109Natural.CommonSurvivingSlots
import Submissions.hailey_collet_1252270103.Record12518109Natural.RetainedSlotCaps

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Record12518109Natural.WeightedHigh
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceLiveColumn CenteredMomentWholeSlotDeletion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot CenteredMomentAllocatedRayDictionary
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge HeckePrimeAnnular Cycle61Moment
open CommonSupply
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def labeledRawSlot {Row : Type} (η₀ : Character) (W : ℝ→ℂ) (Z : ℝ)
    (w σ v : Slot→ℝ) (t : Row→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (χ : Row→Character) (l : Row) (k : Slot) : ℂ :=
  naturalSlot (χ l) (primePool M H 2 (Z^(w k)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight W (Z^(w k)) (σ k) (v k) I) (t l)) (Z^(w k))

lemma maximum_square (x : ℝ) (hx : 0≤x) : max 1 (x^2)=(max 1 x)^2 := by
  by_cases h : x≤1
  · rw [max_eq_left h,max_eq_left (by nlinarith : x^2≤1)]
    norm_num
  · have hh : 1≤x := le_of_not_ge h
    rw [max_eq_right hh,max_eq_right (by nlinarith : 1≤x^2)]

/-- Original height and slot frequencies combine by a unit complex phase. -/
theorem natural_annular_slot_norm (χ ν : Character) (W : ℝ→ℂ)
    (pool : Finset (Ideal O)) (hp : ∀I∈pool,I≠0)
    (P σ v t : ℝ) (hP : 0<P) :
    ‖naturalSlot χ pool (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t) P‖=
      ‖naturalSlot χ pool (fun I=>idealCoeff ν I*annularWeight W P σ (t+v) I) P‖ := by
  have he : naturalSlot χ pool
      (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t) P=
      (P:ℂ)^(Complex.I*t)*naturalSlot χ pool
        (fun I=>idealCoeff ν I*annularWeight W P σ (t+v) I) P := by
    unfold naturalSlot
    have hs : (∑I∈pool,idealCoeff χ I*
        heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I)=
        (P:ℂ)^(Complex.I*t)*(∑I∈pool,idealCoeff χ I*
          (idealCoeff ν I*annularWeight W P σ (t+v) I)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      rw [CenteredMomentEnergySlotHeight.height_coefficient _ W P σ v t hP I (hp I hI)]
      ring
    rw [hs]
    ring
  rw [he,norm_mul]
  have hphase : ‖(P:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hP (Complex.I*t)
  rw [hphase,one_mul]

/-- Exact two-common physical product, with its original surviving subset.
The source character and puncture remain those of the actual natural state. -/
theorem actual_two_common_raw_maximum
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ) (hB : P.B₀=2)
    (st : NaturalState Z P.Bmask P.bΦ) (z : O) (hz : st.radial.keep z)
    (s : Input Slot) (w σ v : Slot→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (hm : Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁) (χ₁ : Character) (t₁ : ℝ)
    (E R₂ : Ideal O) (pick : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools E)
    (t : ℝ) (hmask : st.mask=fixedBadMask*idealGenerator (R₂*E)) :
    sourceSlotMaximum (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) st.character t) E R₂ pick) z=
      (∏k∈originalSlots (fun k : liveIndices pick.val=>k.val.val),
        max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v (fun _ : Unit=>t) θ
          (fun _=>excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) () k‖)^2 := by
  let F := naturalRow st.character z (st.row_ne_zero z hz)
  have hc (k : Slot) : s.coefficient k=fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ k)) I*
      annularWeight P.Wslot (Z^(w k)) (σ k) (v k) I := by
    funext I
    change s.ν k I*s.W k ((I.absNorm:ℝ)/s.P k)=_
    rw [hm.character,hm.profile,hm.scale]
    rfl
  change (∏k : liveIndices pick.val,max 1
    (‖normalizedSlot st.character (fixedBadMask*idealGenerator (R₂*E)) 1 z
      (s.slots k.val.val) (s.coefficient k.val.val) t (s.P k.val.val)‖^2))=_
  rw [double_subtype_prod (liveIndices B₁.val) (liveIndices pick.val)
    (fun k : Slot=>max 1 (‖normalizedSlot st.character (fixedBadMask*idealGenerator (R₂*E)) 1 z
      (s.slots k) (s.coefficient k) t (s.P k)‖^2)),←Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro k hk
  rw [←hmask]
  change max 1 (‖normalizedSlot st.character (fixedBadMask*idealGenerator st.puncture) 1 z
    (s.slots k) (s.coefficient k) t (s.P k)‖^2)=_
  rw [masked_natural_slot_eq F st.puncture st.puncture_ne_zero,hc,hm.pool,hm.scale,hB,
    maximum_square _ (norm_nonneg _)]
  rfl

end
end OAI.SevenEighths.Record12518109Natural.WeightedHigh
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.natural_annular_slot_norm
#print axioms OAI.SevenEighths.Record12518109Natural.WeightedHigh.actual_two_common_raw_maximum
