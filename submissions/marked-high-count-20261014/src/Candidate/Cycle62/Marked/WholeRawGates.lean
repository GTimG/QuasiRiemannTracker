import Candidate.Cycle62.Marked.WholePaddedCore
import Candidate.Cycle62.Marked.DeletionRawCleanSlots

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily ProbePhysical LocalMoment Cycle62Moment
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def wholeRawSlot {Slot : Type} (η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (w σ v : Slot→ℝ) (t : NonzeroFrequency→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (χ : NonzeroFrequency→Character) (u : NonzeroFrequency) (s : Slot) : ℂ :=
  naturalSlot (χ u) (primePool M H 2 (U^(w s)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I) (t u)) (U^(w s))

/-- A lower maximum in the actual whole family supplies the literal
oriented zero row consumed by the unconditional large-root estimate. -/
theorem whole_maximum_to_actual_zero_row (η η₀ χ : Character) (u : NonzeroFrequency)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀K,idealCoeff χ K=idealCoeff (excluded (naturalRow η u.val u.property).character R) K)
    (hχ : ∀j,(wholeSourceFamily M H hH η₀ χ j).residue≠1)
    (a T height : ℝ) (ha : 33/40≤ a) (hmax : a≤ zeroMaximum (wholeSourceFamily M H hH η₀ χ) hχ T)
    (hT : T≤ height) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)).data
      (fun _=>false) a height u := by
  obtain ⟨hc,he⟩ := whole_family_clean_maximum M H hH η η₀ χ u.val u.property R hR hcoeff hχ
  have hm := hmax.trans_eq (he T).symm
  obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained _ hc T (by linarith)
  apply natural_zero_to_literal_dictionary _ (fun _=>false) a height ha u
  refine ⟨j,s,?_,?_,?_,ht.trans hT⟩
  · simpa only [Bool.false_eq_true,ite_false,naturalRawFamily,cleanWholeBase] using hz
  · exact Or.inr (hc j)
  · rw [hs];exact hm

/-- Each row of a sixth-root fiber is an actual member of the original
raw finite population. -/
theorem sixth_fiber_raw_mem (R : Finset NonzeroFrequency) (B : NZIdeal)
    (u : FreeRow) (hu : u∈sixthFreeFiber R B) : sixthFrequencyEquiv (u,B)∈R := by
  obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp,hpB⟩ := Finset.mem_filter.mp hp
  have he : p=(u,B) := Prod.ext hpu hpB
  subst p
  exact (mem_sixthPairs R (u,B)).mp hp

/-- Actual raw norm bounds give the unpadded sixth-free core window. -/
theorem sixth_fiber_core_norm (R : Finset NonzeroFrequency) (B : NZIdeal) (U : ℝ)
    (hrow : ∀u∈R,rawFrequencyNorm u≤ U) (u : FreeRow) (hu : u∈sixthFreeFiber R B) :
    rowNorm u≤ U/(B.val.absNorm : ℝ)^6 := by
  have hh:=hrow _ (sixth_fiber_raw_mem R B u hu)
  rw [raw_sixth_norm] at hh
  have hB : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  exact (le_div_iff₀ (pow_pos hB _)).mpr hh

/-- The same actual row character has a literal free-core presentation,
with the sixth root added to its original moving hole ideal. -/
theorem sixth_core_mask_coefficients (η χ : Character) (u : FreeRow) (B : NZIdeal)
    (R : Ideal O) (hR : R≠0)
    (hcoeff : ∀K,idealCoeff χ K=idealCoeff
      (excluded (naturalRow η (sixthFrequencyEquiv (u,B)).val
        (sixthFrequencyEquiv (u,B)).property).character R) K) :
    ∀K,idealCoeff χ K=idealCoeff (excluded (naturalRow η u.val u.property.1).character (B.val*R)) K := by
  intro K
  rw [hcoeff K]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero B.val B.property
  have hh:=Deletion26.naturalRow_sixth_masked_ideal (naturalRow η u.val u.property.1)
    (ConcretePrimeRowBridge.idealGenerator B.val) hg
    (naturalRow η (sixthFrequencyEquiv (u,B)).val (sixthFrequencyEquiv (u,B)).property) R hR K
  rwa [ConcretePrimeRowBridge.span_idealGenerator] at hh

/-- A uniform individual amplitude cap yields the full raw max-product
envelope, retaining the sum of physical widths exactly. -/
theorem max_product_power_envelope {Slot : Type*} (slots : Finset Slot) (Q : Slot→ℂ)
    (U δ bw : ℝ) (w : Slot→ℝ) (hU : 1≤ U) (hδ : 0≤δ/2+bw)
    (hw : ∀s∈slots,0≤ w s) (hQ : ∀s∈slots,‖Q s‖≤(U^(w s))^(δ/2+bw)) :
    (∏s∈slots,max 1 ‖Q s‖)^2≤ U^((δ+2*bw)*(∑s∈slots,w s)) := by
  have hUp : 0< U := zero_lt_one.trans_le hU
  have hmax (s : Slot) (hs : s∈slots) : max 1 ‖Q s‖≤(U^(w s))^(δ/2+bw) := by
    apply max_le _ (hQ s hs)
    exact Real.one_le_rpow (Real.one_le_rpow hU (hw s hs)) hδ
  have hprod := pow_le_pow_left₀ (Finset.prod_nonneg (fun s _=>le_trans zero_le_one (le_max_left _ _)))
    (Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _)) hmax) 2
  apply hprod.trans_eq
  simp_rw [←Real.rpow_mul hUp.le]
  rw [←Real.rpow_sum_of_pos hUp,←Real.rpow_natCast,←Real.rpow_mul hUp.le]
  congr 1
  rw [←Finset.sum_mul]
  ring

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.whole_maximum_to_actual_zero_row
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.sixth_core_mask_coefficients
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.max_product_power_envelope
