/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B085
import Candidate.Bundles.B107
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

/- BEGIN ORIGINAL Cycle61.Moment.CellGeometry; sha256 7e8f4946e4034ee53b88a597a3961e660e38b734596a78005c5db3d259502366 -/
section
                                       
                                           
                                                   
                                

set_option autoImplicit false

namespace Cycle61.Moment
noncomputable section
open Arithmetic

/-- The original total slot width selects the amplifier once. -/
def originalCell (t : ℝ) : ℕ := max 1 ⌈(t - 17/500)*100000⌉₊

theorem originalCell_mem {t : ℝ} (ht : 17/500 ≤ t ∧ t ≤ 1/25) :
    1 ≤ originalCell t ∧ originalCell t ≤ 600 ∧
      cellUpper (originalCell t) - 1/100000 ≤ t ∧
      t ≤ cellUpper (originalCell t) := by
  have hx : 0 ≤ (t - 17/500)*100000 := by linarith [ht.1]
  have hc : ⌈(t - 17/500)*100000⌉₊ ≤ 600 :=
    Nat.ceil_le.mpr (by norm_num; linarith [ht.2])
  have hle := Nat.le_ceil ((t - 17/500)*100000)
  have hlt := Nat.ceil_lt_add_one hx
  have hi : 1 ≤ originalCell t := le_max_left _ _
  have hi' : originalCell t ≤ 600 := max_le (by omega) hc
  refine ⟨hi, hi', ?_, ?_⟩
  · by_cases hc1 : ⌈(t - 17/500)*100000⌉₊ ≤ 1
    · simp only [originalCell, max_eq_left hc1, cellUpper, Nat.cast_one]
      linarith [ht.1]
    · simp only [originalCell, max_eq_right (by omega :
        1 ≤ ⌈(t - 17/500)*100000⌉₊), cellUpper]
      linarith
  · have hcast : (⌈(t - 17/500)*100000⌉₊ : ℝ) ≤ (originalCell t : ℝ) := by
      exact_mod_cast (le_max_right 1 ⌈(t - 17/500)*100000⌉₊)
    unfold cellUpper
    linarith

theorem normalized_cell_bounds {M n₁ n₂ z : ℝ} (hM : 0 < M)
    (hz : (17/500)*M ≤ z ∧ z ≤ (1/25)*M)
    (haffine : n₁+n₂+lambda*z ≤ B*M) :
    let j := originalCell (z/M)
    1 ≤ j ∧ j ≤ 600 ∧
      max (n₁+n₂+(9/2)*z-M) 0 ≤ M*g (cellUpper j) ∧
      n₁+n₂+z ≤ M*totalA (cellUpper j) ∧
      0 < M*amp (cellUpper j) := by
  dsimp only
  have ht : 17/500 ≤ z/M ∧ z/M ≤ 1/25 := by
    constructor
    · exact (le_div_iff₀ hM).mpr hz.1
    · exact (div_le_iff₀ hM).mpr hz.2
  obtain ⟨hj1,hj600,hl,hu⟩ := originalCell_mem ht
  have hb := cellUpper_bounds hj1 hj600
  have hzup : z ≤ cellUpper (originalCell (z/M))*M := (div_le_iff₀ hM).mp hu
  have hzlow : (cellUpper (originalCell (z/M))-1/100000)*M ≤ z :=
    (le_div_iff₀ hM).mp hl
  have hcoef : 0 ≤ (9/2:ℝ)-lambda := by norm_num [lambda]
  have hcoef' : 0 ≤ lambda-1 := by norm_num [lambda]
  have hdef := mul_le_mul_of_nonneg_left hzup hcoef
  have htotal := mul_le_mul_of_nonneg_left hzlow hcoef'
  have hg := g_pos hb
  have hamp := amp_pos hb
  refine ⟨hj1,hj600, max_le ?_ (mul_pos hM hg).le, ?_, mul_pos hM hamp⟩
  · unfold g
    nlinarith
  · unfold totalA
    nlinarith

theorem comparison_old_capacity {M z ξ : ℝ}
    (hz : z ≤ M/25) (hξ : ξ ≤ 7*M/100) :
    M/4 + (M/2+ξ) + (9/2)*z ≤ M := by linarith

#print axioms originalCell_mem
#print axioms normalized_cell_bounds
end
end Cycle61.Moment

end
/- END ORIGINAL Cycle61.Moment.CellGeometry -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalCapacity.Affine; sha256 bbd8f160c78d0bf6620f0de93993b815552a40cbd59be9e9db7844e2cfd8a7c1 -/
section
                                  
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
variable {ι : Type*} [Fintype ι]

/-- The original affine cell, rather than an old parent-capacity gate, pays
the old 9/2 final capacity. Raw logarithms are bounded by clamped lengths. -/
theorem original_affine_capacity (s : Input ι) (Z M : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hz : (17/500)*M ≤ ∑ i, Real.logb Z (s.P i) ∧
      (∑ i, Real.logb Z (s.P i)) ≤ (1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑ i, Real.logb Z (s.P i)) ≤ Cycle61.Arithmetic.B*M) :
    let b := Cycle61.Arithmetic.cellUpper
      (Cycle61.Moment.originalCell ((∑ i,Real.logb Z (s.P i))/M))
    Real.logb Z (volume s)+(7/2)*(∑ i,Real.logb Z (s.P i)) ≤ M+M*Cycle61.Arithmetic.g b := by
  dsimp only
  obtain ⟨_,_,hcap,_,_⟩ := Cycle61.Moment.normalized_cell_bounds hM hz haffine
  have hh := (le_max_left (length Z s.X₁+length Z s.X₂+
    (9/2)*(∑ i,Real.logb Z (s.P i))-M) 0).trans hcap
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

#print axioms original_affine_capacity
end
end OAI.SevenEighths.Cycle61FinalCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalCapacity.Affine -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalCapacity.Allocation; sha256 d8942d449b8c794399286979d555896b081fc376793170373954430d224a0d13 -/
section
                                                                 
                                                                       
                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentSourceLiveColumn CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- A nonzero actual frozen coefficient supplies the common divisor shift.
The error depends only on the fixed slot count and fixed support bound. -/
theorem common_reduction_log_lower (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (C.absNorm:ℝ)-(N:ℝ)*Real.logb Z b ≤
      Real.logb Z (rawReduction B.val s.P) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hc := norm_ge_one C (allocation_ne s C B)
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R
    (allocation_product s C B) s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx => ⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn' : (C.absNorm:ℝ) ≤ b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le hc) hn'
  rw [Real.logb_mul (pow_pos (zero_lt_one.trans_le hb) _).ne' hr.ne',Real.logb_pow] at hh
  linarith

/-- The first actual common child retains its exact volume dictionary even
when its character and height have changed. -/
theorem first_child_prevolume (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (χ : Character) (t : ℝ) :
    preVolume (child s C R B χ t).toData = preVolume s.toData/rawReduction B.val s.P := by
  change preVolume (commonData s C R B) = _
  exact common_preVolume s C R B

/-- Both common allocations and the residual selected-plain allocation are
visible in the exact final raw volume. -/
theorem two_stage_raw_volume (s : Input ι) (C₁ R₁ : Ideal O)
    (B₁ : actualAllocations s.pools C₁) (χ : Character) (t : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B₂.val) ⊕ Fin 2))) :
    let first := child s C₁ R₁ B₁ χ t
    let final := commonData first C₂ R₂ B₂
    let denom := rawReduction B₁.val s.P*rawReduction B₂.val first.P*
      formalReductionFactor L a final.P
    rawScale L a final.X₁ 0*rawScale L a final.X₂ 1*
      (∏ j ∈ CenteredMomentDivisorRaw.liveIndices L a,final.P j) = preVolume s.toData/denom ∧
    rawScale L a final.Y₁ 0*rawScale L a final.Y₂ 1*
      (∏ j ∈ CenteredMomentDivisorRaw.liveIndices L a,final.P j) = preVolume s.toData/denom := by
  dsimp only
  obtain ⟨h₁,h₂⟩ := common_allocated_raw_volume (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂ L a
  rw [first_child_prevolume,div_div] at h₁ h₂
  exact ⟨h₁.trans (by congr 1; ring),h₂.trans (by congr 1; ring)⟩

#print axioms common_reduction_log_lower
#print axioms first_child_prevolume
#print axioms two_stage_raw_volume
end
end OAI.SevenEighths.Cycle61FinalCapacity

end
/- END ORIGINAL Cycle61.Physical.FinalCapacity.Allocation -/

/- BEGIN ORIGINAL Cycle61.Moment.HighCommonExponent; sha256 562f151cd48fa10e639009795c5c77ee41073be6a1304a220f41556b952ff63f -/
section
                                     
                                      
                                                
                                            

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentSourceLiveColumn Cycle61FinalCapacity
open CenteredMomentEnergyState CenteredMomentDivisorAllocation
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity Filter
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Both actual frozen coefficients pay their common-ideal shifts. The
remaining error depends only on the original slot count and support. -/
theorem actual_two_stage_raw_log (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (s : Input ι) (hcard : Fintype.card ι≤ N) (hs : s.upper≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (Z : ℝ) (hZ : 1< Z) :
    Real.logb Z (preVolume (commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂))≤
      Real.logb Z (preVolume s.toData)-Real.logb Z (C₁.absNorm:ℝ)-
        Real.logb Z (C₂.absNorm:ℝ)+2*(N:ℝ)*Real.logb Z b := by
  let first := child s C₁ R₁ B₁ χ t
  have hr₁ := common_reduction_log_lower N b hb s hcard hs C₁ R₁ B₁ hf₁ Z hZ
  have hr₂ := common_reduction_log_lower N b hb first
    ((live_card_le B₁.val).trans hcard) hs C₂ R₂ B₂ hf₂ Z hZ
  rw [common_preVolume,Real.logb_div (preVolume_pos first.toData).ne'
    (rawReduction_pos B₂.val (alloc_ne first C₂ B₂) first.P first.P_pos).ne',
    first_child_prevolume,Real.logb_div (preVolume_pos s.toData).ne'
    (rawReduction_pos B₁.val (alloc_ne s C₁ B₁) s.P s.P_pos).ne']
  linarith

omit [DecidableEq ι] in
/-- The original affine gate supplies the sharp raw-volume bound used by
the high ledger, in the cell chosen from the original slot sum. -/
theorem actual_original_raw_cap (s : Input ι) (Z M : ℝ) (hZ : 1< Z) (hM : 0< M)
    (hz : (17/500)*M≤∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i))≤(1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle61.Arithmetic.lambda*(∑i,Real.logb Z (s.P i))≤ Cycle61.Arithmetic.B*M) :
    Real.logb Z (preVolume s.toData)≤ M*Cycle61.Arithmetic.totalA
      (Cycle61.Arithmetic.cellUpper
        (Cycle61.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))) := by
  have hh := (Cycle61.Moment.normalized_cell_bounds hM hz haffine).2.2.2.1
  change Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤ _
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

/-- Fixed support padding vanishes uniformly before either common
allocation, the source, or any residual divisor is chosen. -/
theorem eventually_two_stage_padding (N : ℕ) (b ε : ℝ) (hb : 1≤ b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ 2*(N:ℝ)*Real.logb Z b≤ε := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (b^(2*N))),
    eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ (pow_pos (zero_lt_one.trans_le hb) _) hbound
  rw [Real.logb_pow,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

omit [DecidableEq ι] in
/-- One threshold supplies the raw exponent in the actual common-shell
estimate. Both supported common allocations pay their logarithmic shifts;
the final character and Mellin height do not alter the source volume. -/
theorem eventual_two_stage_common_raw_cap (N : ℕ) (b ε : ℝ) (hb : 1≤ b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧
      ∀(s : Input ι)(Mrow : ℝ),0< Mrow → Fintype.card ι≤ N → s.upper≤ b →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
        Cycle61.Arithmetic.B*Mrow →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
      frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
      ∀(χ₁ : Character)(t₁ : ℝ)(C₂ R₂ : Ideal O)
        (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂),
      (let first := child s C₁ R₁ B₁ χ₁ t₁;
        frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
      ∀(χ₂ : Character)(t₂ a c₁ c₂ : ℝ),1/2≤ a → a≤1 →
      c₁≤ Real.logb Z (C₁.absNorm:ℝ) → c₂≤ Real.logb Z (C₂.absNorm:ℝ) →
      (2*a-1)*Real.logb Z
        (preVolume (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂))≤
      (2*a-1)*(Mrow*Cycle61.Arithmetic.totalA (Cycle61.Arithmetic.cellUpper
        (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow)))-c₁-c₂)+ε := by
  filter_upwards [eventually_two_stage_padding N b ε hb hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s Mrow hM hcard hs hz haff C₁ R₁ B₁ hf₁ χ₁ t₁ C₂ R₂ B₂ hf₂ χ₂ t₂ a c₁ c₂
    ha ha' hc₁ hc₂
  have hraw := actual_two_stage_raw_log N b hb s hcard hs C₁ R₁ B₁ hf₁ χ₁ t₁
    C₂ R₂ B₂ hf₂ Z hZ.1
  have horiginal := actual_original_raw_cap s Z Mrow hZ.1 hM hz haff
  have hδ : 0≤2*a-1 := by linarith
  have hδ' : 2*a-1≤1 := by linarith
  have hbase : Real.logb Z
      (preVolume (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂))≤
      Mrow*Cycle61.Arithmetic.totalA (Cycle61.Arithmetic.cellUpper
        (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow)))-c₁-c₂+ε := by
    change Real.logb Z (preVolume (commonData (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂))≤ _
    linarith [hZ.2]
  have hh := mul_le_mul_of_nonneg_left hbase hδ
  nlinarith [mul_le_mul_of_nonneg_right hδ' hε.le]

variable (M : Ideal O) [NeZero M]
local instance highCommonFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The actual final high source, before the residual shell is summed.
All residual allocations share this exponent bound; the clipping term is
paid by its own normalization, and both common shifts come from support. -/
theorem actual_two_stage_high_exponent
    (N : ℕ) (b : ℝ) (hb : 1≤ b)
    (s : Input ι) (hcard : Fintype.card ι≤ N) (hs : s.upper≤ b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ) (hZ : 1< Z)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus≤ M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
    (w σ v : ι→ℝ) (θ : ι→ RayQuotient.Characters M H)
    (hscale : ∀i,s.P i=Z^(w i))
    (hw : ∀i,0≤ w i) (ap bp δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) :
    let src := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
      src second L alloc (fun i=>w i.val.val) (fun i=>σ i.val.val)
        (fun i=>v i.val.val) (fun i=>θ i.val.val) ap bp
    δ*D.total P-Cycle61.Physical.sourcePostClip src.toSource second Z L alloc≤
      δ*(Real.logb Z (preVolume s.toData)-Real.logb Z (C₁.absNorm:ℝ)-
        Real.logb Z (C₂.absNorm:ℝ)+2*(N:ℝ)*Real.logb Z b) := by
  intro src D
  exact (high_source_exponent_le_raw D hZ (fun i=>hscale i.val.val)
    (fun i=>hw i.val.val) δ hδ hδ').trans
    (mul_le_mul_of_nonneg_left
      (actual_two_stage_raw_log N b hb s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ Z hZ) hδ)

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.actual_two_stage_raw_log
#print axioms OAI.SevenEighths.Cycle61Moment.actual_two_stage_high_exponent
#print axioms OAI.SevenEighths.Cycle61Moment.actual_original_raw_cap
#print axioms OAI.SevenEighths.Cycle61Moment.eventually_two_stage_padding

#print axioms OAI.SevenEighths.Cycle61Moment.eventual_two_stage_common_raw_cap

end
/- END ORIGINAL Cycle61.Moment.HighCommonExponent -/
