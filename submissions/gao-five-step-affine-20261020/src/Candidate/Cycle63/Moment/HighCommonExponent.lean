import Candidate.Cycle63.Moment.HighRawExponent
import Candidate.Cycle63.Moment.WholeSourceDatum
import Candidate.Cycle63.Physical.FinalCapacity.Allocation
import Candidate.Cycle63.Physical.FinalCapacity.Affine
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentSourceLiveColumn Cycle63FinalCapacity
open CenteredMomentEnergyState CenteredMomentDivisorAllocation
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity Filter
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Both actual frozen coefficients pay their common-ideal shifts. The
remaining error depends only on the original slot count and support. -/
theorem actual_two_stage_raw_log (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (Z : ℝ) (hZ : 1<Z) :
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

/-- Fixed support padding vanishes uniformly before either common
allocation, the source, or any residual divisor is chosen. -/
theorem eventually_two_stage_padding (N : ℕ) (b ε : ℝ) (hb : 1≤b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 2*(N:ℝ)*Real.logb Z b≤ε := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (b^(2*N))),
    eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ (pow_pos (zero_lt_one.trans_le hb) _) hbound
  rw [Real.logb_pow,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

variable (M : Ideal O) [NeZero M]
local instance highCommonFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end
end OAI.SevenEighths.Cycle63Moment
