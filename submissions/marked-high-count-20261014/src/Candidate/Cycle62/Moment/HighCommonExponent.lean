import Candidate.Cycle62.Moment.HighRawExponent
import Candidate.Cycle62.Moment.WholeSourceDatum
import Candidate.Cycle62.Physical.FinalCapacity.Allocation
import Candidate.Cycle62.Physical.FinalCapacity.Affine

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentAllocatedChildCapacity CenteredMomentEligibleEnergy
open CenteredMomentSourceLiveColumn Cycle62FinalCapacity
open CenteredMomentEnergyState CenteredMomentDivisorAllocation
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity Filter
local notation "O" => HeckeFamily.O
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

omit [DecidableEq ι] in
/-- The original affine gate supplies the sharp raw-volume bound used by
the high ledger, in the cell chosen from the original slot sum. -/
theorem actual_original_raw_cap (s : Input ι) (Z M : ℝ) (hZ : 1<Z) (hM : 0<M)
    (hz : (17/500)*M≤∑i,Real.logb Z (s.P i) ∧
      (∑i,Real.logb Z (s.P i))≤(1/25)*M)
    (haffine : length Z s.X₁+length Z s.X₂+
      Cycle62.Arithmetic.lambda*(∑i,Real.logb Z (s.P i))≤Cycle62.Arithmetic.B*M) :
    Real.logb Z (preVolume s.toData)≤M*Cycle62.Arithmetic.totalA
      (Cycle62.Arithmetic.cellUpper
        (Cycle62.Moment.originalCell ((∑i,Real.logb Z (s.P i))/M))) := by
  have hh := (Cycle62.Moment.normalized_cell_bounds hM hz haffine).2.2.2.1
  change Real.logb Z (CenteredMomentAmplificationChildInput.volume s)≤_
  rw [input_volume_log]
  linarith [raw_log_le_length Z s.X₁ hZ s.X₁_pos,
    raw_log_le_length Z s.X₂ hZ s.X₂_pos]

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

omit [DecidableEq ι] in
/-- One threshold supplies the raw exponent in the actual common-shell
estimate. Both supported common allocations pay their logarithmic shifts;
the final character and Mellin height do not alter the source volume. -/
theorem eventual_two_stage_common_raw_cap (N : ℕ) (b ε : ℝ) (hb : 1≤b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(Mrow : ℝ),0<Mrow → Fintype.card ι≤N → s.upper≤b →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle62.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤
        Cycle62.Arithmetic.B*Mrow →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁),
      frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0 →
      ∀(χ₁ : Character)(t₁ : ℝ)(C₂ R₂ : Ideal O)
        (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂),
      (let first := child s C₁ R₁ B₁ χ₁ t₁;
        frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0) →
      ∀(χ₂ : Character)(t₂ a c₁ c₂ : ℝ),1/2≤a → a≤1 →
      c₁≤Real.logb Z (C₁.absNorm:ℝ) → c₂≤Real.logb Z (C₂.absNorm:ℝ) →
      (2*a-1)*Real.logb Z
        (preVolume (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂))≤
      (2*a-1)*(Mrow*Cycle62.Arithmetic.totalA (Cycle62.Arithmetic.cellUpper
        (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow)))-c₁-c₂)+ε := by
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
      Mrow*Cycle62.Arithmetic.totalA (Cycle62.Arithmetic.cellUpper
        (Cycle62.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow)))-c₁-c₂+ε := by
    change Real.logb Z (preVolume (commonData (child s C₁ R₁ B₁ χ₁ t₁) C₂ R₂ B₂))≤_
    linarith [hZ.2]
  have hh := mul_le_mul_of_nonneg_left hbase hδ
  nlinarith [mul_le_mul_of_nonneg_right hδ' hε.le]

variable (M : Ideal O) [NeZero M]
local instance highCommonFiniteQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual final high source, before the residual shell is summed.
All residual allocations share this exponent bound; the clipping term is
paid by its own normalization, and both common shifts come from support. -/
theorem actual_two_stage_high_exponent
    (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ R₁ s.ν s.W s.P≠0)
    (χ : Character) (t : ℝ) (C₂ R₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R₁ B₁ χ t).pools C₂)
    (hf₂ : let first := child s C₁ R₁ B₁ χ t
      frozenCoefficient B₂.val C₂ R₂ first.ν first.W first.P≠0)
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ) (hZ : 1<Z)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus≤M) (hQη : st.fixedModulus≤η₀.modulus)
    (z : O) (hz : st.radial.keep z) (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset (liveIndices B₂.val⊕Fin 2)))
    (w σ v : ι→ℝ) (θ : ι→RayQuotient.Characters M H)
    (hscale : ∀i,s.P i=Z^(w i))
    (hw : ∀i,0≤w i) (ap bp δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) :
    let src := commonData (child s C₁ R₁ B₁ χ t) C₂ R₂ B₂
    let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
      src second L alloc (fun i=>w i.val.val) (fun i=>σ i.val.val)
        (fun i=>v i.val.val) (fun i=>θ i.val.val) ap bp
    δ*D.total P-Cycle62.Physical.sourcePostClip src.toSource second Z L alloc≤
      δ*(Real.logb Z (preVolume s.toData)-Real.logb Z (C₁.absNorm:ℝ)-
        Real.logb Z (C₂.absNorm:ℝ)+2*(N:ℝ)*Real.logb Z b) := by
  intro src D
  exact (high_source_exponent_le_raw D hZ (fun i=>hscale i.val.val)
    (fun i=>hw i.val.val) δ hδ hδ').trans
    (mul_le_mul_of_nonneg_left
      (actual_two_stage_raw_log N b hb s hcard hs C₁ R₁ B₁ hf₁ χ t C₂ R₂ B₂ hf₂ Z hZ) hδ)

end
end OAI.SevenEighths.Cycle62Moment
#print axioms OAI.SevenEighths.Cycle62Moment.actual_two_stage_raw_log
#print axioms OAI.SevenEighths.Cycle62Moment.actual_two_stage_high_exponent
#print axioms OAI.SevenEighths.Cycle62Moment.actual_original_raw_cap
#print axioms OAI.SevenEighths.Cycle62Moment.eventually_two_stage_padding

#print axioms OAI.SevenEighths.Cycle62Moment.eventual_two_stage_common_raw_cap
