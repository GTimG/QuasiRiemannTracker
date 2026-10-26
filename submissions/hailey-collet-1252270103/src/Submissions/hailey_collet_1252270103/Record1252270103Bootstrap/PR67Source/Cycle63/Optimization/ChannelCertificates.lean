import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Optimization.ChannelWindow
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Root
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The channels of the HIGH reserve keep the fee in every bin of the marked range and every cell of the
slot window, the HIGH reserve alone keeps it above the bin top, and the large-root tail of the root
cutoff dominates the capped gain in every bin of the marked range. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-- The root cutoff of the marked count: the dominance root cutoff of the junction, the largest of the
marked range (`dominantRoot_anti`). -/
def markedRootCutoff : ℝ := dominantRoot firstJunction

/-- The slope of the ledger's plane. -/
def ledgerSlope : ℝ := planeSlope lowRegionPrice lowRegionIntercept firstJunction

/-- The intercept of the ledger's plane. -/
def ledgerIntercept : ℝ := planeIntercept lowRegionPrice lowRegionIntercept firstJunction slotTop

bracket junction_enclosure (digits := 14) : firstJunction unfolding [firstJunction]
bracket markedRootCutoff_enclosure (digits := 14) : markedRootCutoff unfolding *
bracket ledgerSlope_bounds (digits := 14) : ledgerSlope unfolding *
bracket ledgerIntercept_bounds (digits := 14) : ledgerIntercept unfolding *

/-- The HIGH reserve of the ledger in the bin `d` and the cell `b`, less the fee. -/
def unmarkedMargin (d b : ℝ) : ℝ :=
  planeHigh lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b -
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop

/-- Unfolds the ledger quantities to rational expressions in the bin, the cell, the junction and the
plane. -/
macro "unfold_ledger_channels" : tactic => `(tactic|
  (simp only [Cycle63.Optimization.unmarkedMargin, Cycle63.Optimization.rateChannel,
    Cycle63.Optimization.linearChannel, Cycle63.Optimization.mixedChannel,
    Cycle63.Optimization.inverseChannel, Cycle63.Optimization.cappedChannel,
    Cycle63.Optimization.commonRateAt, Cycle63.Optimization.dominantRoot,
    Cycle63.Optimization.capCoefficient, Cycle63.Optimization.planeHigh,
    Cycle63.Optimization.planeFrequency, Cycle63.Optimization.planeAmplifier,
    Cycle63.Optimization.highFee, Cycle63.Optimization.inverseCapAt, Cycle63.Optimization.plainCapAt,
    Cycle63.Optimization.capUnitAt, Cycle63.Optimization.chosenPerUnit,
    Cycle63.Optimization.plainCapacityCost, Cycle63.Optimization.halfGain,
    Cycle63.Optimization.amplifierRatio, Cycle63.Optimization.lowRegionPrice,
    Cycle63.Optimization.lowRegionIntercept, Cycle63.Optimization.density,
    Cycle63.Optimization.regionPrice, Cycle63.Optimization.regionIntercept, Cycle63.Optimization.regionSlope,
    Cycle63.Optimization.secondRatio, Cycle63.Optimization.amplifierCost, Cycle63.Optimization.regionMargin,
    Cycle63.Optimization.secondJunction,
    Cycle63.Optimization.lowReserveAt, Cycle63.Optimization.markedLossAt, Cycle63.Optimization.markedRate,
    Cycle63.Optimization.markedPad, Cycle63.Optimization.markedBinWidth,
    Cycle63.Optimization.geometryLossCap, Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.allowanceUnit, Cycle63.Optimization.suppliedAt, Cycle63.Optimization.cellMesh,
    Cycle63.Optimization.supplyLoss, Cycle63.Optimization.commonAllocationLoss,
    Cycle63.Optimization.tinySlotLoss, Cycle63.Optimization.frequencyLossCap,
    Cycle63.Optimization.tailSlack, Cycle63.Optimization.slotTop,
    Cycle63.Optimization.firstCellTop, Cycle63.Optimization.slotFloor,
    Cycle63.Optimization.slotPrice, Cycle63.Optimization.betaBound]))

theorem unmarkedMargin_mono :
    StrictMonoOn (fun d => unmarkedMargin d slotTop) (Set.Icc (31/50) (3/4)) ∧
      ContinuousOn (fun d => unmarkedMargin d slotTop) (Set.Icc (31/50) (3/4)) := by
  unfold_ledger_channels
  rat_mono [junction_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds]

/-- The bin top: from it on the HIGH reserve alone keeps the fee in the top cell. -/
bracket_root binTop_spec (digits := 12) : (fun d => unmarkedMargin d slotTop) on (31/50) (3/4)
  by unmarkedMargin_mono
  using [junction_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds] unfolding *

/-- The bin top of the marked ledger: the lowest bin from which on the HIGH reserve alone keeps the
fee in the top cell. -/
def markedBinTop : ℝ := firstNonneg (fun d => unmarkedMargin d slotTop) (31/50) (3/4)

bracket binTop_enclosure (digits := 12) : markedBinTop using [binTop_spec.1] unfolding [markedBinTop]

theorem junction_le_binTop : firstJunction ≤ markedBinTop := by
  linarith [junction_enclosure.2, binTop_enclosure.1]

/-- The rate, linear, inverse and capped channels keep the fee strictly in every bin of the marked
range at both window ends. -/
theorem slack_channels {d b : ℝ} (hd : firstJunction ≤ d ∧ d ≤ markedBinTop)
    (hb : b = firstCellTop ∨ b = slotTop) :
    highFee lowRegionPrice lowRegionIntercept firstJunction slotTop <
        rateChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop <
          linearChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop <
        inverseChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop <
        cappedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b := by
  rcases hb with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold_ledger_channels <;>
    rat_pos [hd, junction_enclosure, binTop_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds,
      markedRootCutoff_enclosure]

/-- The mixed channel rises with the bin over the marked range at both window ends. -/
theorem mixed_channel_mono {b : ℝ} (hb : b = firstCellTop ∨ b = slotTop) :
    StrictMonoOn
        (fun d => mixedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b)
        (Set.Icc firstJunction markedBinTop) ∧
      ContinuousOn
          (fun d => mixedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b)
        (Set.Icc firstJunction markedBinTop) := by
  rcases hb with rfl | rfl <;> unfold_ledger_channels <;>
    rat_mono [junction_enclosure, binTop_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds,
      markedRootCutoff_enclosure]

/-- The dominance root cutoff falls with the bin over the marked range. -/
theorem dominantRoot_anti :
    StrictAntiOn (fun d => dominantRoot d) (Set.Icc firstJunction markedBinTop) ∧
      ContinuousOn (fun d => dominantRoot d) (Set.Icc firstJunction markedBinTop) := by
  unfold_ledger_channels
  rat_mono [junction_enclosure, binTop_enclosure]

/-- Above the bin top the HIGH reserve alone keeps the fee strictly in the lowest cell. -/
theorem unmarked_floor {d : ℝ} (hd : markedBinTop ≤ d ∧ d ≤ 3/4) : 0 < unmarkedMargin d firstCellTop := by
  unfold_ledger_channels
  rat_pos [hd, junction_enclosure, binTop_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds]

/-- The channel sum `q + W + W'` of the ledger's plane is positive. -/
theorem ledger_plane_sum_pos :
    0 < firstJunction + weight lowRegionPrice lowRegionIntercept firstJunction +
        plainWeight lowRegionPrice lowRegionIntercept firstJunction markedRootCutoff := by
  simp only [weight, plainWeight, plainCapAt, capUnitAt, chosenPerUnit, plainCapacityCost, halfGain,
    amplifierRatio, lowRegionPrice, lowRegionIntercept, density, slotPrice, betaBound, regionPrice,
    regionIntercept, regionSlope, secondRatio, amplifierCost, regionMargin, allowanceUnit, secondJunction]
  rat_pos [junction_enclosure, markedRootCutoff_enclosure]

/-- The mixed channel at the junction keeps exactly the fee in every cell. -/
theorem mixed_channel_junction (b : ℝ) :
    mixedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff firstJunction b =
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop :=
  mixed_channel_fee lowRegionPrice lowRegionIntercept ledger_plane_sum_pos.ne' slotTop b

/-! Every cell lies between the two window ends and every channel is affine in the cell. -/

/-- A function affine between two points keeps a lower bound that it keeps at both. -/
theorem affine_between {f : ℝ → ℝ} {lo hi b fee : ℝ}
    (haff : (hi - lo)*f b = (hi - b)*f lo + (b - lo)*f hi) (hb : lo ≤ b ∧ b ≤ hi) (hlohi : lo < hi)
    (hlo : fee ≤ f lo) (hhi : fee ≤ f hi) : fee ≤ f b := by
  have h1 := mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hlo)
  have h2 := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hhi)
  have hpos : 0 < hi - lo := sub_pos.mpr hlohi
  nlinarith

theorem window_ends : firstCellTop < slotTop := by
  norm_num [firstCellTop, slotFloor, cellMesh, allowanceUnit, slotTop]

macro "cell_affine" : tactic => `(tactic|
  (simp only [Cycle63.Optimization.rateChannel, Cycle63.Optimization.linearChannel,
    Cycle63.Optimization.mixedChannel, Cycle63.Optimization.inverseChannel,
    Cycle63.Optimization.cappedChannel, Cycle63.Optimization.planeHigh,
    Cycle63.Optimization.planeFrequency, Cycle63.Optimization.planeAmplifier,
    Cycle63.Optimization.suppliedAt]; ring))

/-- In every bin of the marked range and every cell of the slot window the five channels keep the
fee. -/
theorem ledger_channels {d b : ℝ} (hd : firstJunction ≤ d ∧ d ≤ markedBinTop)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
        rateChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
          linearChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
        mixedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
        inverseChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b ∧
      highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
        cappedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b := by
  have hlo := slack_channels hd (.inl rfl)
  have hhi := slack_channels hd (.inr rfl)
  have hdJ : d ∈ Set.Icc firstJunction markedBinTop := hd
  have hJ : firstJunction ∈ Set.Icc firstJunction markedBinTop := ⟨le_rfl, junction_le_binTop⟩
  have hmlo := (mixed_channel_mono (.inl rfl)).1.monotoneOn hJ hdJ hd.1
  have hmhi := (mixed_channel_mono (.inr rfl)).1.monotoneOn hJ hdJ hd.1
  simp only [mixed_channel_junction] at hmlo hmhi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact affine_between
      (f := fun b => rateChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b)
      (by cell_affine) hb window_ends hlo.1.le hhi.1.le
  · exact affine_between
      (f := fun b => linearChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b)
      (by cell_affine) hb window_ends hlo.2.1.le hhi.2.1.le
  · exact affine_between
      (f := fun b => mixedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b)
      (by cell_affine) hb window_ends hmlo hmhi
  · exact affine_between
      (f := fun b => inverseChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b)
      (by cell_affine) hb window_ends hlo.2.2.1.le hhi.2.2.1.le
  · exact affine_between
      (f := fun b => cappedChannel lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff d b)
      (by cell_affine) hb window_ends hlo.2.2.2.le hhi.2.2.2.le

/-- From the bin top on the HIGH reserve alone keeps the fee in every cell of the slot window. -/
theorem ledger_unmarked {d b : ℝ} (hd : markedBinTop ≤ d ∧ d ≤ 3/4)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    highFee lowRegionPrice lowRegionIntercept firstJunction slotTop ≤
        planeHigh lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b := by
  have hT : markedBinTop ∈ Set.Icc (31/50 : ℝ) (3/4) :=
    ⟨by linarith [binTop_enclosure.1], by linarith [hd.2, hd.1]⟩
  have hdT : d ∈ Set.Icc (31/50 : ℝ) (3/4) := ⟨by linarith [hT.1, hd.1], hd.2⟩
  have htop := unmarkedMargin_mono.1.monotoneOn hT hdT hd.1
  have hzero : unmarkedMargin markedBinTop slotTop = 0 := binTop_spec.2
  rw [hzero] at htop
  have hfloor := (unmarked_floor hd).le
  unfold unmarkedMargin at htop hfloor
  exact affine_between
      (f := fun b => planeHigh lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept d b)
    (by cell_affine) hb window_ends (by linarith) (by linarith)

/-- In every bin of the marked range the large-root tail of the ledger's root cutoff dominates the
capped gain: `c (1 - 6 r) ≤ r (6 ρ - 1 - tailSlack)` for the cap coefficient `c` of the bin. -/
theorem ledger_dominance {d : ℝ} (hd : firstJunction ≤ d ∧ d ≤ markedBinTop) :
    capCoefficient d*(1 - 6*markedRootCutoff) ≤ markedRootCutoff*(6*density d - 1 - tailSlack) := by
  have hdJ : d ∈ Set.Icc firstJunction markedBinTop := hd
  have hJ : firstJunction ∈ Set.Icc firstJunction markedBinTop := ⟨le_rfl, junction_le_binTop⟩
  have hr : dominantRoot d ≤ markedRootCutoff := dominantRoot_anti.1.antitoneOn hJ hdJ hd.1
  have hpos : 0 < (6*density d - 1 - tailSlack) + 6*capCoefficient d ∧ 0 ≤ capCoefficient d := by
    constructor <;> unfold_ledger_channels <;> (try apply le_of_lt) <;>
      rat_pos [hd, junction_enclosure, binTop_enclosure]
  unfold dominantRoot at hr
  rw [div_le_iff₀ hpos.1] at hr
  linarith

/-- In every bin of the marked range the half gain and both caps are positive, and the common rate
exceeds twice the slope of the capped gain. -/
theorem ledger_gain_facts {d : ℝ} (hd : firstJunction ≤ d ∧ d ≤ markedBinTop) :
    0 < halfGain d ∧ 0 < inverseCapAt d ∧ 0 < plainCapAt d ∧ 2*capCoefficient d < commonRateAt d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold_ledger_channels <;>
    rat_pos [hd, junction_enclosure, binTop_enclosure]

/-- In every cell of the slot window the live frequency exceeds twice the supplied width. -/
theorem supply_le_frequency {b : ℝ} (hb : firstCellTop ≤ b ∧ b ≤ slotTop) :
    2*suppliedAt b ≤
        planeFrequency lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept markedRootCutoff b := by
  have hcell := hb
  simp only [firstCellTop, slotFloor, cellMesh, allowanceUnit, slotTop] at hcell
  apply le_of_lt
  unfold_ledger_channels
  rat_pos [hcell, junction_enclosure, ledgerSlope_bounds, ledgerIntercept_bounds,
    markedRootCutoff_enclosure]

/-- In every bin of the marked range the cap coefficient is below `1/20`. -/
theorem capCoefficient_lt {d : ℝ} (hd : firstJunction ≤ d ∧ d ≤ markedBinTop) : capCoefficient d < 1/20 := by
  unfold_ledger_channels
  rat_pos [hd, junction_enclosure, binTop_enclosure]

/-- The loss of the marked count for slot sums up to the window top. -/
def markedLoss : ℝ := markedLossAt slotTop

theorem markedLoss_pos : 0 < markedLoss := markedLossAt_pos (by norm_num [slotTop])

/-- The core factor `1 - 6 r` of the root cutoff `r`: the share of the frequency left to the live
slots. -/
def coreFactor : ℝ := 1 - 6*markedRootCutoff

/-- The amplifier width of the top cell of the slot window, the largest of the cells. -/
def amplifierCap : ℝ :=
    planeAmplifier lowRegionPrice lowRegionIntercept firstJunction ledgerSlope ledgerIntercept slotTop

bracket markedBinTop_bounds (digits := 9) : markedBinTop using [binTop_enclosure] unfolding []
bracket markedRootCutoff_bounds (digits := 9) : markedRootCutoff using [markedRootCutoff_enclosure]
  unfolding []
bracket coreFactor_bounds (digits := 9) : coreFactor using [markedRootCutoff_enclosure]
  unfolding [coreFactor]
bracket amplifierCap_bounds (digits := 9) : amplifierCap
  using [ledgerSlope_bounds, ledgerIntercept_bounds] unfolding *

end

end Cycle63.Optimization

end Record1252270103Bootstrap.PR67
