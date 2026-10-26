/- The bin split and the caps of the marked count: the residual of the caps increases on the split
range, so the bin split is its root, and the constraints the caps meet with equality.
Released under Apache 2.0. -/
import Candidate.Cycle63.Optimization.MarkedCaps
import Candidate.Cycle63.Certificate.MonoTactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Certificate

/-- The balancing core cap increases with the bin split. -/
theorem balancedCoreCap_mono :
    StrictMonoOn (fun q => balancedCoreCap q) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => balancedCoreCap q) (Set.Icc (1/2) (37/50)) := by
  simp only [balancedCoreCap, frequencyFactorAt, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]
  rat_mono []

/-- The bin top of the price end increases with the bin split. -/
theorem priceEndBinTop_mono :
    StrictMonoOn (fun q => priceEndBinTop q) (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn (fun q => priceEndBinTop q) (Set.Icc (1/2) (37/50)) := by
  simp only [priceEndBinTop, priceEndGrowth, cellAmplifier, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]
  rat_mono []

/-- The bin top of the price end at the bottom of the split range. -/
bracket priceEndBinTop_low (digits := 6) : priceEndBinTop (1/2)
  unfolding [priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The bin top of the price end at the top of the split range. -/
bracket priceEndBinTop_high (digits := 6) : priceEndBinTop (37/50)
  unfolding [priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The bin tops of the split range. -/
def binTopRange : Set ℝ := Set.Icc (priceEndBinTop (1/2)) (priceEndBinTop (37/50))

/-- The core cap falls with the bin top: the cap unit falls and the root cutoff rises. -/
theorem coreCapAt_anti :
    StrictAntiOn (fun d => coreCapAt d) binTopRange ∧
      ContinuousOn (fun d => coreCapAt d) binTopRange := by
  simp only [binTopRange, coreCapAt, capUnitAt, rootCutoffAt, tailSlack, allowanceUnit, liveRate, liveRatio, chosenPerUnit,
    plainCapacityCost, halfGain, density]
  rat_mono [priceEndBinTop_low, priceEndBinTop_high]

/-- The residual of the caps increases on the split range: the balancing core cap rises, and the
core cap that the count provides falls since the bin top rises. -/
theorem capResidual_mono :
    StrictMonoOn capResidual (Set.Icc (1/2) (37/50)) ∧
      ContinuousOn capResidual (Set.Icc (1/2) (37/50)) := by
  obtain ⟨hB, hBc⟩ := balancedCoreCap_mono
  obtain ⟨hD, hDc⟩ := priceEndBinTop_mono
  obtain ⟨hC, hCc⟩ := coreCapAt_anti
  have hmaps : Set.MapsTo priceEndBinTop (Set.Icc (1/2) (37/50)) binTopRange := fun q hq =>
    ⟨hD.monotoneOn ⟨le_rfl, by norm_num⟩ hq hq.1, hD.monotoneOn hq ⟨by norm_num, le_rfl⟩ hq.2⟩
  refine ⟨fun x hx y hy hxy => ?_, ?_⟩
  · have hCxy := hC (hmaps hx) (hmaps hy) (hD hx hy hxy)
    have hBxy := hB hx hy hxy
    simp only at hCxy hBxy
    unfold capResidual
    linarith
  · unfold capResidual
    exact hBc.sub (hCc.comp hDc hmaps)

/-- The bin split is the root of the residual of the caps. -/
bracket_root markedSplit_spec (digits := 14) : capResidual on (1/2) (37/50) by capResidual_mono
  unfolding [capResidual, balancedCoreCap, frequencyFactorAt, coreCapAt, capUnitAt, rootCutoffAt, tailSlack, allowanceUnit, priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]

/-- An enclosure of the bin split. -/
bracket markedSplit_enclosure (digits := 14) : markedSplit using [markedSplit_spec.1]
  unfolding [markedSplit]

theorem capResidual_markedSplit : capResidual markedSplit = 0 := markedSplit_spec.2

/-! The constants at the bin split: enclosures, and the constraints met with equality. -/

bracket markedBinTop_bounds (digits := 9) : markedBinTop using [markedSplit_enclosure]
  unfolding [markedBinTop, priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

bracket capUnit_bounds (digits := 9) : capUnit using [markedBinTop_bounds]
  unfolding [capUnit, capUnitAt, chosenPerUnit, plainCapacityCost]

bracket inverseWidthCap_bounds (digits := 9) : inverseWidthCap using [capUnit_bounds]
  unfolding [inverseWidthCap]

bracket plainWidthCap_bounds (digits := 9) : plainWidthCap using [capUnit_bounds]
  unfolding [plainWidthCap, plainCapacityCost]

bracket chosenWidthCap_bounds (digits := 9) : chosenWidthCap using [capUnit_bounds]
  unfolding [chosenWidthCap, inverseWidthCap, plainWidthCap, plainCapacityCost]

bracket countSlope_bounds (digits := 9) : countSlope using [capUnit_bounds] unfolding [countSlope]

bracket markedRootCutoff_bounds (digits := 9) : markedRootCutoff
  using [markedBinTop_bounds, inverseWidthCap_bounds]
  unfolding [markedRootCutoff, rootCutoffAt, liveRate, liveRatio, chosenPerUnit,
    plainCapacityCost, halfGain, density, tailSlack, allowanceUnit]

bracket amplifierCap_bounds (digits := 9) : amplifierCap using [markedSplit_enclosure]
  unfolding [amplifierCap, priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

bracket coreFactor_bounds (digits := 9) : coreFactor using [markedRootCutoff_bounds]
  unfolding [coreFactor]

bracket frequencyFactor_bounds (digits := 9) : frequencyFactor using [amplifierCap_bounds]
  unfolding [frequencyFactor, frequencyLossCap, geometryLossCap, lowReserveWeight]

bracket liveFrequency_bounds (digits := 9) : liveFrequency
  using [coreFactor_bounds, frequencyFactor_bounds] unfolding [liveFrequency]

bracket reserveGrowth_bounds (digits := 9) : reserveGrowth using [markedSplit_enclosure]
  unfolding [reserveGrowth, priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit]

/-- The live cap is the one at which the capped live channel is tight in the top cell. -/
theorem liveCap_eq_balanced :
    liveCap = balancedCoreCap markedSplit*frequencyFactorAt markedSplit := by
  have h := capResidual_markedSplit
  have hcore : coreCapAt (priceEndBinTop markedSplit) = inverseWidthCap*coreFactor := rfl
  have hb : balancedCoreCap markedSplit = inverseWidthCap*coreFactor := by
    unfold capResidual at h
    rw [← hcore]
    linarith
  have hf : frequencyFactor = frequencyFactorAt markedSplit := rfl
  rw [hb, ← hf]
  unfold liveCap liveFrequency
  ring

/-- An enclosure of the live cap, through the balancing core cap of the bin split. -/
bracket liveCap_bounds (digits := 13) : liveCap via liveCap_eq_balanced
  using [markedSplit_enclosure]
  unfolding [balancedCoreCap, frequencyFactorAt, priceEndBinTop, priceEndGrowth, cellAmplifier, cellHigh, priceIntercept, lowReserveAt,
    movingSlope, suppliedAt, priceEndRate, slope, weight, amplifierRatio, density, slotTop, cellMesh,
    lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, allowanceUnit,
    liveRate, liveRatio, chosenPerUnit, plainCapacityCost, halfGain, frequencyLossCap]

theorem capUnit_pos : 0 < capUnit := by linarith [capUnit_bounds.1]

theorem inverseWidthCap_pos : 0 < inverseWidthCap := by
  unfold inverseWidthCap; linarith [capUnit_pos]

theorem plainWidthCap_pos : 0 < plainWidthCap := by
  have hu := capUnit_pos
  unfold plainWidthCap plainCapacityCost
  positivity

theorem liveRatio_eq : liveRatio = 22/27 := by
  unfold liveRatio chosenPerUnit plainCapacityCost; norm_num

theorem plainWidthCap_le_inverse : plainWidthCap ≤ inverseWidthCap := by
  have hu := capUnit_bounds
  unfold plainWidthCap inverseWidthCap plainCapacityCost
  norm_num
  linarith

/-- The inverse moment is used up to its capacity: `r_cap + 2 w_I = 1`. -/
theorem inverse_caps_sum : inverseLengthCap + 2*inverseWidthCap = 1 := by
  unfold inverseLengthCap countSlope inverseWidthCap; ring

/-- The plain moment is used up to its capacity: `2 m_cap + 6 κ_p w_P = 1`. -/
theorem plain_caps_sum : 2*plainLengthCap + 6*plainCapacityCost*plainWidthCap = 1 := by
  unfold plainLengthCap countSlope plainWidthCap plainCapacityCost; ring

/-- The count bound holds with equality at the bin top. -/
theorem count_slope_identity :
    (5 - 2*markedBinTop)*countSlope = 10/3 + chosenWidthCap*(5 - 6*markedBinTop) := by
  have hd := markedBinTop_bounds
  have hD : 0 < 5 - 2*markedBinTop + chosenPerUnit*(5 - 6*markedBinTop) := by
    unfold chosenPerUnit plainCapacityCost
    rat_pos [hd]
  have hu : capUnit*(5 - 2*markedBinTop + chosenPerUnit*(5 - 6*markedBinTop)) =
      5/3 - 2*markedBinTop := by
    unfold capUnit capUnitAt
    exact div_mul_cancel₀ _ hD.ne'
  have hk : chosenWidthCap = chosenPerUnit*capUnit := by
    unfold chosenWidthCap inverseWidthCap plainWidthCap chosenPerUnit
    ring
  rw [hk]
  unfold countSlope
  linear_combination (-1 : ℝ)*hu

/-- The large-root tail equals the live gain at the bin top. -/
theorem root_cutoff_balance :
    liveRate markedBinTop*(inverseWidthCap*coreFactor) =
      markedRootCutoff*(6*density markedBinTop - 1 - tailSlack) := by
  have hd := markedBinTop_bounds
  have hw := inverseWidthCap_bounds
  have hD : (6*density markedBinTop - 1 - tailSlack) + 6*liveRate markedBinTop*inverseWidthCap ≠ 0 := by
    apply ne_of_gt
    unfold liveRate liveRatio chosenPerUnit plainCapacityCost halfGain density tailSlack allowanceUnit
    rat_pos [hd, hw]
  have hκ : markedRootCutoff*((6*density markedBinTop - 1 - tailSlack) +
      6*liveRate markedBinTop*inverseWidthCap) = liveRate markedBinTop*inverseWidthCap := by
    unfold markedRootCutoff rootCutoffAt
    exact div_mul_cancel₀ _ hD
  unfold coreFactor
  linear_combination (-1 : ℝ)*hκ

/-- The bin top is where the growth of the HIGH reserve pays the net saving of the price end in the
top cell. -/
theorem bin_top_growth :
    priceEndRate markedSplit*suppliedAt slotTop - markedLoss =
      (markedBinTop - markedSplit)*reserveGrowth := by
  have hg := reserveGrowth_bounds
  have hg' : priceEndGrowth markedSplit ≠ 0 := by
    have : 0 < reserveGrowth := by linarith [hg.1]
    exact this.ne'
  unfold markedBinTop reserveGrowth priceEndBinTop
  rw [add_sub_cancel_left, div_mul_cancel₀ _ hg']

/-- The moving slope in closed form. -/
theorem movingSlope_closed {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) :
    movingSlope q = (430*q^2 - 399*q + 135)/(q*(24*q^2 - 34*q + 35)) := by
  have hE : (0:ℝ) < 24*q^2 - 34*q + 35 := planeQuadratic_pos q
  have h5 : (0:ℝ) < 5 - 2*q := by linarith
  have h9 : (0:ℝ) < 9 - 12*q := by linarith
  have h5' : (5:ℝ) - q*2 ≠ 0 := by linarith
  have h9' : (9:ℝ) - q*12 ≠ 0 := by linarith
  have hE' : (35:ℝ) - q*34 + q^2*24 ≠ 0 := by nlinarith
  have hsum : (q + weight q)*((9 - 12*q)*(5 - 2*q)) = q*(24*q^2 - 34*q + 35) := by
    unfold weight amplifierRatio density
    field_simp
    ring
  have hW : 0 < q + weight q := by
    have hpos : 0 < (q + weight q)*((9 - 12*q)*(5 - 2*q)) := by rw [hsum]; positivity
    exact pos_of_mul_pos_left hpos (by positivity)
  have hγ : priceEndRate q*(3*(5 - 2*q)) = -(6*q^2 - 73*q + 45) := by
    unfold priceEndRate density
    field_simp
    ring
  have hs := slope_closed h0 h1
  unfold movingSlope
  rw [hs]
  unfold planeQuadratic
  rw [eq_div_iff (by positivity), sub_mul]
  have e1 : 24*q*(q + 5)/(24*q^2 - 34*q + 35)*(q*(24*q^2 - 34*q + 35)) = 24*q^2*(q + 5) := by
    rw [div_mul_eq_mul_div, div_eq_iff hE.ne']
    ring
  have e2 : priceEndRate q/(q + weight q)*(q*(24*q^2 - 34*q + 35)) =
      priceEndRate q*((9 - 12*q)*(5 - 2*q)) := by
    rw [← hsum, div_mul_eq_mul_div, div_eq_iff hW.ne']
    ring
  rw [e1, e2]
  linear_combination (-(3 - 4*q))*hγ

/-- With the moving slope, the price channel is tight in every cell at the price intercept. -/
theorem price_tight (q b : ℝ) (hq : q + weight q ≠ 0) :
    cellHigh q (priceIntercept q) b + priceEndRate q*suppliedAt b - markedLoss - lowReserveAt q = 0 := by
  have hB : priceIntercept q*(q + weight q) =
      1 - density q + weight q - q*(movingSlope q - 1)*cellMesh - lowReserveWeight*(5 - 6*density q)
        - priceEndRate q*(cellMesh + supplyLoss) - markedLoss - lowReserveAt q := by
    unfold priceIntercept
    exact div_mul_cancel₀ _ hq
  have hlam : movingSlope q*(q + weight q) = q + 9/2*weight q - priceEndRate q := by
    unfold movingSlope slope
    rw [sub_mul, div_mul_cancel₀ _ hq, div_mul_cancel₀ _ hq]
  have hW : weight q = amplifierRatio q*(5 - 6*density q) := rfl
  unfold cellHigh cellAmplifier suppliedAt
  linear_combination (-1 : ℝ)*hB + b*hlam +
    (priceIntercept q - 1 + (9/2 - movingSlope q)*b)*hW

/-- At the bin split the capped live channel is tight in the top cell. -/
theorem cap_tight :
    cellHigh markedSplit (priceIntercept markedSplit) slotTop + liveRate markedSplit*liveCap
      - markedLoss - lowReserveAt markedSplit = 0 := by
  have hq := markedSplit_enclosure
  have hr : 0 < liveRate markedSplit := by
    unfold liveRate liveRatio chosenPerUnit plainCapacityCost halfGain
    rat_pos [hq]
  have hF : 0 < frequencyFactorAt markedSplit := by
    simp only [frequencyFactorAt, cellAmplifier, priceIntercept, lowReserveAt,
      movingSlope, priceEndRate, slope, weight, amplifierRatio, density, slotTop,
      cellMesh, lowReserveWeight, markedLoss, markedRate, markedPad, supplyLoss, commonAllocationLoss, tinySlotLoss,
      geometryLossCap, markedBinWidth, allowanceUnit, frequencyLossCap]
    rat_pos [hq]
  rw [liveCap_eq_balanced]
  unfold balancedCoreCap
  field_simp [hr.ne', hF.ne']
  ring

/-- At the bin split the price channel and the capped live channel are equal in the top cell. -/
theorem price_eq_live_top : priceEndRate markedSplit*suppliedAt slotTop = liveRate markedSplit*liveCap := by
  have hq := markedSplit_enclosure
  have hw : markedSplit + weight markedSplit ≠ 0 := by
    apply ne_of_gt
    unfold weight amplifierRatio density
    rat_pos [hq]
  have h1 := price_tight markedSplit slotTop hw
  have h2 := cap_tight
  linarith

end

end Cycle63.Optimization
