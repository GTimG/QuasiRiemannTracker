/- The bin split `q0` minimizes the class bound over the bin splits and intercepts that the marked
ledger admits. Released under Apache 2.0. -/
import Candidate.Cycle63.Arithmetic.Constants
import Candidate.Cycle63.Certificate.MonoTactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Cycle63.Optimization

noncomputable section
open Cycle63.Arithmetic Cycle63.Certificate

/-! ### The ledger at an arbitrary bin split and intercept

At the bin split `q` with intercept `B` the price channel keeps the loss and the LOW reserve in every
cell exactly when `B ≤ priceIntercept q` (`price_tight`). The capped live channel must do so in the
top cell with the caps that the count provides at the bin top, and the smallest bin top is the one
at which the growth of the HIGH reserve above `q` covers the LOW reserve in the top cell. -/

/-- The growth rate of the HIGH reserve per unit of zero parameter above the bin split `q` in the
top cell, for the intercept `B`. -/
def growthAt (q B : ℝ) : ℝ :=
  50*(1 - 6*cellAmplifier q B slotTop)/(3*(5 - 2*q)^2) - (B - (movingSlope q - 1)*(slotTop - cellMesh))

/-- The smallest bin top at which the growth of the HIGH reserve above `q` covers the LOW reserve in
the top cell, for the intercept `B`. -/
def binTopAt (q B : ℝ) : ℝ := q + (lowReserveAt q - cellHigh q B slotTop)/growthAt q B

/-- The frequency factor of the live slots in the top cell for the intercept `B`. -/
def frequencyAt (q B : ℝ) : ℝ := 1 - 6*cellAmplifier q B slotTop - frequencyLossCap

/-- The intercept `B` is admissible at the bin split `q`: the price channel keeps the loss and the
LOW reserve in every cell, and the capped live channel does so in the top cell with the caps that
the count provides at the bin top `binTopAt q B`. -/
def Admissible (q B : ℝ) : Prop :=
  B ≤ priceIntercept q ∧
    lowReserveAt q + markedLoss ≤
      cellHigh q B slotTop + liveRate q*coreCapAt (binTopAt q B)*frequencyAt q B

/-- The level function of the class bound at the slope `lam`, the intercept `B` and the level `T`:
`rootPoly` at the zero parameter where the bound formula equals `T`. Where it is negative the class
bound exceeds `T` (`lt_thetaMin_of_signs`). -/
def levelAt (lam B T : ℝ) : ℝ := rootPoly lam B (deltaL lam T)

/-! ### Closed forms in the bin split -/

/-- Numerator of the moving slope. -/
def slopeNum (q : ℝ) : ℝ := 430*q^2 - 399*q + 135

/-- Denominator of the moving slope. -/
def slopeDen (q : ℝ) : ℝ := q*(24*q^2 - 34*q + 35)

/-- Numerator of the price intercept over `q (24 q^2 - 34 q + 35)^2`. -/
def interceptNum (q : ℝ) : ℝ :=
  96*q^4 + 344*q^3 - 540*q^2 + 700*q
    + cellMesh*(-4752*q^4 + 26732*q^3 - 30316*q^2 + 11505*q - 1350)
    + lowReserveWeight*(768*q^5 + 2176*q^4 - 6384*q^3 + 8840*q^2 - 4200*q)
    + supplyLoss*(-576*q^5 + 8256*q^4 - 20956*q^3 + 27656*q^2 - 18555*q + 4725)
    + markedLoss*(-576*q^4 + 2688*q^3 - 4572*q^2 + 4260*q - 1575)

/-- Denominator of the price intercept. -/
def interceptDen (q : ℝ) : ℝ := q*(24*q^2 - 34*q + 35)^2

theorem priceIntercept_closed {q : ℝ} (h0 : 0 < q) (h1 : q < 3/4) :
    priceIntercept q = interceptNum q/interceptDen q := by
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  have h9 : (9:ℝ) - 12*q ≠ 0 := by linarith
  have hq : q ≠ 0 := h0.ne'
  have hE := (planeQuadratic_pos q).ne'
  have hw := plane_sum_closed h5 h9 1
  rw [one_mul] at hw
  have hN : (9 - 12*q)*(5 - 2*q) + 2*1*(22*q - 5) = planeQuadratic q := by unfold planeQuadratic; ring
  rw [hN] at hw
  have hsl : movingSlope q = (430*q^2 - 399*q + 135)/(q*planeQuadratic q) := by
    rw [movingSlope_closed h0 h1]; rfl
  have h5' := h5; ring_nf at h5'
  have h9' := h9; ring_nf at h9'
  have hd : interceptDen q = q*planeQuadratic q^2 := by unfold interceptDen planeQuadratic; ring
  unfold priceIntercept lowReserveAt priceEndRate
  rw [hw, hsl, weight_closed h5 h9, hd]
  unfold density
  field_simp
  unfold interceptNum planeQuadratic
  ring

/-- The point where the bound formula equals `T`, at the slope `a/b`, has numerator `a (9 T - 7)`. -/
theorem deltaL_div (a b T : ℝ) (hb : b ≠ 0) (hf : (7 - 6*T)*a + (11 - 12*T)*b ≠ 0) :
    deltaL (a/b) T = a*(9*T - 7)/((7 - 6*T)*a + (11 - 12*T)*b) := by
  unfold deltaL
  rw [div_eq_div_iff (by
      intro h
      apply hf
      field_simp at h
      linarith) hf]
  field_simp
  ring

/-- `rootPoly` at a slope, an intercept and a zero parameter given as fractions. -/
def rootPolyCleared (a b c d e f : ℝ) : ℝ :=
  (7*a*d*f + 6*e*c*b)*((25/2*a - 10*b)*f + (6*b - 9*a)*e)
    - 18*a*(5/6*f - e)*((25/2*a - 10*b)*d*f + (6*b*d - 6*a*d - 3*b*c)*e)

theorem rootPoly_div (a b c d e f : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) :
    rootPoly (a/b) (c/d) (e/f) = rootPolyCleared a b c d e f/(b^2*d*f^2) := by
  unfold rootPoly rootPolyCleared
  field_simp

/-- The level function along the price intercept, in closed form. -/
def priceLevelClosed (q T : ℝ) : ℝ :=
  rootPolyCleared (slopeNum q) (slopeDen q) (interceptNum q) (interceptDen q)
      (slopeNum q*(9*T - 7)) ((7 - 6*T)*slopeNum q + (11 - 12*T)*slopeDen q) /
    (slopeDen q^2*interceptDen q*((7 - 6*T)*slopeNum q + (11 - 12*T)*slopeDen q)^2)

/-- Left of the bin split the level function of the price intercept increases. -/
theorem priceLevelClosed_mono :
    StrictMonoOn (fun q => priceLevelClosed q (thetaMin lambda B)) (Set.Icc (1/2) q0) ∧
      ContinuousOn (fun q => priceLevelClosed q (thetaMin lambda B)) (Set.Icc (1/2) q0) := by
  have hq := q0_bounds
  have hT := thetaClass_bounds
  simp only [priceLevelClosed, rootPolyCleared, slopeNum, slopeDen, interceptNum, interceptDen,
    cellMesh, lowReserveWeight, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, markedLoss, markedRate, markedPad, slotTop, allowanceUnit]
  rat_mono [hq, hT]

/-- The intercept at which the level function at the slope `a/b` and the zero parameter `e/f`
vanishes, as a fraction. -/
def levelInterceptNum (a b e f : ℝ) : ℝ :=
  -(7*a*((25/2*a - 10*b)*f + (6*b - 9*a)*e)*f
    - 18*a*(5/6*f - e)*((25/2*a - 10*b)*f + (6*b - 6*a)*e))

/-- Denominator of the level intercept. -/
def levelInterceptDen (a b e f : ℝ) : ℝ :=
  b*(6*e*((25/2*a - 10*b)*f + (6*b - 9*a)*e) + 54*a*e*(5/6*f - e))

/-- `cellHigh` in the top cell is affine in the intercept. -/
theorem cellHigh_affine (q B : ℝ) :
    cellHigh q B slotTop = cellHigh q 0 slotTop - (q + weight q)*B := by
  unfold cellHigh cellAmplifier weight
  ring

/-- `growthAt` is affine in the intercept. -/
theorem growthAt_affine (q B : ℝ) :
    growthAt q B = growthAt q 0 - (growthAt q 0 - growthAt q 1)*B := by
  unfold growthAt cellAmplifier
  ring

/-- `frequencyAt` is affine in the intercept. -/
theorem frequencyAt_affine (q B : ℝ) :
    frequencyAt q B = frequencyAt q 0 - 6*amplifierRatio q*B := by
  unfold frequencyAt cellAmplifier
  ring

/-! ### The level function at the bin split -/

/-- `deltaL` inverts `boundAt`. -/
theorem deltaL_boundAt {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 ≤ δ) :
    deltaL lam (boundAt lam δ) = δ := by
  have hE : 0 < 9*lam + 6*lam*δ + 12*δ := by positivity
  have hnum : 9*boundAt lam δ - 7 = 3*δ*(7*lam + 5)/(9*lam + 6*lam*δ + 12*δ) := by
    unfold boundAt; field_simp; ring
  have hden : 7*lam + 11 - 6*lam*boundAt lam δ - 12*boundAt lam δ =
      3*lam*(7*lam + 5)/(9*lam + 6*lam*δ + 12*δ) := by
    unfold boundAt; field_simp; ring
  unfold deltaL
  rw [hnum, hden]
  have h7 : 0 < 7*lam + 5 := by linarith
  field_simp

/-- At the bin split the level function vanishes at the class bound. -/
theorem levelAt_split : levelAt lambda B (thetaMin lambda B) = 0 := by
  have hl := lambda_bounds
  have hB := B_bounds
  have ha : rootA2 lambda B < 0 := by unfold rootA2; rat_pos [hl, hB]
  have hdisc : 0 < rootDisc lambda B := by
    unfold rootDisc discrim rootA2 rootA1 rootA0; rat_pos [hl, hB]
  have hδs : 0 ≤ deltaStar lambda B := le_trans (by norm_num) deltaStar_bounds.1
  unfold levelAt thetaMin
  rw [deltaL_boundAt (by linarith [hl.1]) hδs]
  exact rootPoly_deltaStar ha.ne hdisc.le

/-- The numerator of the moving slope is positive. -/
theorem slopeNum_pos (q : ℝ) : 0 < slopeNum q := by
  unfold slopeNum; nlinarith [sq_nonneg (q - 399/860)]

/-- The denominator of the point where the bound formula equals `T`, at the moving slope. -/
def levelDen (q T : ℝ) : ℝ := (7 - 6*T)*slopeNum q + (11 - 12*T)*slopeDen q

theorem levelDen_pos {q T : ℝ} (h0 : 0 < q) (hT : T < 7/8) : 0 < levelDen q T := by
  have hE : (0:ℝ) < 24*q^2 - 34*q + 35 := planeQuadratic_pos q
  have hb : 0 < slopeDen q := by unfold slopeDen; positivity
  have h7 := mul_pos (by linarith : (0:ℝ) < 7 - 6*T) (slopeNum_pos q)
  have h11 := mul_pos (by linarith : (0:ℝ) < 11 - 12*T) hb
  unfold levelDen; linarith

/-- The level function along the price intercept equals its closed form. -/
theorem priceLevel_closed {q T : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (hT : T < 7/8) :
    levelAt (movingSlope q) (priceIntercept q) T = priceLevelClosed q T := by
  have hE : (0:ℝ) < 24*q^2 - 34*q + 35 := planeQuadratic_pos q
  have hb : slopeDen q ≠ 0 := by unfold slopeDen; positivity
  have hd : interceptDen q ≠ 0 := by unfold interceptDen; positivity
  have hf := (levelDen_pos h0 hT).ne'
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  unfold levelDen at hf
  unfold levelAt
  rw [hsl, priceIntercept_closed h0 h1, deltaL_div _ _ T hb hf, rootPoly_div _ _ _ _ _ _ hb hd hf]
  rfl

/-- Left of the bin split the level function of the price intercept is negative. -/
theorem price_level_neg {q : ℝ} (hq : 1/2 ≤ q) (hlt : q < q0) :
    levelAt (movingSlope q) (priceIntercept q) (thetaMin lambda B) < 0 := by
  have hq0 := q0_bounds
  have hT2 : thetaMin lambda B < 7/8 := by linarith [thetaClass_bounds.2]
  have hm := priceLevelClosed_mono.1 ⟨hq, hlt.le⟩ ⟨by linarith [hq0.1], le_rfl⟩ hlt
  simp only at hm
  rw [← priceLevel_closed (by linarith) (by linarith [hq0.2]) hT2,
    ← priceLevel_closed (by linarith [hq0.1]) (by linarith [hq0.2]) hT2] at hm
  exact hm.trans_eq levelAt_split

/-- Far right of the bin split the level function of the price intercept is negative too: there the
price channel alone keeps the class bound above the one at the bin split. -/
theorem far_level_neg {q : ℝ} (hq : 7/10 ≤ q) (hq' : q ≤ 37/50) :
    levelAt (movingSlope q) (priceIntercept q) (thetaMin lambda B) < 0 := by
  have hT := thetaClass_bounds
  rw [priceLevel_closed (by linarith) (by linarith) (by linarith [hT.2])]
  have hqi : q ∈ Set.Icc (7/10:ℝ) (37/50) := ⟨hq, hq'⟩
  simp only [priceLevelClosed, rootPolyCleared, slopeNum, slopeDen, interceptNum, interceptDen,
    cellMesh, lowReserveWeight, supplyLoss, commonAllocationLoss, tinySlotLoss, geometryLossCap,
    markedBinWidth, markedLoss, markedRate, markedPad, slotTop, allowanceUnit]
  rat_pos [hqi, hT]

/-! ### Right of the bin split: the capped live channel

At each slope the level function is affine in the intercept with a positive coefficient, so it is
positive exactly above the level intercept. Right of the bin split, up to `7/10`, an intercept above
the level intercept fails the capped live channel in the top cell: the bin top and the balancing core
cap rise with the intercept, and along the level intercept they rise with the bin split, so the core
cap that the count provides falls below the balancing one. -/

/-- The level intercept at the bin split `q` for the level `T`: the root in the intercept of the
level function at the moving slope (`rightIntercept_level`). -/
def rightIntercept (q T : ℝ) : ℝ :=
  levelInterceptNum (slopeNum q) (slopeDen q) (slopeNum q*(9*T - 7)) (levelDen q T) /
    levelInterceptDen (slopeNum q) (slopeDen q) (slopeNum q*(9*T - 7)) (levelDen q T)

/-- The cleared `rootPoly` vanishes at the cleared level intercept. -/
theorem rootPolyCleared_levelIntercept (a b e f : ℝ) :
    rootPolyCleared a b (levelInterceptNum a b e f) (levelInterceptDen a b e f) e f = 0 := by
  unfold rootPolyCleared levelInterceptNum levelInterceptDen
  ring

/-- The coefficient of the intercept in the level function. -/
def levelCoef (lam δ : ℝ) : ℝ := 6*δ*((25/2*lam - 10 + (6 - 9*lam)*δ) + 9*lam*(5/6 - δ))

/-- The level function is affine in the intercept. -/
theorem levelAt_sub (lam B B' T : ℝ) :
    levelAt lam B' T - levelAt lam B T = (B' - B)*levelCoef lam (deltaL lam T) := by
  unfold levelAt levelCoef
  exact rootPoly_intercept lam B B' (deltaL lam T)

/-- The intercept enters the level function with a positive coefficient where `deltaL` lies in
`(0, 5/6)` and the cutoff denominator is nonnegative. -/
theorem levelCoef_pos {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ < 5/6)
    (hd : 0 ≤ 25/2*lam - 10 + (6 - 9*lam)*δ) : 0 < levelCoef lam δ := by
  unfold levelCoef
  have : 0 < 9*lam*(5/6 - δ) := by nlinarith
  positivity

/-- `bin top = q + (n₀ + n₁ B)/(g₀ - g₁ B)` rises with the intercept where its coefficient
`n₁ g₀ + g₁ n₀` is positive and the denominator stays positive. -/
theorem frac_mono {n0 n1 g0 g1 B B' : ℝ} (hc : 0 < n1*g0 + g1*n0) (hB : B ≤ B')
    (hg : 0 < g0 - g1*B) (hg' : 0 < g0 - g1*B') :
    (n0 + n1*B)/(g0 - g1*B) ≤ (n0 + n1*B')/(g0 - g1*B') := by
  rw [div_le_div_iff₀ hg hg']
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) hc.le]

theorem binTopAt_affine (q B : ℝ) :
    binTopAt q B = q + ((lowReserveAt q - cellHigh q 0 slotTop) + (q + weight q)*B) /
      (growthAt q 0 - (growthAt q 0 - growthAt q 1)*B) := by
  unfold binTopAt
  rw [cellHigh_affine, growthAt_affine q B]
  ring_nf

/-- The balancing core cap at the intercept `B`. -/
def balancedAt (q B : ℝ) : ℝ :=
  (lowReserveAt q + markedLoss - cellHigh q B slotTop)/(liveRate q*frequencyAt q B)

/-- The balancing core cap as a fraction affine in the intercept. -/
theorem balancedAt_affine (q B : ℝ) :
    balancedAt q B = ((lowReserveAt q + markedLoss - cellHigh q 0 slotTop) + (q + weight q)*B) /
      (liveRate q*frequencyAt q 0 - liveRate q*(6*amplifierRatio q)*B) := by
  unfold balancedAt
  rw [cellHigh_affine, frequencyAt_affine q B]
  ring_nf

/-- The HIGH reserve of the top cell at the intercept `0`, at the slope `lam`. -/
def highConstAt (q lam : ℝ) : ℝ :=
  1 - density q - q*(0 - (lam - 1)*(slotTop - cellMesh))
    - (amplifierRatio q*(0 - 1 + (9/2 - lam)*slotTop) + lowReserveWeight)*(5 - 6*density q)

/-- The growth of the HIGH reserve in the top cell at the intercept `0`, at the slope `lam`. -/
def growthConstAt (q lam : ℝ) : ℝ :=
  50*(1 - 6*(amplifierRatio q*(0 - 1 + (9/2 - lam)*slotTop) + lowReserveWeight))/(3*(5 - 2*q)^2)
    - (0 - (lam - 1)*(slotTop - cellMesh))

/-- The fall of the growth per unit of intercept. -/
def growthSlope (q : ℝ) : ℝ := 100*amplifierRatio q/(5 - 2*q)^2 + 1

/-- The frequency factor in the top cell at the intercept `0`, at the slope `lam`. -/
def frequencyConstAt (q lam : ℝ) : ℝ :=
  1 - 6*(amplifierRatio q*(0 - 1 + (9/2 - lam)*slotTop) + lowReserveWeight) - frequencyLossCap

theorem cellHigh_zero (q : ℝ) : cellHigh q 0 slotTop = highConstAt q (movingSlope q) := by
  unfold cellHigh cellAmplifier highConstAt; ring

theorem growthAt_zero (q : ℝ) : growthAt q 0 = growthConstAt q (movingSlope q) := by
  unfold growthAt cellAmplifier growthConstAt; ring

theorem growthAt_fall (q : ℝ) (h5 : (5:ℝ) - 2*q ≠ 0) : growthAt q 0 - growthAt q 1 = growthSlope q := by
  unfold growthAt cellAmplifier growthSlope
  field_simp
  ring

theorem frequencyAt_zero (q : ℝ) : frequencyAt q 0 = frequencyConstAt q (movingSlope q) := by
  unfold frequencyAt cellAmplifier frequencyConstAt; ring

/-- The numerator and denominator of the level intercept at the bin split `q`. -/
def interceptLevelNum (q T : ℝ) : ℝ :=
  levelInterceptNum (slopeNum q) (slopeDen q) (slopeNum q*(9*T - 7)) (levelDen q T)

def interceptLevelDen (q T : ℝ) : ℝ :=
  levelInterceptDen (slopeNum q) (slopeDen q) (slopeNum q*(9*T - 7)) (levelDen q T)

/-- The bin top along the level intercept, in closed form. -/
def binTopCurve (q T : ℝ) : ℝ :=
  q + ((lowReserveAt q - highConstAt q (slopeNum q/slopeDen q))*interceptLevelDen q T
        + (q + weight q)*interceptLevelNum q T) /
    (growthConstAt q (slopeNum q/slopeDen q)*interceptLevelDen q T
        - growthSlope q*interceptLevelNum q T)

/-- The balancing core cap along the level intercept, in closed form. -/
def balancedCurve (q T : ℝ) : ℝ :=
  ((lowReserveAt q + markedLoss - highConstAt q (slopeNum q/slopeDen q))*interceptLevelDen q T
      + (q + weight q)*interceptLevelNum q T) /
    (liveRate q*(frequencyConstAt q (slopeNum q/slopeDen q)*interceptLevelDen q T
      - 6*amplifierRatio q*interceptLevelNum q T))

/-- Along the level intercept the bin top rises with the bin split. -/
theorem binTopCurve_mono :
    StrictMonoOn (fun q => binTopCurve q (thetaMin lambda B)) (Set.Icc q0 (7/10)) ∧
      ContinuousOn (fun q => binTopCurve q (thetaMin lambda B)) (Set.Icc q0 (7/10)) := by
  have hq := q0_bounds
  have hT := thetaClass_bounds
  simp only [binTopCurve, highConstAt, growthConstAt, growthSlope, interceptLevelNum,
    interceptLevelDen, levelInterceptNum, levelInterceptDen, levelDen, slopeNum, slopeDen,
    lowReserveAt, weight, amplifierRatio, density, slotTop, cellMesh, lowReserveWeight,
    allowanceUnit]
  rat_mono [hq, hT]

/-- Along the level intercept the balancing core cap rises with the bin split. -/
theorem balancedCurve_mono :
    StrictMonoOn (fun q => balancedCurve q (thetaMin lambda B)) (Set.Icc q0 (7/10)) ∧
      ContinuousOn (fun q => balancedCurve q (thetaMin lambda B)) (Set.Icc q0 (7/10)) := by
  have hq := q0_bounds
  have hT := thetaClass_bounds
  simp only [balancedCurve, highConstAt, frequencyConstAt, interceptLevelNum, interceptLevelDen,
    levelInterceptNum, levelInterceptDen, levelDen, slopeNum, slopeDen, lowReserveAt, weight,
    amplifierRatio, density, slotTop, cellMesh, lowReserveWeight, allowanceUnit, markedLoss,
    markedRate, markedPad, geometryLossCap, markedBinWidth, frequencyLossCap, liveRate, liveRatio,
    chosenPerUnit, plainCapacityCost, halfGain]
  rat_mono [hq, hT]

/-! ### Ranges of the moving slope and of the level point on the split range -/

/-- The moving slope on the split range lies in `[7/2, 9/2]`. -/
theorem movingSlope_mem {q : ℝ} (hq : q ∈ splitRange) : 7/2 ≤ movingSlope q ∧ movingSlope q ≤ 9/2 := by
  obtain ⟨h0, h1⟩ := mem_splitRange hq
  have hq' : q ∈ Set.Icc (1/2:ℝ) (37/50) := hq
  rw [movingSlope_closed h0 h1]
  constructor <;> (apply le_of_lt; rat_pos [hq'])

/-- At slopes in `[7/2, 9/2]` the level point of the class bound at the bin split lies in `(0, 3/5)`,
the cutoff denominator is positive there and at `3/5`, and `rootPoly` at `3/5` is positive for every
positive intercept. -/
theorem level_point_mem {lam : ℝ} (hlam : 7/2 ≤ lam ∧ lam ≤ 9/2) :
    0 < deltaL lam (thetaMin lambda B) ∧ deltaL lam (thetaMin lambda B) < 3/5 ∧
      0 < 7*lam + 11 - 6*lam*thetaMin lambda B - 12*thetaMin lambda B ∧
      0 < 25/2*lam - 10 + (6 - 9*lam)*deltaL lam (thetaMin lambda B) ∧
      0 < rootPoly lam 0 (3/5) := by
  have hT := thetaClass_bounds
  have hl : lam ∈ Set.Icc (7/2:ℝ) (9/2) := hlam
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold deltaL; rat_pos [hl, hT]
  · unfold deltaL; rat_pos [hl, hT]
  · rat_pos [hl, hT]
  · unfold deltaL; rat_pos [hl, hT]
  · unfold rootPoly; rat_pos [hl]

/-- Where the level function at the class bound of the bin split is negative, the class bound is
larger. -/
theorem lt_thetaMin_of_level {lam x : ℝ} (hlam : 7/2 ≤ lam ∧ lam ≤ 9/2) (hx : 0 < x)
    (hneg : levelAt lam x (thetaMin lambda B) < 0) : thetaMin lambda B < thetaMin lam x := by
  obtain ⟨hd0, hd1, hK, -, hr⟩ := level_point_mem hlam
  have hT := thetaClass_bounds
  have hhigh : 0 < rootPoly lam x (3/5) :=
    lt_of_lt_of_le hr (rootPoly_mono_intercept (by linarith [hlam.1]) (by norm_num) (by norm_num)
      (by nlinarith [hlam.1]) hx.le)
  exact lt_thetaMin_of_signs (by linarith [hlam.1]) hx (by linarith [hT.1]) hK hd1 hneg hhigh

/-- The level function rises with the intercept at slopes in `[7/2, 9/2]`. -/
theorem levelAt_mono {lam x x' : ℝ} (hlam : 7/2 ≤ lam ∧ lam ≤ 9/2) (hxx : x ≤ x') :
    levelAt lam x (thetaMin lambda B) ≤ levelAt lam x' (thetaMin lambda B) := by
  obtain ⟨hd0, hd1, -, hc, -⟩ := level_point_mem hlam
  have hcoef := levelCoef_pos (by linarith [hlam.1]) hd0 (by linarith) hc.le
  have h := levelAt_sub lam x x' (thetaMin lambda B)
  nlinarith [mul_nonneg (sub_nonneg.mpr hxx) hcoef.le]

theorem levelAt_strictMono {lam x x' : ℝ} (hlam : 7/2 ≤ lam ∧ lam ≤ 9/2) (hxx : x < x') :
    levelAt lam x (thetaMin lambda B) < levelAt lam x' (thetaMin lambda B) := by
  obtain ⟨hd0, hd1, -, hc, -⟩ := level_point_mem hlam
  have hcoef := levelCoef_pos (by linarith [hlam.1]) hd0 (by linarith) hc.le
  have h := levelAt_sub lam x x' (thetaMin lambda B)
  nlinarith [mul_pos (sub_pos.mpr hxx) hcoef]

/-- The level intercept is the root of the level function at the moving slope. -/
theorem rightIntercept_level {q T : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (hT' : T < 7/8)
    (hG : interceptLevelDen q T ≠ 0) :
    levelAt (movingSlope q) (rightIntercept q T) T = 0 := by
  have hE : (0:ℝ) < 24*q^2 - 34*q + 35 := planeQuadratic_pos q
  have hb : slopeDen q ≠ 0 := by unfold slopeDen; positivity
  have hf := (levelDen_pos h0 hT').ne'
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  unfold interceptLevelDen at hG
  unfold levelAt rightIntercept
  unfold levelDen at hf hG ⊢
  rw [hsl, deltaL_div _ _ T hb hf, rootPoly_div _ _ _ _ _ _ hb hG hf, rootPolyCleared_levelIntercept,
    zero_div]

/-- The level intercept at the moving slope in closed form, as used in the curve certificates. -/
theorem rightIntercept_eq (q T : ℝ) :
    rightIntercept q T = interceptLevelNum q T/interceptLevelDen q T := rfl

/-- Clearing the inner denominator of an intercept `A/G` in a fraction affine in the intercept. -/
theorem frac_clear (a b c d A G : ℝ) (hG : G ≠ 0) :
    (a + b*(A/G))/(c - d*(A/G)) = (a*G + b*A)/(c*G - d*A) := by
  rw [← mul_div_mul_right _ _ hG]
  congr 1 <;> field_simp

theorem balanced_curve_eq {q T : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (hG : interceptLevelDen q T ≠ 0) :
    balancedAt q (rightIntercept q T) = balancedCurve q T := by
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  rw [balancedAt_affine, rightIntercept_eq, frac_clear _ _ _ _ _ _ hG, cellHigh_zero, frequencyAt_zero,
    hsl]
  unfold balancedCurve
  congr 1
  ring

theorem interceptLevelDen_pos {q : ℝ} (hq : q ∈ Set.Icc q0 (7/10)) :
    0 < interceptLevelDen q (thetaMin lambda B) := by
  have hq0 := q0_bounds
  have hT := thetaClass_bounds
  simp only [interceptLevelDen, levelInterceptDen, levelDen, slopeNum, slopeDen]
  rat_pos [hq, hq0, hT]

/-- The coefficient of the intercept in the bin top is positive. -/
theorem binTop_coef_pos {q : ℝ} (hq : q ∈ Set.Icc q0 (7/10)) :
    0 < (q + weight q)*growthAt q 0 + (growthAt q 0 - growthAt q 1)*(lowReserveAt q - cellHigh q 0 slotTop) := by
  have hq0 := q0_bounds
  have h0 : 0 < q := by linarith [hq.1, hq0.1]
  have h1 : q < 3/4 := by linarith [hq.2]
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  rw [growthAt_fall q h5, cellHigh_zero, growthAt_zero, hsl]
  simp only [highConstAt, growthConstAt, growthSlope, slopeNum, slopeDen, lowReserveAt, weight,
    amplifierRatio, density, slotTop, cellMesh, lowReserveWeight, allowanceUnit]
  rat_pos [hq, hq0]

/-- The coefficient of the intercept in the balancing core cap is positive. -/
theorem balanced_coef_pos {q : ℝ} (hq : q ∈ Set.Icc q0 (7/10)) :
    0 < (q + weight q)*(liveRate q*frequencyAt q 0) +
      liveRate q*(6*amplifierRatio q)*(lowReserveAt q + markedLoss - cellHigh q 0 slotTop) := by
  have hq0 := q0_bounds
  have h0 : 0 < q := by linarith [hq.1, hq0.1]
  have h1 : q < 3/4 := by linarith [hq.2]
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  rw [cellHigh_zero, frequencyAt_zero, hsl]
  simp only [highConstAt, frequencyConstAt, slopeNum, slopeDen, lowReserveAt, weight, amplifierRatio,
    density, slotTop, cellMesh, lowReserveWeight, allowanceUnit, markedLoss, markedRate, markedPad,
    geometryLossCap, markedBinWidth, frequencyLossCap, liveRate, liveRatio, chosenPerUnit,
    plainCapacityCost, halfGain]
  rat_pos [hq, hq0]

/-- At the price intercept the growth and the live frequency are positive on the right range. -/
theorem price_growth_frequency_pos {q : ℝ} (hq : q ∈ Set.Icc q0 (7/10)) :
    0 < growthAt q 0 - (growthAt q 0 - growthAt q 1)*priceIntercept q ∧
      0 < liveRate q*frequencyAt q 0 - liveRate q*(6*amplifierRatio q)*priceIntercept q := by
  have hq0 := q0_bounds
  have h0 : 0 < q := by linarith [hq.1, hq0.1]
  have h1 : q < 3/4 := by linarith [hq.2]
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  rw [growthAt_fall q h5, growthAt_zero, frequencyAt_zero, hsl, priceIntercept_closed h0 h1]
  constructor
  · simp only [growthConstAt, growthSlope, slopeNum, slopeDen, interceptNum, interceptDen, amplifierRatio,
      slotTop, cellMesh, lowReserveWeight, allowanceUnit, supplyLoss, commonAllocationLoss, tinySlotLoss,
      geometryLossCap, markedBinWidth, markedLoss, markedRate, markedPad]
    rat_pos [hq, hq0]
  · simp only [frequencyConstAt, slopeNum, slopeDen, interceptNum, interceptDen, amplifierRatio, slotTop,
      cellMesh, lowReserveWeight, allowanceUnit, supplyLoss, commonAllocationLoss, tinySlotLoss,
      geometryLossCap, markedBinWidth, markedLoss, markedRate, markedPad, frequencyLossCap, liveRate,
      liveRatio, chosenPerUnit, plainCapacityCost, halfGain]
    rat_pos [hq, hq0]

/-! ### The capped live channel right of the bin split -/

/-- At the bin split the level intercept is the intercept of the ledger. -/
theorem rightIntercept_split : rightIntercept q0 (thetaMin lambda B) = B := by
  have hq := q0_bounds
  have hlam : 7/2 ≤ lambda ∧ lambda ≤ 9/2 := movingSlope_mem ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have h1 := rightIntercept_level (q := q0) (T := thetaMin lambda B) (by linarith [hq.1])
    (by linarith [hq.2]) (by linarith [thetaClass_bounds.2])
    (interceptLevelDen_pos ⟨le_rfl, by linarith [hq.2]⟩).ne'
  have h2 := levelAt_split
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := levelAt_strictMono hlam h
    change levelAt lambda (rightIntercept q0 (thetaMin lambda B)) (thetaMin lambda B) = 0 at h1
    linarith
  · have := levelAt_strictMono hlam h
    change levelAt lambda (rightIntercept q0 (thetaMin lambda B)) (thetaMin lambda B) = 0 at h1
    linarith

/-- The bin top of the ledger's intercept at a bin split is the price end's bin top. -/
theorem binTopAt_price (q : ℝ) (hq : q + weight q ≠ 0) :
    binTopAt q (priceIntercept q) = priceEndBinTop q := by
  have h := price_tight q slotTop hq
  unfold binTopAt priceEndBinTop
  congr 2
  linarith

theorem binTop_curve_eq {q T : ℝ} (h0 : 0 < q) (h1 : q < 3/4) (hG : interceptLevelDen q T ≠ 0) :
    binTopAt q (rightIntercept q T) = binTopCurve q T := by
  have hsl : movingSlope q = slopeNum q/slopeDen q := movingSlope_closed h0 h1
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  rw [binTopAt_affine, rightIntercept_eq, frac_clear _ _ _ _ _ _ hG, growthAt_fall q h5, cellHigh_zero,
    growthAt_zero, hsl]
  rfl

/-- The weight of the amplified slots is positive on the split range. -/
theorem weight_pos {q : ℝ} (hq : 1/2 ≤ q) (hq' : q < 3/4) : 0 < weight q := by
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  have h9 : (9:ℝ) - 12*q ≠ 0 := by linarith
  rw [weight_closed h5 h9]
  apply div_pos
  · nlinarith
  · have : (0:ℝ) < 9 - 12*q := by linarith
    have : (0:ℝ) < 5 - 2*q := by linarith
    positivity

/-- Right of the bin split, up to `7/10`, an intercept at least the level intercept fails the
capped live channel in the top cell. -/
theorem cap_fails {q x : ℝ} (hq : q0 < q) (hq' : q ≤ 7/10) (hxP : x ≤ priceIntercept q)
    (hxl : rightIntercept q (thetaMin lambda B) ≤ x) :
    cellHigh q x slotTop + liveRate q*coreCapAt (binTopAt q x)*frequencyAt q x <
      lowReserveAt q + markedLoss := by
  have hq0 := q0_bounds
  have hT := thetaClass_bounds
  have hqI : q ∈ Set.Icc q0 (7/10) := ⟨hq.le, hq'⟩
  have hq0I : q0 ∈ Set.Icc q0 (7/10) := ⟨le_rfl, by linarith [hq0.2]⟩
  have h0 : 0 < q := by linarith [hq0.1]
  have h1 : q < 3/4 := by linarith
  have h5 : (5:ℝ) - 2*q ≠ 0 := by linarith
  set xl := rightIntercept q (thetaMin lambda B) with hxl_def
  obtain ⟨hgP, hfP⟩ := price_growth_frequency_pos hqI
  have hG1 : 0 < growthAt q 0 - growthAt q 1 := by
    rw [growthAt_fall q h5]; unfold growthSlope amplifierRatio
    have : 0 < 2*q/(9 - 12*q) := div_pos (by linarith) (by linarith)
    positivity
  have hF1 : 0 < liveRate q*(6*amplifierRatio q) := by
    unfold liveRate liveRatio chosenPerUnit plainCapacityCost halfGain amplifierRatio
    have : 0 < 2*q/(9 - 12*q) := div_pos (by linarith) (by linarith)
    have : 0 < q*(5 - 6*q)/(5 - 2*q) := div_pos (by nlinarith) (by linarith)
    positivity
  have hxlP : xl ≤ priceIntercept q := hxl.trans hxP
  have hgx : 0 < growthAt q 0 - (growthAt q 0 - growthAt q 1)*x := by
    nlinarith [mul_nonneg hG1.le (sub_nonneg.mpr hxP)]
  have hgl : 0 < growthAt q 0 - (growthAt q 0 - growthAt q 1)*xl := by
    nlinarith [mul_nonneg hG1.le (sub_nonneg.mpr hxlP)]
  have hfx : 0 < liveRate q*frequencyAt q 0 - liveRate q*(6*amplifierRatio q)*x := by
    nlinarith [mul_nonneg hF1.le (sub_nonneg.mpr hxP)]
  have hfl : 0 < liveRate q*frequencyAt q 0 - liveRate q*(6*amplifierRatio q)*xl := by
    nlinarith [mul_nonneg hF1.le (sub_nonneg.mpr hxlP)]
  have hW : q + weight q ≠ 0 := (add_pos h0 (weight_pos (by linarith [hq0.1]) h1)).ne'
  -- The bin top rises with the intercept and, along the level intercept, with the bin split.
  have hbt1 : binTopAt q xl ≤ binTopAt q x := by
    rw [binTopAt_affine, binTopAt_affine]
    linarith [frac_mono (binTop_coef_pos hqI) hxl hgl hgx]
  have hbt2 : markedBinTop < binTopAt q xl := by
    have hm := binTopCurve_mono.1 hq0I hqI hq
    simp only at hm
    rw [← binTop_curve_eq h0 h1 (interceptLevelDen_pos hqI).ne',
      ← binTop_curve_eq (by linarith [hq0.1]) (by linarith [hq0.2]) (interceptLevelDen_pos hq0I).ne',
      rightIntercept_split] at hm
    have hp := binTopAt_price q0
      (add_pos (by linarith [hq0.1]) (weight_pos (by linarith [hq0.1]) (by linarith [hq0.2]))).ne'
    have hB : binTopAt q0 B = markedBinTop := hp
    rw [hB] at hm
    exact hm
  have hbt3 : binTopAt q x ≤ priceEndBinTop q := by
    rw [← binTopAt_price q hW, binTopAt_affine, binTopAt_affine]
    linarith [frac_mono (binTop_coef_pos hqI) hxP hgx hgP]
  -- The bin tops lie in the range where the core cap falls.
  have hmono := priceEndBinTop_mono.1
  have hq0R : q0 ∈ Set.Icc (1/2:ℝ) (37/50) := ⟨by linarith [hq0.1], by linarith [hq0.2]⟩
  have hqR : q ∈ Set.Icc (1/2:ℝ) (37/50) := ⟨by linarith [hq0.1], by linarith⟩
  have hlow : priceEndBinTop (1/2) ≤ markedBinTop :=
    hmono.monotoneOn ⟨le_rfl, by norm_num⟩ hq0R hq0R.1
  have hhigh : priceEndBinTop q ≤ priceEndBinTop (37/50) :=
    hmono.monotoneOn hqR ⟨by norm_num, le_rfl⟩ hqR.2
  have hmark : markedBinTop ∈ binTopRange :=
    ⟨hlow, hmono.monotoneOn hq0R ⟨by norm_num, le_rfl⟩ hq0R.2⟩
  have hrange : binTopAt q x ∈ binTopRange := ⟨by linarith, by linarith⟩
  have hcore : coreCapAt (binTopAt q x) < coreCapAt markedBinTop :=
    coreCapAt_anti.1 hmark hrange (by linarith)
  -- The balancing core cap rises with the intercept and along the level intercept.
  have hbal1 : balancedAt q xl ≤ balancedAt q x := by
    rw [balancedAt_affine, balancedAt_affine]
    exact frac_mono (balanced_coef_pos hqI) hxl hfl hfx
  have hbal2 : balancedCoreCap q0 < balancedAt q xl := by
    have hm := balancedCurve_mono.1 hq0I hqI hq
    simp only at hm
    rw [← balanced_curve_eq h0 h1 (interceptLevelDen_pos hqI).ne',
      ← balanced_curve_eq (by linarith [hq0.1]) (by linarith [hq0.2]) (interceptLevelDen_pos hq0I).ne',
      rightIntercept_split] at hm
    exact hm
  have hbal0 : balancedCoreCap q0 = coreCapAt markedBinTop := by
    have h := capResidual_markedSplit
    unfold capResidual at h
    change balancedCoreCap q0 - coreCapAt markedBinTop = 0 at h
    linarith
  have hlt : coreCapAt (binTopAt q x) < balancedAt q x := by linarith
  have hpos : 0 < liveRate q*frequencyAt q x := by
    rw [frequencyAt_affine]; nlinarith
  unfold balancedAt at hlt
  rw [lt_div_iff₀ hpos] at hlt
  nlinarith

/-! ### The bin split is optimal -/

/-- The bin split `q0` with its price intercept gives the smallest class bound of the marked ledger:
at every bin split of the split range and every positive intercept that the ledger admits there, the
class bound of the top-row certificate is at least the one at `q0`. -/
theorem markedSplit_optimal {q x : ℝ} (hq : q ∈ splitRange) (hx : 0 < x) (hadm : Admissible q x) :
    thetaMin lambda B ≤ thetaMin (movingSlope q) x := by
  obtain ⟨hxP, hcap⟩ := hadm
  have hq0 := q0_bounds
  have hlam := movingSlope_mem hq
  rcases lt_trichotomy q q0 with hlt | heq | hgt
  · -- Left of the bin split the price intercept is below the level intercept.
    apply le_of_lt
    apply lt_thetaMin_of_level hlam hx
    exact lt_of_le_of_lt (levelAt_mono hlam hxP) (price_level_neg hq.1 hlt)
  · subst heq
    rcases lt_or_eq_of_le hxP with hlt' | heq'
    · apply le_of_lt
      apply lt_thetaMin_of_level hlam hx
      have h := levelAt_strictMono hlam hlt'
      have h0 := levelAt_split
      change levelAt (movingSlope q0) (priceIntercept q0) (thetaMin lambda B) = 0 at h0
      linarith
    · rw [heq']; exact le_rfl
  · rcases le_or_gt q (7/10) with hnear | hfar
    · -- Near right of the bin split the capped live channel keeps the intercept below the level
      -- intercept.
      have hbelow : x < rightIntercept q (thetaMin lambda B) := by
        by_contra hc
        push Not at hc
        have := cap_fails hgt hnear hxP hc
        linarith
      apply le_of_lt
      apply lt_thetaMin_of_level hlam hx
      have hqI : q ∈ Set.Icc q0 (7/10) := ⟨hgt.le, hnear⟩
      have h := levelAt_strictMono hlam hbelow
      rw [rightIntercept_level (by linarith [hq0.1]) (by linarith)
        (by linarith [thetaClass_bounds.2]) (interceptLevelDen_pos hqI).ne'] at h
      exact h
    · apply le_of_lt
      apply lt_thetaMin_of_level hlam hx
      exact lt_of_le_of_lt (levelAt_mono hlam hxP) (far_level_neg hfar.le hq.2)

/-- The bin split is admissible with its price intercept: both channels are tight in the top cell. -/
theorem markedSplit_admissible : Admissible q0 B := by
  have hq0 := q0_bounds
  refine ⟨le_rfl, ?_⟩
  have h : cellHigh q0 B slotTop + liveRate q0*liveCap - markedLoss - lowReserveAt q0 = 0 := cap_tight
  have hbt : binTopAt q0 B = markedBinTop :=
    binTopAt_price q0
      (add_pos (by linarith [hq0.1]) (weight_pos (by linarith [hq0.1]) (by linarith [hq0.2]))).ne'
  have hc : coreCapAt markedBinTop = inverseWidthCap*coreFactor := rfl
  have hf : frequencyAt q0 B = frequencyFactor := rfl
  have hlive : liveRate q0*coreCapAt markedBinTop*frequencyAt q0 B = liveRate q0*liveCap := by
    rw [hc, hf]
    unfold liveCap liveFrequency
    ring
  rw [hbt, hlive]
  linarith

end

end Cycle63.Optimization
