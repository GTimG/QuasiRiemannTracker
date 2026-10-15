import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedSameDataCentral

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.PerturbedFloorFrontier

open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.Parameters

/-!
# The perturbed floor rho reserve on the same f630 datum

The old floor endpoint acquires a fixed rho cost.  With
`E = 1/6+rho`, `lx = 17/48-rho/2`, `ly = 23/48-rho/2`,
`H = 13/16+3rho/2`, and comparison against
`b0 = 7/8-rho/4`, the sharp floor endpoint acquires the fixed positive cost
`32*rho/25`.  This file proves that cost exactly and then closes it from the stronger
`new_central_budget` and `high_saving` fields of the very same f630 datum.
The isolated old floor inequality is insufficient, but no scalar floor premise
remains for the actual datum.
-/

/-- Sharp perturbed floor endpoint, before the remaining real losses. -/
theorem floor_source_margin_sharp
    (q beta zeta d : ℝ)
    (hq : q ≤ 1 / 100)
    (hbeta : boundary ≤ beta)
    (hzeta : 0 ≤ zeta)
    (hd : d ≤ physicalHeight + zeta) :
    sourceExponentTau rho0 (51 / 100) d 1 q - (beta - 7 / 8) ≤
      -7 / 1200 + 32 * rho0 / 25 + 67 * zeta / 100 := by
  unfold sourceExponentTau heightTau lyTau ellTau physicalHeight boundary rho0 at *
  norm_num at *
  nlinarith

/-- A looser form aligned with the old scalar allocation `2*zeta`. -/
theorem floor_source_margin_with_two_zeta
    (q beta zeta d : ℝ)
    (hq : q ≤ 1 / 100)
    (hbeta : boundary ≤ beta)
    (hzeta : 0 ≤ zeta)
    (hd : d ≤ physicalHeight + zeta) :
    sourceExponentTau rho0 (51 / 100) d 1 q - (beta - 7 / 8) ≤
      -7 / 1200 + 32 * rho0 / 25 + 2 * zeta := by
  have h := floor_source_margin_sharp q beta zeta d hq hbeta hzeta hd
  nlinarith

/-- The f630 slot-aware floor budget rewritten in the central namespace. -/
lemma same_D_slot_floor_budget
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    2 * D.t + 26 * D.e + (D.N + 8) * D.eps + D.t +
        totalE * D.t + D.t / 8 + D.sigma ≤ 7 / 1200 := by
  simpa only [totalE, rho0, perturbedTotalE, perturbedRho]
    using D.slot_aware_floor_budget

/--
What the current same-D floor budget proves unconditionally: the desired
relative exponent with an unavoidable additive `32*rho0/25`.
-/
theorem same_D_floor_scalar_bound
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (q v d : ℝ) (hq : q ≤ 1 / 100) (hv : v ≤ 1)
    (hd : d ≤ physicalHeight + D.t) :
    3 / 16 + sourceExponentTau rho0 (51 / 100) d 1 q +
        realLossTau rho0 D.N v D.e D.eps D.t D.t + D.t / 8 ≤
      HeckeZeroSupremum.beta - 11 / 16 - D.sigma + 32 * rho0 / 25 := by
  have hfloor := floor_source_margin_with_two_zeta q HeckeZeroSupremum.beta
    D.t d hq hbeta.le D.t_pos.le hd
  have hreal := realLossTau_bound_fixed D.N v D.e D.eps D.t D.t
    hv D.e_pos.le D.eps_pos.le D.t_pos.le
  have hbudget := same_D_slot_floor_budget D
  nlinarith

/-- Exact scalar strengthening that would absorb the new fixed floor cost. -/
def FloorRhoReserve {Delta : ℝ} (D : HighDataPerturbed Delta) : Prop :=
  2 * D.t + 26 * D.e + (D.N + 8) * D.eps + D.t +
      totalE * D.t + D.t / 8 + D.sigma + 32 * rho0 / 25 ≤ 7 / 1200

/--
The same f630 datum already has the required reserve.  The proof must use both
`new_central_budget` and `high_saving`; using only
`slot_aware_floor_budget` would miss the fixed `32*rho0/25` term.
-/
theorem same_D_floor_rho_reserve
    {Delta : ℝ} (D : HighDataPerturbed Delta) : FloorRhoReserve D := by
  have hcount : 0 ≤ 159 * D.ε + D.t + D.t + 7 * D.t := by
    nlinarith [D.epsilon_pos, D.t_pos]
  have hheight : 0 ≤ physicalHeight := height_nonneg
  have hnew :
      physicalHeight * (159 * D.ε + D.t + D.t + 7 * D.t) + 2 * D.t +
        (3 / 2) * (2 * D.t) +
        (26 * D.e + (D.N + 8) * D.eps + D.t + totalE * D.t) +
        (D.t + D.t + D.t) + D.t < perturbedBv6 / 2 := by
    simpa only [physicalHeight, totalE, rho0, perturbedHeight,
      perturbedTotalE, perturbedRho] using D.new_central_budget
  have hfloor_le :
      2 * D.t + 26 * D.e + (D.N + 8) * D.eps + D.t +
          totalE * D.t + D.t / 8 + D.sigma ≤
        physicalHeight * (159 * D.ε + D.t + D.t + 7 * D.t) + 2 * D.t +
          (3 / 2) * (2 * D.t) +
          (26 * D.e + (D.N + 8) * D.eps + D.t + totalE * D.t) +
          (D.t + D.t + D.t) + D.t := by
    have hphys : 0 ≤ physicalHeight *
        (159 * D.ε + D.t + D.t + 7 * D.t) := mul_nonneg hheight hcount
    nlinarith [D.high_saving, D.t_pos]
  have hnumeric :
      perturbedBv6 / 2 + 32 * rho0 / 25 < (7 / 1200 : ℝ) := by
    norm_num [perturbedBv6, rho0]
  unfold FloorRhoReserve
  linarith

/-- With the exact additional reserve, the old target exponent closes. -/
theorem same_D_floor_scalar_bound_of_rho_reserve
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hreserve : FloorRhoReserve D)
    (hbeta : boundary < HeckeZeroSupremum.beta)
    (q v d : ℝ) (hq : q ≤ 1 / 100) (hv : v ≤ 1)
    (hd : d ≤ physicalHeight + D.t) :
    3 / 16 + sourceExponentTau rho0 (51 / 100) d 1 q +
        realLossTau rho0 D.N v D.e D.eps D.t D.t + D.t / 8 ≤
      HeckeZeroSupremum.beta - 11 / 16 - D.sigma := by
  have hfloor := floor_source_margin_with_two_zeta q HeckeZeroSupremum.beta
    D.t d hq hbeta.le D.t_pos.le hd
  have hreal := realLossTau_bound_fixed D.N v D.e D.eps D.t D.t
    hv D.e_pos.le D.eps_pos.le D.t_pos.le
  unfold FloorRhoReserve at hreserve
  nlinarith

/-! ## Concrete counterexample to the missing scalar implication -/

def floorCounterSaving : ℝ := rho0 / 2

def floorCounterOtherLoss : ℝ := 7 / 1200 - floorCounterSaving

/--
The old aggregate budget `otherLoss+saving <= 7/1200` does not imply the
perturbed target after the sharp endpoint contributes `32*rho0/25`.
-/
theorem slot_floor_budget_shape_counterexample :
    0 < floorCounterSaving ∧
      0 ≤ floorCounterOtherLoss ∧
      floorCounterOtherLoss + floorCounterSaving ≤ 7 / 1200 ∧
      ¬ (-7 / 1200 + 32 * rho0 / 25 + floorCounterOtherLoss ≤
          -floorCounterSaving) := by
  norm_num [floorCounterSaving, floorCounterOtherLoss, rho0]

/-- The fixed new cost is genuinely positive. -/
lemma floor_rho_cost_pos : 0 < 32 * rho0 / 25 := by
  norm_num [rho0]

/--
The counterexample concerns the isolated old floor inequality only.  On the
actual same datum the stronger central budget supplies the missing reserve, so
there is no remaining scalar floor premise.
-/
theorem required_floor_repair_is_available
    {Delta : ℝ} (D : HighDataPerturbed Delta) : FloorRhoReserve D :=
  same_D_floor_rho_reserve D

end SevenEighths.PerturbedFloorFrontier

end

end OAI
