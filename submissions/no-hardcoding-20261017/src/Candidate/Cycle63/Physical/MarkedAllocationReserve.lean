import Candidate.Cycle63.Physical.CoupledRadicalSaving
import Candidate.Cycle63.Optimization.Ledger

namespace MarkedAllocationReserve
noncomputable section

theorem second_common_saving (δ b g t : ℝ) (hg : g ≤ b) :
    g-t-(1+δ)*b ≤ -δ*b-t := by nlinarith

theorem raw_frequency_lower (M c d b a R Lc ω err q : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ M*Cycle63.Optimization.amplifierCap) (hω : ω ≤ M*Cycle63.Optimization.frequencyLossCap) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err) :
    Cycle63.Optimization.frequencyFactor*M-2*(c+b) ≤ q := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  unfold Cycle63.Optimization.frequencyFactor
  linarith

/-- Removing a sixth power of norm at most `U^κ`, for the root cutoff `κ`, preserves the frequency
lower bound required by the continuous allocation ledger. -/
theorem small_core_frequency_lower (M removed q qcore : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed)
    (hq : Cycle63.Optimization.frequencyFactor*M-2*removed ≤ q)
    (hcore : Cycle63.Optimization.coreFactor*q ≤ qcore) :
    Cycle63.Optimization.liveFrequency*M-2*removed ≤ qcore := by
  have hk := Cycle63.Optimization.coreFactor_bounds
  have hq' := mul_le_mul_of_nonneg_left hq (by linarith [hk.1] : (0:ℝ) ≤ Cycle63.Optimization.coreFactor)
  have hr := mul_le_mul_of_nonneg_right (by linarith [hk.2] : Cycle63.Optimization.coreFactor ≤ 1) hu
  unfold Cycle63.Optimization.liveFrequency
  nlinarith

/-- The ledger minimum of the marked saving in the cell with upper edge `b` for the price `c` per
unit of removed width and the live rate `r`: all supplied width removed, or all live at the live
cap. -/
def ledgerMinimum (b c r : ℝ) : ℝ := min (c*Cycle63.Optimization.suppliedAt b) (r*Cycle63.Optimization.liveCap)

/-- Coupled radical loss and asymmetric marked moments cover every split of the conserved width
between common, frozen, and surviving slots: the saving is at least the ledger minimum whenever the
price `c` is at most the zero parameter and at least twice the capped live rate. A price above the
live rate makes removal the dearer option; the supply exceeds the live cap, so the
minimum is then still attained at an end. -/
theorem continuous_marked_ledger (M removed frozen live q δ c r b : ℝ) (hb : Cycle63.Optimization.firstCellTop ≤ b)
    (hM : 0 ≤ M) (hu : 0 ≤ removed) (hf : 0 ≤ frozen) (hl : 0 ≤ live)
    (hcδ : c ≤ δ) (hr : 0 ≤ r) (hcrate : 2*r*Cycle63.Optimization.inverseWidthCap ≤ c)
    (hsupply : Cycle63.Optimization.suppliedAt b*M ≤ removed+frozen+live)
    (hq : Cycle63.Optimization.liveFrequency*M-2*removed ≤ q) :
    M*ledgerMinimum b c r ≤ c*removed+δ*frozen+r*min live (Cycle63.Optimization.inverseWidthCap*q) := by
  have hw := Cycle63.Optimization.inverseWidthCap_pos
  have hc0 : 0 ≤ c := le_trans (by positivity) hcrate
  have hdf : c*frozen ≤ δ*frozen := mul_le_mul_of_nonneg_right hcδ hf
  have hcap_eq : Cycle63.Optimization.liveCap = Cycle63.Optimization.inverseWidthCap*Cycle63.Optimization.liveFrequency := rfl
  unfold ledgerMinimum
  by_cases hs : live ≤ Cycle63.Optimization.inverseWidthCap*q
  · rw [min_eq_left hs]
    -- The saving is at least `min c r` per unit of supply.
    have h1 := mul_le_mul_of_nonneg_right (min_le_left c r) hu
    have h2 := mul_le_mul_of_nonneg_right (min_le_left c r) hf
    have h3 := mul_le_mul_of_nonneg_right (min_le_right c r) hl
    have hs' := mul_le_mul_of_nonneg_left hsupply (le_min hc0 hr)
    have hS : Cycle63.Optimization.liveCap ≤ Cycle63.Optimization.suppliedAt b := by
      have hc := Cycle63.Optimization.liveCap_bounds
      have hft : (17:ℝ)/500 ≤ b := by
        have hb1 := hb
        unfold Cycle63.Optimization.firstCellTop Cycle63.Optimization.slotFloor
          Cycle63.Optimization.cellMesh Cycle63.Optimization.allowanceUnit at hb1
        linarith
      unfold Cycle63.Optimization.suppliedAt Cycle63.Optimization.cellMesh Cycle63.Optimization.supplyLoss Cycle63.Optimization.commonAllocationLoss
        Cycle63.Optimization.tinySlotLoss Cycle63.Optimization.geometryLossCap Cycle63.Optimization.markedBinWidth
        Cycle63.Optimization.lowReserveWeight Cycle63.Optimization.allowanceUnit
      norm_num
      linarith [hc.2, hft]
    have hcap : min (c*Cycle63.Optimization.suppliedAt b) (r*Cycle63.Optimization.liveCap) ≤ min c r*Cycle63.Optimization.suppliedAt b := by
      rcases le_total c r with h | h
      · rw [min_eq_left h]; exact min_le_left _ _
      · rw [min_eq_right h]; exact (min_le_right _ _).trans (by nlinarith)
    have hcap' := mul_le_mul_of_nonneg_left hcap hM
    nlinarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hs))]
    have hmin := mul_le_mul_of_nonneg_left
      (min_le_right (c*Cycle63.Optimization.suppliedAt b) (r*Cycle63.Optimization.liveCap)) hM
    have hk : M*(r*Cycle63.Optimization.liveCap) = r*Cycle63.Optimization.inverseWidthCap*(Cycle63.Optimization.liveFrequency*M) := by
      rw [hcap_eq]; ring
    have hrem := mul_nonneg (show 0 ≤ c-2*r*Cycle63.Optimization.inverseWidthCap by linarith) hu
    have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ r*Cycle63.Optimization.inverseWidthCap by positivity)
    have hfr := mul_nonneg (le_trans hc0 hcδ) hf
    nlinarith [hmin, hk, hq', hrem, hfr]

end
end MarkedAllocationReserve

#print axioms MarkedAllocationReserve.continuous_marked_ledger
#print axioms MarkedAllocationReserve.raw_frequency_lower
#print axioms MarkedAllocationReserve.small_core_frequency_lower
