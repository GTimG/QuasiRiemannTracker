import Candidate.Cycle63.Physical.InitialMass.MarkedParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped ContDiff
open Cycle63Moment

/-- The marked analytic parameters that must hold after the shared density
degree is selected. Slot profiles and the containing real interval are
fixed outside the degree quantifier. Physical capacity and height-payment
inequalities are supplied separately by the original source schedule. -/
structure MarkedSchedule (P : HighSourceParameters) (N : ℕ)
    (W : ℝ→ℂ) (lo hi : ℝ) : Prop where
  slot : P.Wslot=W
  slotCap : P.B₀=2
  sigmaLo : lo≤P.σmin
  sigmaHi : P.σmax≤hi
  degree : P.d=31
  mask : 0≤P.Bmask
  heightZero : P.τ< markedCoreMin/2
  heightWitness : 4*P.τ< markedCoreMin*markedWitnessRate
  buffer : 12*P.e*((22:ℝ)+2)+8*markedWitnessRate+2*markedWitnessRate≤ markedRate/2
  slotLoss : 2*P.εslot*P.d≤ markedBinWidth*markedTinyWidth N

theorem marked_tiny_width_antitone {N Nbudget : ℕ} (hN : N≤Nbudget) :
    markedTinyWidth Nbudget≤ markedTinyWidth N := by
  unfold markedTinyWidth
  apply one_div_le_one_div_of_le (by positivity)
  have hn : (N:ℝ)≤Nbudget := by exact_mod_cast hN
  nlinarith

theorem MarkedSchedule.of_card_le {P : HighSourceParameters} {N Nbudget : ℕ}
    {W : ℝ→ℂ} {lo hi : ℝ} (h : MarkedSchedule P Nbudget W lo hi) (hN : N≤Nbudget) :
    MarkedSchedule P N W lo hi := by
  refine {h with slotLoss := h.slotLoss.trans ?_}
  exact mul_le_mul_of_nonneg_left (marked_tiny_width_antitone hN)
    (by norm_num [markedBinWidth])


theorem MarkedSchedule.width_cap {P : HighSourceParameters} {N : ℕ}
    {W : ℝ→ℂ} {lo hi mesh oldMesh w : ℝ}
    (h : MarkedSchedule P N W lo hi) (hm : mesh≤ markedGeometryMesh oldMesh)
    (hw : w≤P.d*mesh) : w≤ markedRawMesh*markedCoreMin := by
  rw [h.degree] at hw
  exact marked_mesh_transfer oldMesh mesh hm hw

end
end OAI.SevenEighths.Cycle63MarkedPlain
