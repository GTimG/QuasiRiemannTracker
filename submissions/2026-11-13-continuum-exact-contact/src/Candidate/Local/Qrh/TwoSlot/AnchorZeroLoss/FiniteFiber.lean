/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The stronger finite source in the literal detector-fiber contract. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.FiniteSource
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineBridge
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineCountFiber

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss
open OAI.SevenEighths

def finiteLine : Affine.Line where
  g0 := Certificate.targetG0
  g1 := Certificate.targetG1
  slope_nonneg := by norm_num [Certificate.targetG1]
  slope_le := by norm_num [Certificate.targetG1]

instance finite_capacity : Affine.Return.CapacityBounds finiteLine where
  bounds := by
    intro w h1 h2
    unfold Affine.markCap finiteLine Qrh.MarkedAnchor.Interface.anchorLeft
      Qrh.MarkedAnchor.Interface.anchorTop at *
    norm_num [Certificate.targetG0,Certificate.targetG1] at *
    constructor <;> linarith

/-- The finite chain supplies the actual detector fiber moments, including
log derivatives, common height, both orientations, physical slot masks and the
common mesh chosen before arithmetic data. -/
theorem finite_fiber_moments (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    Affine.ImprovedFiberMoments finiteLine := by
  apply Affine.fiber_of_improved_split finiteLine
    (hi := 311/400+1/1000)
    (by norm_num [Qrh.MarkedAnchor.Interface.anchorTop])
  · exact finite_source hβ
  · exact finite_source_top hβ

/-- The geometric slot capacity is positive and within the physical supply on
its whole requested interval, with the inherited positive slot slack. -/
theorem finite_markCap_bounds {w ν : ℝ}
    (h1 : Qrh.MarkedAnchor.Interface.anchorLeft ≤ w)
    (h2 : w ≤ Qrh.MarkedAnchor.Interface.anchorTop)
    (hν : 0 < ν) (hν1 : ν ≤ 1/10000000) :
    0 < Affine.markCap finiteLine w-ν ∧
      Affine.markCap finiteLine w-ν ≤ 7/37 := by
  unfold Affine.markCap finiteLine Qrh.MarkedAnchor.Interface.anchorLeft
    Qrh.MarkedAnchor.Interface.anchorTop at *
  norm_num [Certificate.targetG0,Certificate.targetG1] at *
  constructor <;> linarith

end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.finite_fiber_moments
