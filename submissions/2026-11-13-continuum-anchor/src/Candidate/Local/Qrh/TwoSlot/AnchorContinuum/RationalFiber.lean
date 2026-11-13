/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The continuum rational source in the detector's physical fiber contract. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.AffineSource
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineBridge
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.AffineCountFiber

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss

def rationalLine : Affine.Line where
  g0 := RationalSource.g0
  g1 := RationalSource.g1
  slope_nonneg := by norm_num [RationalSource.g1]
  slope_le := by norm_num [RationalSource.g1]

instance rational_capacity : Affine.Return.CapacityBounds rationalLine where
  bounds := by
    intro w h1 h2
    unfold Affine.markCap rationalLine Qrh.MarkedAnchor.Interface.anchorLeft
      Qrh.MarkedAnchor.Interface.anchorTop at *
    norm_num [RationalSource.g0,RationalSource.g1] at *
    constructor <;> linarith

theorem rational_fiber_moments
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta) :
    Affine.ImprovedFiberMoments rationalLine := by
  apply Affine.fiber_of_improved_split rationalLine
    (hi := 311/400+1/1000)
    (by norm_num [Qrh.MarkedAnchor.Interface.anchorTop])
  · exact RationalSource.full_moments hβ
  · exact RationalSource.top_moments hβ

end
end Qrh.TwoSlot.AnchorContinuum
#print axioms Qrh.TwoSlot.AnchorContinuum.rational_fiber_moments
