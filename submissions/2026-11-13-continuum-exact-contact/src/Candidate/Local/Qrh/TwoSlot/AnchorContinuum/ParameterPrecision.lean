/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Exact interval propagation to the stationary cutoff. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CutoffBounds
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.RationalInterval

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.Precision
noncomputable section
open RationalInterval Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

theorem coefficients :
    (58059119/1000000000:ℝ) ≤ tangentIntercept ∧ tangentIntercept ≤ 1451478/25000000 ∧
    (9499523/125000000:ℝ) ≤ -tangentSlope ∧ -tangentSlope ≤ 37998093/500000000 := by
  have hw := width_tight
  have hpos : (0:ℝ) ≤ 37616102690677/50000000000000 := by norm_num
  have h2lo := pow_le_pow_left₀ hpos hw.1.le 2
  have h2hi := pow_le_pow_left₀ (hpos.trans hw.1.le) hw.2.le 2
  have h3lo := pow_le_pow_left₀ hpos hw.1.le 3
  have h3hi := pow_le_pow_left₀ (hpos.trans hw.1.le) hw.2.le 3
  have hd : 0 < (45*width-14)*(15*width-10) :=
    mul_pos (by linarith [hw.1]) (by linarith [hw.1])
  have hs : 0 < width*(45*width-14)*(15*width-10) :=
    mul_pos (mul_pos (by linarith [hw.1]) (by linarith [hw.1])) (by linarith [hw.1])
  rw [tangentIntercept_formula,negative_slope_formula]
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,
    (le_div_iff₀ hs).mpr ?_,(div_le_iff₀ hs).mpr ?_⟩ <;>
    nlinarith [hw.1,hw.2,h2lo,h2hi,h3lo,h3hi]

def wBox : Box := ⟨37616102690677/50000000000000,15046441076271/20000000000000⟩
def thetaBox : Box := ⟨109168232013339822100148/125000000000000000000000,
  174669171221343715360237/200000000000000000000000⟩
def g0Box : Box := ⟨58059119/1000000000,1451478/25000000⟩
def g1Box : Box := ⟨9499523/125000000,37998093/500000000⟩
def dDen : Box := add (mul (point 54) wBox) (point 6)
def dBox : Box := div (sub (mul (point 45) wBox) (point 14)) dDen
def ellBox : Box := sub (point (11/3)) (mul (point 4) thetaBox)
def jBox : Box := sub (point (5/2)) (mul dBox (add (point 2) (mul (point 2) g1Box)))
def uBox : Box := add (sub (point (1/2)) (mul (point 3) g0Box)) (mul (point 2) g1Box)
def slopeBox : Box := neg (add (point 2) (mul (point 2) g1Box))
def numeratorBox : Box := sub
  (mul (sub (point (5/6)) (mul (point 2) dBox)) jBox)
  (mul (mul (sub (point (5/6)) dBox) dBox) slopeBox)
def squareBox : Box := mul jBox jBox
def rateBox : Box := add (point (-1)) (div (mul uBox numeratorBox) squareBox)
def hDen : Box := sub (point (1/8)) (mul (point (3/4)) rateBox)
def hBox : Box := div (add (point (1/2)) ellBox) hDen

theorem width_sound : wBox.Contains width := by
  simpa [Box.Contains,wBox] using And.intro width_tight.1.le width_tight.2.le
theorem theta_sound : thetaBox.Contains theta := by
  simpa [Box.Contains,thetaBox,lower,upper] using And.intro theta_isolated.1.le theta_isolated.2.le
theorem g0_sound : g0Box.Contains tangentIntercept := by
  simpa [Box.Contains,g0Box] using And.intro coefficients.1 coefficients.2.1
theorem g1_sound : g1Box.Contains (-tangentSlope) := by
  simpa [Box.Contains,g1Box] using And.intro coefficients.2.2.1 coefficients.2.2.2

theorem density_sound : dBox.Contains density := by
  have hn := sub_sound (mul_sound (point_sound 45) width_sound) (point_sound 14)
  have hd := add_sound (mul_sound (point_sound 54) width_sound) (point_sound 6)
  exact Box.transport (div_sound hn hd (by norm_num [dDen,add,mul,point,wBox])) (by norm_num [density])

theorem ell_sound : ellBox.Contains ell :=
  Box.transport (sub_sound (point_sound (11/3)) (mul_sound (point_sound 4) theta_sound)) (by norm_num [ell])

theorem J_sound : jBox.Contains (ExactWindow.JI density (1/2)) := by
  have hh := sub_sound (point_sound (5/2))
    (mul_sound density_sound (add_sound (point_sound 2) (mul_sound (point_sound 2) g1_sound)))
  apply Box.transport hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  dsimp [ExactWindow.JI,ExactWindow.kI,exactLine]
  ring

theorem U_sound : uBox.Contains criticalU := by
  have hh := add_sound (sub_sound (point_sound (1/2)) (mul_sound (point_sound 3) g0_sound))
    (mul_sound (point_sound 2) g1_sound)
  apply Box.transport hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  dsimp [criticalU,ExactWindow.UI,exactLine]
  ring

theorem slope_sound : slopeBox.Contains jSlope := by
  have hh := neg_sound (add_sound (point_sound 2) (mul_sound (point_sound 2) g1_sound))
  apply Box.transport hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  dsimp [jSlope,exactLine]
  ring

theorem numerator_sound : numeratorBox.Contains rateNumerator := by
  exact Box.transport (sub_sound
    (mul_sound (sub_sound (point_sound (5/6)) (mul_sound (point_sound 2) density_sound)) J_sound)
    (mul_sound (mul_sound (sub_sound (point_sound (5/6)) density_sound) density_sound) slope_sound))
      (by norm_num [rateNumerator])

theorem square_positive : 0 < squareBox.lo := by
  norm_num [squareBox,jBox,dBox,dDen,g1Box,add,sub,neg,mul,div,inv,point,wBox]

theorem rate_sound : rateBox.Contains (densityRate density) := by
  have hh := add_sound (point_sound (-1))
    (div_sound (mul_sound U_sound numerator_sound) (mul_sound J_sound J_sound) square_positive)
  apply Box.transport hh
  norm_num only [Rat.cast_neg,Rat.cast_ofNat]
  unfold densityRate rateNumerator
  ring

theorem hDen_positive : 0 < hDen.lo := by
  norm_num [hDen,rateBox,squareBox,numeratorBox,slopeBox,uBox,jBox,dBox,dDen,g0Box,g1Box,
    add,sub,neg,mul,div,inv,point,wBox]

theorem cutoff_sound : hBox.Contains stationaryCutoff := by
  exact Box.transport (div_sound (add_sound (point_sound (1/2)) ell_sound)
    (sub_sound (point_sound (1/8)) (mul_sound (point_sound (3/4)) rate_sound))
    hDen_positive) (by norm_num [stationaryCutoff])

theorem cutoff_bounds : (815324503/1000000000:ℝ) < stationaryCutoff ∧
    stationaryCutoff < 163064901/200000000 := by
  have hh := cutoff_sound
  have hlo : (815324503/1000000000:ℚ) < hBox.lo := by
    norm_num [hBox,hDen,rateBox,squareBox,numeratorBox,slopeBox,uBox,jBox,dBox,dDen,ellBox,
      thetaBox,g0Box,g1Box,add,sub,neg,mul,div,inv,point,wBox]
  have hhi : hBox.hi < (163064901/200000000:ℚ) := by
    norm_num [hBox,hDen,rateBox,squareBox,numeratorBox,slopeBox,uBox,jBox,dBox,dDen,ellBox,
      thetaBox,g0Box,g1Box,add,sub,neg,mul,div,inv,point,wBox]
  have hrl : (815324503/1000000000:ℝ) < (hBox.lo:ℝ) := by
    have h : ((815324503/1000000000:ℚ):ℝ) < (hBox.lo:ℝ) := Rat.cast_lt.mpr hlo
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  have hru : (hBox.hi:ℝ) < (163064901/200000000:ℝ) := by
    have h : (hBox.hi:ℝ) < ((163064901/200000000:ℚ):ℝ) := Rat.cast_lt.mpr hhi
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  exact ⟨hrl.trans_le hh.1,hh.2.trans_lt hru⟩

end
end Qrh.TwoSlot.AnchorContinuum.Contact.Precision
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.Precision.cutoff_bounds
