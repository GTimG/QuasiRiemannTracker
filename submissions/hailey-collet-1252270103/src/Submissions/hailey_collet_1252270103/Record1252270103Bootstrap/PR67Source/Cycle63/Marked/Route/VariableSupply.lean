import Mathlib.Tactic
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-! Variable-width marked detector count.  The analytic moment bounds
remain explicit hypotheses.  The resulting saving pays surviving physical
slot width at the same rate as the allocation ledger pays removed width. -/

namespace VariableSupply
noncomputable section

def cutoff (d p s : ℝ) : ℝ := (5-12*d*p*s)/(5-2*d)
def count (d p s : ℝ) : ℝ := 1/6+(5/6-d)*cutoff d p s
def density (d : ℝ) : ℝ := 1-10*d/(3*(5-2*d))
def gain (d p s : ℝ) : ℝ := d*p*s*(10-12*d)/(5-2*d)
/-- The inverse width of the supplied width `S` in the bin `d`: `S` up to the inverse cap of the
bin. -/
def inverseWidth (d S : ℝ) : ℝ := min S (Cycle63.Optimization.inverseCapAt d)
/-- The plain width of the supplied width `S` in the bin `d`: `S` up to the plain cap of the bin. -/
def plainWidth (d S : ℝ) : ℝ := min S (Cycle63.Optimization.plainCapAt d)
/-- The chosen width `(2 w_I + w_P)/3` of the supplied width `S` in the bin `d`. -/
def chosenWidth (d S : ℝ) : ℝ := (2*inverseWidth d S+plainWidth d S)/3
/-- The chosen width at the caps of the bin `d`. -/
def chosenCap (d : ℝ) : ℝ := (2*Cycle63.Optimization.inverseCapAt d+Cycle63.Optimization.plainCapAt d)/3
/-- The inverse length cap `c_L = 1 - u` of the bin `d`: the count slope of the bin. -/
def lengthCap (d : ℝ) : ℝ := 1-Cycle63.Optimization.capUnitAt d

theorem count_identity {d p s : ℝ} (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    count d p s = 1-2*d/3*cutoff d p s-2*d*p*s := by
  have hn : 5-2*d ≠ 0 := by linarith [Cycle63.Optimization.markedBinTop_bounds.2]
  apply mul_left_cancel₀ hn
  unfold count cutoff
  field_simp [hn]
; ring

theorem gain_identity {d p s : ℝ} (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    density d-count d p s = gain d p s := by
  have hn : 5-2*d ≠ 0 := by linarith [Cycle63.Optimization.markedBinTop_bounds.2]
  apply mul_left_cancel₀ hn
  unfold density count cutoff gain
  field_simp [hn]
; ring

/-- In the bins of the marked range the cap unit lies in `(0, 1/5)`. -/
theorem capUnitAt_bounds {d : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    0 < Cycle63.Optimization.capUnitAt d ∧ Cycle63.Optimization.capUnitAt d < 1/5 := by
  have hq := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hd' : Cycle63.Arithmetic.q0 ≤ d ∧ d ≤ Cycle63.Optimization.markedBinTop := ⟨hd0, hd⟩
  unfold Cycle63.Optimization.capUnitAt Cycle63.Optimization.chosenPerUnit
    Cycle63.Optimization.plainCapacityCost
  constructor <;> rat_pos [hq, hd', htop]

theorem inverseWidth_bounds {d S : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d)
    (hd : d ≤ Cycle63.Optimization.markedBinTop) (hS : 0 ≤ S) :
    0 ≤ inverseWidth d S ∧ inverseWidth d S ≤ S ∧ inverseWidth d S ≤ Cycle63.Optimization.inverseCapAt d := by
  have hu := (capUnitAt_bounds hd0 hd).1
  exact ⟨le_min hS (by unfold Cycle63.Optimization.inverseCapAt; positivity), min_le_left _ _,
    min_le_right _ _⟩

theorem plainWidth_bounds {d S : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d)
    (hd : d ≤ Cycle63.Optimization.markedBinTop) (hS : 0 ≤ S) :
    0 ≤ plainWidth d S ∧ plainWidth d S ≤ S ∧ plainWidth d S ≤ Cycle63.Optimization.plainCapAt d := by
  have hu := (capUnitAt_bounds hd0 hd).1
  have hv : 0 ≤ Cycle63.Optimization.plainCapAt d := by
    unfold Cycle63.Optimization.plainCapAt Cycle63.Optimization.plainCapacityCost
    positivity
  exact ⟨le_min hS hv, min_le_left _ _, min_le_right _ _⟩

theorem chosenWidth_bounds {d S : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d)
    (hd : d ≤ Cycle63.Optimization.markedBinTop) (hS : 0 ≤ S) :
    0 ≤ chosenWidth d S ∧ chosenWidth d S ≤ S ∧ chosenWidth d S ≤ chosenCap d := by
  have hi := inverseWidth_bounds hd0 hd hS
  have hp := plainWidth_bounds hd0 hd hS
  unfold chosenWidth chosenCap
  refine ⟨by linarith [hi.1, hp.1], by linarith, by linarith⟩

/-- In the bins of the marked range the chosen cap is at most `1/12`. -/
theorem chosenCap_le {d : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    chosenCap d ≤ 1/12 := by
  have hu := capUnitAt_bounds hd0 hd
  unfold chosenCap Cycle63.Optimization.inverseCapAt Cycle63.Optimization.plainCapAt
    Cycle63.Optimization.plainCapacityCost
  norm_num
  linarith [hu.2]

/-- Below the inverse length cap of the bin the inverse moment has room for the inverse cap. -/
theorem inverse_capacities {d r s : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d)
    (hd : d ≤ Cycle63.Optimization.markedBinTop) (hr : r < lengthCap d)
    (hs : s ≤ Cycle63.Optimization.inverseCapAt d) :
    r+2*s < 1 ∧ 2*r+8*s < 3 := by
  have hu := capUnitAt_bounds hd0 hd
  unfold lengthCap at hr
  unfold Cycle63.Optimization.inverseCapAt at hs
  constructor <;> linarith

/-- Up to the plain length cap of the bin the plain moment has room for the plain cap. -/
theorem plain_capacity {d m s : ℝ} (hm : m ≤ lengthCap d/2) (hs : s ≤ Cycle63.Optimization.plainCapAt d) :
    2*m+6*Cycle63.Optimization.plainCapacityCost*s ≤ 1 := by
  have hk : (0:ℝ) < 6*Cycle63.Optimization.plainCapacityCost := by
    unfold Cycle63.Optimization.plainCapacityCost; norm_num
  have hh := mul_le_mul_of_nonneg_left hs hk.le
  have hid : 6*Cycle63.Optimization.plainCapacityCost*Cycle63.Optimization.plainCapAt d =
      Cycle63.Optimization.capUnitAt d := by
    unfold Cycle63.Optimization.plainCapAt
    rw [mul_comm]
    exact div_mul_cancel₀ _ hk.ne'
  unfold lengthCap at hm
  nlinarith

/-- The marked count in the bin `d` is at least `1 - c_L d` for every width up to the chosen cap and
slot amplitude up to `1/2`, with equality at the chosen cap and amplitude `1/2`: the cap unit of the
bin is the largest for which this holds. -/
theorem count_lower {d p s : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ chosenCap d) :
    1-lengthCap d*d ≤ count d p s := by
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hden : 0 < 5-2*d := by linarith
  have hk : 0 < 5-2*d+Cycle63.Optimization.chosenPerUnit*(5-6*d) := by
    unfold Cycle63.Optimization.chosenPerUnit Cycle63.Optimization.plainCapacityCost; nlinarith
  have hu : Cycle63.Optimization.capUnitAt d*(5-2*d+Cycle63.Optimization.chosenPerUnit*(5-6*d)) =
      5/3-2*d := div_mul_cancel₀ _ hk.ne'
  have hcap : chosenCap d = Cycle63.Optimization.chosenPerUnit*Cycle63.Optimization.capUnitAt d := by
    unfold chosenCap Cycle63.Optimization.inverseCapAt Cycle63.Optimization.plainCapAt
      Cycle63.Optimization.chosenPerUnit
    ring
  have hid : (5-2*d)*(count d p s-(1-lengthCap d*d)) = d*(5-6*d)*(chosenCap d-2*p*s) := by
    have hc : (5-2*d)*count d p s = (5-2*d)/6+(5/6-d)*(5-12*d*p*s) := by
      unfold count cutoff
      field_simp
    rw [hcap]
    unfold lengthCap
    linear_combination hc - d*hu
  have hn : 0 ≤ d*(5-6*d)*(chosenCap d-2*p*s) := by
    have h3 : 0 ≤ 5-6*d := by linarith
    have h4 : 0 ≤ chosenCap d-2*p*s := by nlinarith
    positivity
  have hh : 0 ≤ count d p s-(1-lengthCap d*d) :=
    (mul_nonneg_iff_of_pos_left hden).mp (hid.symm ▸ hn)
  linarith

/-- The inverse and plain estimates select independent subproducts. The
weighted effective width reflects their different coefficients in the length
balance, and each selected subproduct obeys its own moment capacity. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (_hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (heps : 0 ≤ eps)
    (hlength : cutoff d p (chosenWidth d S)-eps ≤ r+m)
    (hrcap : r ≤ cutoff d p (chosenWidth d S)+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r < lengthCap d → E ≤ 1-d*r-2*d*p*inverseWidth d S+loss)
    (hPM : m ≤ lengthCap d/2 → E ≤ 1-2*d*m-2*d*p*plainWidth d S+loss) :
    E ≤ count d p (chosenWidth d S)+loss+eps := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hc := capUnitAt_bounds hd0 hd
  have hdpos : 0 ≤ d := by linarith
  obtain ⟨hs0,hsS,hs⟩ := chosenWidth_bounds hd0 hd hS
  have hlow := count_lower hdpos hd hp hs0 hs
  have hid := count_identity (p:=p) (s:=chosenWidth d S) hd
  have hmix : 3*chosenWidth d S=2*inverseWidth d S+plainWidth d S := by
    unfold chosenWidth
    ring
  by_cases hr : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hir : r < lengthCap d
    · by_cases hpm : m ≤ lengthCap d/2
      · have hi := hIM hir
        have hp' := hPM hpm
        have hlen := mul_le_mul_of_nonneg_left hlength hdpos
        have he := mul_nonneg hdpos heps
        have he' := mul_le_mul_of_nonneg_right hd heps
        have hmix' := congrArg (fun x : ℝ => d*p*x) hmix
        nlinarith
      · have hm : lengthCap d/2 ≤ m := le_of_lt (lt_of_not_ge hpm)
        have hmul := mul_le_mul_of_nonneg_left hm hdpos
        linarith
    · have hr' : lengthCap d ≤ r := le_of_not_gt hir
      have hmul := mul_le_mul_of_nonneg_left hr' hdpos
      nlinarith
  · have hr' : 1 ≤ r := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have hV : 0 ≤ 5/6-d := by linarith
    have hh := mul_le_mul_of_nonneg_left hrcap hV
    have he := mul_le_mul_of_nonneg_right hd0 heps
    unfold count
    nlinarith

/-- At slot amplitude `1/2` the gain per unit of effective width is the half-amplitude gain of
the bin. -/
theorem gain_half_eq (d s : ℝ) : gain d (1/2) s = Cycle63.Optimization.halfGain d*s := by
  unfold gain Cycle63.Optimization.halfGain
  ring

theorem gain_one_upper {d s S : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (hs0 : 0 ≤ s) (hsS : s ≤ S) : gain d 1 s ≤ 2*d*S := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hdpos : 0 ≤ d := by linarith
  have hden : 0 < 5-2*d := by linarith
  have hratio : (10-12*d)/(5-2*d) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg hdpos hs0)
  have hh' := mul_le_mul_of_nonneg_left hsS hdpos
  calc
    gain d 1 s = d*s*((10-12*d)/(5-2*d)) := by unfold gain; ring
    _ ≤ d*s*2 := hh
    _ ≤ 2*d*S := by linarith

/-- At unit frequency the exact marked gain is the half gain times the chosen width. -/
theorem markedGain_one (d S : ℝ) :
    Cycle63.Optimization.markedGain d S 1 = Cycle63.Optimization.halfGain d*chosenWidth d S := by
  simp only [Cycle63.Optimization.markedGain, Cycle63.Optimization.ExactGain.scaledGain,
    Cycle63.Optimization.ExactGain.gain, mul_one, chosenWidth, inverseWidth, plainWidth]
  ring

theorem joint_width_gap {d p s S : ℝ}
    (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop) (hp : p ≤ 1/2)
    (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    count d p s+2*d*p*S ≤ density d+d*S-Cycle63.Optimization.halfGain d*s := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hgain := gain_half_eq d s
  have hupper := gain_one_upper hd0 hd hs0 hsS
  have hlinear : gain d p s = p*gain d 1 s := by unfold gain; ring
  have hhalf : gain d (1/2) s = gain d 1 s/2 := by unfold gain; ring
  have hid := gain_identity (p:=p) (s:=s) hd
  have hcoeff : 0 ≤ 2*d*S-gain d 1 s := by linarith
  have hh := mul_le_mul_of_nonneg_right hp hcoeff
  nlinarith

theorem joint_chosen_gap {d p S : ℝ}
    (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop) (hp : p ≤ 1/2) (hS0 : 0 ≤ S) :
    count d p (chosenWidth d S)+2*d*p*S ≤
      density d+d*S-Cycle63.Optimization.halfGain d*chosenWidth d S := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hb := chosenWidth_bounds hd0 hd hS0
  exact joint_width_gap hd0 hd hp hb.1 hb.2.1

end
end VariableSupply

end Record1252270103Bootstrap.PR67
