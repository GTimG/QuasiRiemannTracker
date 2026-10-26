import Mathlib.Tactic
import Candidate.Cycle63.Arithmetic.Constants

/-! Variable-width marked detector count.  The analytic moment bounds
remain explicit hypotheses.  The resulting saving pays surviving physical
slot width at the same rate as the allocation ledger pays removed width. -/

namespace VariableSupply
noncomputable section

def cutoff (d p s : ℝ) : ℝ := (5-12*d*p*s)/(5-2*d)
def count (d p s : ℝ) : ℝ := 1/6+(5/6-d)*cutoff d p s
def density (d : ℝ) : ℝ := 1-10*d/(3*(5-2*d))
def gain (d p s : ℝ) : ℝ := d*p*s*(10-12*d)/(5-2*d)
def inverseWidth (S : ℝ) : ℝ := min S Cycle63.Optimization.inverseWidthCap
def plainWidth (S : ℝ) : ℝ := min S Cycle63.Optimization.plainWidthCap
def chosenWidth (S : ℝ) : ℝ := (2*inverseWidth S+plainWidth S)/3

theorem count_identity {d p s : ℝ} (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    count d p s = 1-2*d/3*cutoff d p s-2*d*p*s := by
  have hn : 5-2*d ≠ 0 := by linarith [Cycle63.Optimization.markedBinTop_bounds.2]
  apply mul_left_cancel₀ hn
  unfold count cutoff
  field_simp [hn]
  <;> ring

theorem gain_identity {d p s : ℝ} (hd : d ≤ Cycle63.Optimization.markedBinTop) :
    density d-count d p s = gain d p s := by
  have hn : 5-2*d ≠ 0 := by linarith [Cycle63.Optimization.markedBinTop_bounds.2]
  apply mul_left_cancel₀ hn
  unfold density count cutoff gain
  field_simp [hn]
  <;> ring

theorem inverseWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ inverseWidth S ∧ inverseWidth S ≤ S ∧ inverseWidth S ≤ Cycle63.Optimization.inverseWidthCap := by
  exact ⟨le_min hS Cycle63.Optimization.inverseWidthCap_pos.le,min_le_left _ _,min_le_right _ _⟩

theorem plainWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ plainWidth S ∧ plainWidth S ≤ S ∧ plainWidth S ≤ Cycle63.Optimization.plainWidthCap := by
  exact ⟨le_min hS Cycle63.Optimization.plainWidthCap_pos.le,min_le_left _ _,min_le_right _ _⟩

theorem chosenWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ chosenWidth S ∧ chosenWidth S ≤ S ∧ chosenWidth S ≤ Cycle63.Optimization.chosenWidthCap := by
  have hi := inverseWidth_bounds hS
  have hp := plainWidth_bounds hS
  dsimp [chosenWidth]
  unfold Cycle63.Optimization.chosenWidthCap
  constructor
  · linarith [hi.1,hp.1]
  constructor <;> linarith

theorem chosenWidth_pos {S : ℝ} (hS : 0 < S) : 0 < chosenWidth S := by
  have hi : 0 < inverseWidth S := lt_min hS Cycle63.Optimization.inverseWidthCap_pos
  have hp : 0 < plainWidth S := lt_min hS Cycle63.Optimization.plainWidthCap_pos
  dsimp [chosenWidth]
  positivity

/-- The chosen width is at least the live ratio times the inverse width: the plain width is at
least the ratio of the plain cap to the inverse cap times the inverse width. -/
theorem chosenWidth_lower {S : ℝ} (hS : 0 ≤ S) :
    Cycle63.Optimization.liveRatio*min S Cycle63.Optimization.inverseWidthCap ≤ chosenWidth S := by
  have hI := Cycle63.Optimization.inverseWidthCap_pos
  have hP := Cycle63.Optimization.plainWidthCap_pos
  have hPI := Cycle63.Optimization.plainWidthCap_le_inverse
  set ratio := Cycle63.Optimization.plainWidthCap/Cycle63.Optimization.inverseWidthCap with hratio
  have hr0 : 0 ≤ ratio := div_nonneg hP.le hI.le
  have hr1 : ratio ≤ 1 := (div_le_one hI).mpr hPI
  have hrw : ratio*Cycle63.Optimization.inverseWidthCap = Cycle63.Optimization.plainWidthCap := div_mul_cancel₀ _ hI.ne'
  have hsmall : ratio*min S Cycle63.Optimization.inverseWidthCap ≤ min S Cycle63.Optimization.plainWidthCap := by
    apply le_min
    · have hm := min_le_left S Cycle63.Optimization.inverseWidthCap
      have hn := le_min hS hI.le
      nlinarith
    · have hm := min_le_right S Cycle63.Optimization.inverseWidthCap
      nlinarith
  have hlive : Cycle63.Optimization.liveRatio = (2 + ratio)/3 := by
    rw [hratio, Cycle63.Optimization.liveRatio_eq]
    unfold Cycle63.Optimization.plainWidthCap Cycle63.Optimization.inverseWidthCap Cycle63.Optimization.plainCapacityCost
    field_simp [Cycle63.Optimization.capUnit_pos.ne']
    ring
  dsimp [chosenWidth,inverseWidth,plainWidth]
  rw [hlive]
  nlinarith

theorem chosenWidth_mono {S T : ℝ} (h : S ≤ T) : chosenWidth S ≤ chosenWidth T := by
  have hi := min_le_min_right Cycle63.Optimization.inverseWidthCap h
  have hp := min_le_min_right Cycle63.Optimization.plainWidthCap h
  dsimp [chosenWidth,inverseWidth,plainWidth]
  linarith

theorem zero_width_count {d p : ℝ} (hd : d ≤ Cycle63.Optimization.markedBinTop) : count d p 0 = density d := by
  have hh := gain_identity (p:=p) (s:=0) hd
  simp only [gain,mul_zero,zero_mul,zero_div] at hh
  linarith

theorem cutoff_bounds {d p s : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ Cycle63.Optimization.chosenWidthCap) :
    1 ≤ cutoff d p s ∧ cutoff d p s ≤ 3/2 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hcap := Cycle63.Optimization.chosenWidthCap_bounds
  have hden : 0 < 5-2*d := by linarith
  have hdpos : 0 ≤ d := by linarith
  have hps : p*s ≤ 1/2*Cycle63.Optimization.chosenWidthCap := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hs)]
  have hps0 : 0 ≤ p*s := mul_nonneg hp0 hs0
  have hbound := mul_le_mul_of_nonneg_left hps hdpos
  have hnon := mul_nonneg hdpos hps0
  unfold cutoff
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

/-- Below the inverse length cap the inverse moment has room for the inverse width cap. -/
theorem inverse_capacities {r s : ℝ} (hr : r < Cycle63.Optimization.inverseLengthCap)
    (hs : s ≤ Cycle63.Optimization.inverseWidthCap) :
    r+2*s < 1 ∧ 2*r+8*s < 3 := by
  have hsum := Cycle63.Optimization.inverse_caps_sum
  have hu := Cycle63.Optimization.capUnit_bounds
  unfold Cycle63.Optimization.inverseLengthCap Cycle63.Optimization.countSlope Cycle63.Optimization.inverseWidthCap at *
  constructor <;> linarith

/-- Up to the plain length cap the plain moment has room for the plain width cap. -/
theorem plain_capacity {m s : ℝ} (hm : m ≤ Cycle63.Optimization.plainLengthCap) (hs : s ≤ Cycle63.Optimization.plainWidthCap) :
    2*m+6*Cycle63.Optimization.plainCapacityCost*s ≤ 1 := by
  have hsum := Cycle63.Optimization.plain_caps_sum
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 6*Cycle63.Optimization.plainCapacityCost by unfold Cycle63.Optimization.plainCapacityCost; norm_num)
  nlinarith

/-- The marked count is at least `1 - c_L d` up to the bin top, with equality at the bin top, the
largest chosen width and slot amplitude `1/2`. -/
theorem count_lower {d p s : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ Cycle63.Optimization.chosenWidthCap) :
    1-Cycle63.Optimization.countSlope*d ≤ count d p s := by
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hc := Cycle63.Optimization.countSlope_bounds
  have hw := Cycle63.Optimization.chosenWidthCap_bounds
  have hE := Cycle63.Optimization.count_slope_identity
  have hden : 0 < 5-2*d := by linarith
  have hid : (5-2*d)*(count d p s-(1-Cycle63.Optimization.countSlope*d)) =
      d*((Cycle63.Optimization.markedBinTop-d)*(2*Cycle63.Optimization.countSlope-6*Cycle63.Optimization.chosenWidthCap)
        +(Cycle63.Optimization.chosenWidthCap-2*p*s)*(5-6*d)) := by
    have hc : (5-2*d)*count d p s = (5-2*d)/6+(5/6-d)*(5-12*d*p*s) := by
      unfold count cutoff
      field_simp
    linear_combination hc + d*hE
  have hn : 0 ≤ d*((Cycle63.Optimization.markedBinTop-d)*(2*Cycle63.Optimization.countSlope-6*Cycle63.Optimization.chosenWidthCap)
      +(Cycle63.Optimization.chosenWidthCap-2*p*s)*(5-6*d)) := by
    have h1 : 0 ≤ Cycle63.Optimization.markedBinTop-d := by linarith
    have h2 : 0 ≤ 2*Cycle63.Optimization.countSlope-6*Cycle63.Optimization.chosenWidthCap := by linarith
    have h3 : 0 ≤ 5-6*d := by linarith
    have h4 : 0 ≤ Cycle63.Optimization.chosenWidthCap-2*p*s := by nlinarith
    positivity
  have hh : 0 ≤ count d p s-(1-Cycle63.Optimization.countSlope*d) :=
    (mul_nonneg_iff_of_pos_left hden).mp (hid.symm ▸ hn)
  linarith

/-- The inverse and plain estimates select independent subproducts. The
weighted effective width reflects their different coefficients in the length
balance, and each selected subproduct obeys its own moment capacity. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ Cycle63.Optimization.markedBinTop)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (heps : 0 ≤ eps)
    (hlength : cutoff d p (chosenWidth S)-eps ≤ r+m)
    (hrcap : r ≤ cutoff d p (chosenWidth S)+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r < Cycle63.Optimization.inverseLengthCap → E ≤ 1-d*r-2*d*p*inverseWidth S+loss)
    (hPM : m ≤ Cycle63.Optimization.plainLengthCap → E ≤ 1-2*d*m-2*d*p*plainWidth S+loss) :
    E ≤ count d p (chosenWidth S)+loss+eps := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hc := Cycle63.Optimization.countSlope_bounds
  have hdpos : 0 ≤ d := by linarith
  obtain ⟨hs0,hsS,hs⟩ := chosenWidth_bounds hS
  have hlow := count_lower hdpos hd hp hs0 hs
  have hid := count_identity (p:=p) (s:=chosenWidth S) hd
  have hmix : 3*chosenWidth S=2*inverseWidth S+plainWidth S := by
    unfold chosenWidth
    ring
  by_cases hr : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hir : r < Cycle63.Optimization.inverseLengthCap
    · by_cases hpm : m ≤ Cycle63.Optimization.plainLengthCap
      · have hi := hIM hir
        have hp' := hPM hpm
        have hlen := mul_le_mul_of_nonneg_left hlength hdpos
        have he := mul_nonneg hdpos heps
        have he' := mul_le_mul_of_nonneg_right hd heps
        have hmix' := congrArg (fun x : ℝ => d*p*x) hmix
        nlinarith
      · have hm : Cycle63.Optimization.plainLengthCap ≤ m := le_of_lt (lt_of_not_ge hpm)
        have hmul := mul_le_mul_of_nonneg_left hm hdpos
        unfold Cycle63.Optimization.plainLengthCap at hmul
        linarith
    · have hr' : Cycle63.Optimization.inverseLengthCap ≤ r := le_of_not_gt hir
      have hmul := mul_le_mul_of_nonneg_left hr' hdpos
      unfold Cycle63.Optimization.inverseLengthCap at hmul
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

/-- The live rate of a bin of the HIGH range lies in `[0, 1/6]`. -/
theorem liveRate_bounds {d : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ 3/4) :
    0 ≤ Cycle63.Optimization.liveRate d ∧ Cycle63.Optimization.liveRate d ≤ 1/6 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hd' : Cycle63.Arithmetic.q0 ≤ d ∧ d ≤ 3/4 := ⟨hd0, hd⟩
  unfold Cycle63.Optimization.liveRate Cycle63.Optimization.liveRatio
    Cycle63.Optimization.chosenPerUnit Cycle63.Optimization.plainCapacityCost
    Cycle63.Optimization.halfGain
  constructor <;> (apply le_of_lt; rat_pos [hq0b, hd'])

theorem halfGain_nonneg {d : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ 3/4) :
    0 ≤ Cycle63.Optimization.halfGain d := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hden : 0 < 5-2*d := by linarith
  unfold Cycle63.Optimization.halfGain
  apply div_nonneg _ hden.le
  nlinarith

/-- The capped live gain is at most the half-amplitude gain of the chosen width. -/
theorem liveRate_le_chosen {d S : ℝ} (hd0 : Cycle63.Arithmetic.q0 ≤ d) (hd : d ≤ 3/4)
    (hS0 : 0 ≤ S) :
    Cycle63.Optimization.liveRate d*min S Cycle63.Optimization.inverseWidthCap ≤
      Cycle63.Optimization.halfGain d*chosenWidth S := by
  have h := mul_le_mul_of_nonneg_left (chosenWidth_lower hS0) (halfGain_nonneg hd0 hd)
  unfold Cycle63.Optimization.liveRate
  linarith

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
    count d p (chosenWidth S)+2*d*p*S ≤
      density d+d*S-Cycle63.Optimization.halfGain d*chosenWidth S := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have htop := Cycle63.Optimization.markedBinTop_bounds
  have hb := chosenWidth_bounds hS0
  exact joint_width_gap hd0 hd hp hb.1 hb.2.1

#print axioms fiber_exponent
end
end VariableSupply
