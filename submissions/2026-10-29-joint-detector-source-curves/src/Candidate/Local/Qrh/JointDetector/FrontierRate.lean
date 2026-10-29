/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed selected cutoff .500000001, same original-row event and full amplitude supremum.
Inherited notices follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Rate
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Price
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateBounds
import Candidate.Local.Qrh.JointDetector.FrontierSelectedCount

namespace Qrh.JointDetector.FrontierRepeatedMarks
noncomputable section
set_option autoImplicit false
open Set RepeatedMarks

/-- Literal density/amplitude label domain, shared by the count and the
physical amplitude response. -/
abbrev DensityAmplitude := RepeatedMarks.DensityAmplitude
abbrev familyOfRate := @RepeatedMarks.familyOfRate

/-- Same-event minimum, restricted to the actual selected-norm range.
Below its cutoff, the repeated-mark estimate is retained by itself. -/
def combineSelected (rate : ℝ → ℝ → ℝ) (ν v : ℝ) : ℝ :=
  if (500000001/1000000000:ℝ) ≤ v then
    min (rate ν v) (detectorRate ν v)
  else rate ν v

theorem combineSelected_mem {rate : ℝ → ℝ → ℝ} {ν v : ℝ}
    (hν : ν ≤ 3/4) (hv : v ∈ Icc (0:ℝ) ν)
    (hrate : rate ν v ∈ Icc (0:ℝ) 1) :
    combineSelected rate ν v ∈ Icc (0:ℝ) 1 := by
  unfold combineSelected
  split_ifs with hd
  · have he := FrontierNaturalCount.detectorRate_bounds hν ⟨hd,hv.2.trans hν⟩
    exact ⟨le_min hrate.1 (by linarith), (min_le_left _ _).trans hrate.2⟩
  · exact hrate

/-- The precise reported repeated-mark rate, optionally combined with the
same-event selected count before maximizing over amplitude. -/
def repeatedFamily (B L c q : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 1)
    (hL : (3/2:ℝ) ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 1/6)
    (hq : q ∈ Ioc (0:ℝ) (3/4)) (combined : Bool) : WeightedFamily :=
  familyOfRate q hq
    (fun ν v => if combined then combineSelected (rawRepeatedCountRate B L c) ν v
      else rawRepeatedCountRate B L c ν v)
    (by
      intro ν hν v hv
      have hr := rawRepeatedCountRate_bounds hB0 hB hL hc0 hc
        (hq.1.trans_le hν.1) hν.2 hv.1 hv.2
      have hrate : rawRepeatedCountRate B L c ν v ∈ Icc (0:ℝ) 1 :=
        ⟨by linarith [hr.1,hν.2],hr.2⟩
      split
      · exact combineSelected_mem hν.2 hv hrate
      · exact hrate)

end

 theorem combineSelected_le_raw (rate : ℝ → ℝ → ℝ) (ν v : ℝ) :
     combineSelected rate ν v ≤ rate ν v := by
   unfold combineSelected
   split_ifs
   · exact min_le_left _ _
   · exact le_rfl
 theorem combineSelected_le_selected (rate : ℝ → ℝ → ℝ) {ν v : ℝ}
     (hv : (500000001/1000000000:ℝ) ≤ v) :
     combineSelected rate ν v ≤ detectorRate ν v := by
   simp only [combineSelected,if_pos hv]
   exact min_le_right _ _

end Qrh.JointDetector.FrontierRepeatedMarks
