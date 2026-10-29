/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Price
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateBounds
import Candidate.Local.Qrh.JointDetector.RestartSelectedCount

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open Set

/-- Literal density/amplitude label domain, shared by the count and the
physical amplitude response. -/
def DensityAmplitude (q : ℝ) :=
  {p : ℝ × ℝ // q ≤ p.1 ∧ p.1 ≤ 3/4 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1}

/-- Convert a genuinely bounded count rate to the full affine supremum.
The rate depends on the labels, never on the live coordinate increments. -/
def familyOfRate (q : ℝ) (hq : q ∈ Ioc (0:ℝ) (3/4))
    (rate : ℝ → ℝ → ℝ)
    (hrate : ∀ ν ∈ Icc q (3/4:ℝ), ∀ v ∈ Icc (0:ℝ) ν,
      rate ν v ∈ Icc (0:ℝ) 1) : WeightedFamily where
  Index := DensityAmplitude q
  nonempty := ⟨⟨(q,0),⟨le_rfl,hq.2,le_rfl,hq.1.le⟩⟩⟩
  density i := i.val.1
  amplitude i := i.val.2
  rate i := rate i.val.1 i.val.2
  density_mem i := ⟨hq.1.le.trans i.property.1,i.property.2.1⟩
  amplitude_mem i := ⟨i.property.2.2.1,i.property.2.2.2.trans i.property.2.1⟩
  rate_mem i := hrate _ ⟨i.property.1,i.property.2.1⟩ _ i.property.2.2

/-- Same-event minimum, restricted to the actual selected-norm range.
Below its cutoff, the repeated-mark estimate is retained by itself. -/
def combineSelected (rate : ℝ → ℝ → ℝ) (ν v : ℝ) : ℝ :=
  if (500001/1000000:ℝ) ≤ v then
    min (rate ν v) (detectorRate ν v)
  else rate ν v

theorem combineSelected_mem {rate : ℝ → ℝ → ℝ} {ν v : ℝ}
    (hν : ν ≤ 3/4) (hv : v ∈ Icc (0:ℝ) ν)
    (hrate : rate ν v ∈ Icc (0:ℝ) 1) :
    combineSelected rate ν v ∈ Icc (0:ℝ) 1 := by
  unfold combineSelected
  split_ifs with hd
  · have he := FineNaturalCount.detectorRate_bounds hν ⟨hd,hv.2.trans hν⟩
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
end Qrh.JointDetector.RepeatedMarks
