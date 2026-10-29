/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateBounds

namespace Qrh.JointDetector.RepeatedMarks
set_option autoImplicit false

theorem inverse_capacity {r τ : ℝ} (hr0 : 1/2<r) (hr : r<1) (hτ : 0<τ) :
    0≤max 0 ((1-r)/2-τ) ∧ max 0 ((1-r)/2-τ)≤1 ∧
      r+2*max 0 ((1-r)/2-τ)<1 ∧ 2*r+8*max 0 ((1-r)/2-τ)<3 := by
  constructor
  · exact le_max_left _ _
  by_cases h : 0≤(1-r)/2-τ
  · rw [max_eq_right h]
    constructor
    · linarith
    constructor <;> linarith
  · rw [max_eq_left (le_of_not_ge h)]
    constructor
    · norm_num
    constructor <;> linarith

theorem plain_capacity {B L c m τ : ℝ} (hm : 0≤m) (hmB : m≤B/2)
    (hL : 0<L) (hc : 0≤c) (hc1 : c≤1) (hτ : 0≤τ) :
    0≤max 0 (min c ((B-2*m)/L)-τ) ∧ max 0 (min c ((B-2*m)/L)-τ)≤1 ∧
      max 0 (min c ((B-2*m)/L)-τ)≤c ∧
      2*m+L*max 0 (min c ((B-2*m)/L)-τ)≤B := by
  have hb : 0≤(B-2*m)/L := div_nonneg (by linarith) hL.le
  have hcap : max 0 (min c ((B-2*m)/L)-τ)≤c := max_le hc
    (by linarith [min_le_left c ((B-2*m)/L)])
  have hbudget : max 0 (min c ((B-2*m)/L)-τ)≤(B-2*m)/L := max_le hb
    (by linarith [min_le_right c ((B-2*m)/L)])
  refine ⟨le_max_left _ _,hcap.trans hc1,hcap,?_⟩
  have hh := (le_div_iff₀ hL).mp hbudget
  nlinarith

/-- The actual detector lower inverse length stays strictly above onehalf
when its buffered length error fits the uniform positive cutoff gap. -/
theorem inverse_length_above_half {ν νmin p c tstar r ε : ℝ}
    (hνmin : 0<νmin) (hν : νmin≤ν) (hνhi : ν≤3/4)
    (hp0 : 0≤p) (hp : p≤1/2) (hc0 : 0≤c) (hc : c≤1/6)
    (htstar : crossingCut ν p 2 (2*p*c)≤tstar)
    (hε : ε≤νmin/2000) (hr : tstar-1/2-76*ε≤r) : 1/2<r := by
  have hgap := cap_cutoff_gap (hνmin.trans_le hν) hνhi hp0 hp hc0 hc
  linarith

end Qrh.JointDetector.RepeatedMarks
