/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RateContinuity

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open Set

/-- One fixed buffer pays both lowering the zero line and clipping the
amplitude at that lowered line. The buffer precedes every live row and slot. -/
theorem buffered_rate_budget (B L c floor dmin loss : ℝ)
    (hL : 3/2≤L) (hfloor : 0<floor) (hdmin : 0<dmin) (hloss : 0<loss) :
    ∃buffer : ℝ,0<buffer ∧ ∀ν v e : ℝ,
      floor≤ν → ν≤3/4 → dmin≤v → v≤ν → 0≤e → e≤buffer →
      floor/2≤ν-2*e ∧ dmin/2≤min v (ν-2*e) ∧
      0≤min v (ν-2*e) ∧ min v (ν-2*e)≤ν-2*e ∧
      rawRepeatedCountRate B L c (ν-2*e) (min v (ν-2*e))≤
        rawRepeatedCountRate B L c ν v+loss := by
  obtain ⟨η,hη,hbuffer⟩ := rawRate_buffer (B:=B) (c:=c) hL
    (show 0<floor/2 by positivity) hloss
  let buffer := min (floor/8) (min (dmin/8) (η/8))
  have hb : 0<buffer := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨buffer,hb,?_⟩
  intro ν v e hν hνhi hv hvν he heb
  have heF : e≤floor/8 := heb.trans (min_le_left _ _)
  have heD : e≤dmin/8 := heb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heη : e≤η/8 := heb.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν0 : floor/2≤ν-2*e := by linarith
  have hv0 : dmin/2≤min v (ν-2*e) := le_min (by linarith) (by linarith)
  have hdom : (ν,v)∈rateDomain (floor/2) := ⟨by linarith,hνhi,hdmin.le.trans hv,hvν⟩
  have hdom' : (ν-2*e,min v (ν-2*e))∈rateDomain (floor/2) :=
    ⟨hν0,by linarith,by linarith,min_le_right _ _⟩
  have hdiffν : |(ν-2*e)-ν|<η := by
    rw [show (ν-2*e)-ν= -(2*e) by ring,abs_neg,abs_of_nonneg (by positivity)]
    linarith
  have hdiffv : |min v (ν-2*e)-v|<η := by
    apply lt_of_le_of_lt (abs_le.mpr ?_) (show 2*e<η by linarith)
    constructor
    · have hl : v-2*e≤min v (ν-2*e) := le_min (by linarith) (by linarith)
      linarith
    · have hu := min_le_left v (ν-2*e)
      linarith
  have hr := hbuffer (ν-2*e) (min v (ν-2*e)) ν v hdom' hdom hdiffν hdiffv
  refine ⟨hν0,hv0,by linarith,min_le_right _ _,?_⟩
  have hh := (abs_lt.mp hr).2
  linarith

end
end Qrh.JointDetector.RepeatedMarks
