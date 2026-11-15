/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Continuous ordinary stage hypotheses from the authoritative rational certificate.
The checked values are cast, not recomputed by floating-point arithmetic. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.StageInterpolation

set_option autoImplicit false
noncomputable section
namespace Qrh.TwoSlot.AnchorZeroLoss.Certificate
open Qrh.TwoSlot.AnchorExtension.ChainData

private theorem positive_cast {q : ℚ} {x : ℝ} (h : 0<q) (hx : (q:ℝ)=x) : 0<x := by
  rw [←hx]
  exact_mod_cast h

/-- The three actual ordinary/reference gates at one rational endpoint. -/
theorem ordinary_endpoint (s : Stage) (r : ℚ) (h : ∀v∈s.gates r,0<v) :
    0<137/1000-fS (s.R:ℝ) s.gain s.cut r ∧
    0<9/10-(r:ℝ)-fS (s.R:ℝ) s.gain s.cut r-4*fu (s.R:ℝ) r ∧
    0<5/6+21/250-(r:ℝ)-fS (s.R:ℝ) s.gain s.cut r-3*fu (s.R:ℝ) r-1/100 := by
  have h2 := h (137/1000-fS s.R s.gain s.cut r) (by simp [Stage.gates])
  have h4 := h (9/10-r-fS s.R s.gain s.cut r-4*fu s.R r) (by simp [Stage.gates])
  have h6 := h (5/6+21/250-r-fS s.R s.gain s.cut r-3*fu s.R r-1/100) (by simp [Stage.gates])
  refine ⟨positive_cast h2 ?_,positive_cast h4 ?_,positive_cast h6 ?_⟩ <;>
    (simp only [fS,fY,fu]; push_cast; ring)

/-- Every real width of a checked stage satisfies the ordinary step hypotheses. -/
theorem ordinary_hyp (s : Stage) (hok : s.ok=true) (r : ℝ)
    (hlo : (s.left:ℝ)≤r) (hhi : r≤s.R) :
    Qrh.MarkedAnchor.Price.StageHyp s.R s.gain s.cut r := by
  obtain ⟨hb,hL,hR⟩ := Stage.ok_sound hok
  rcases hb with ⟨hR0,hR1,hleft,hlt,hk0,hk1,hz,ha1,ha1hi,huL,hrest⟩
  have hR0r : (7/10:ℝ)≤s.R := by
    have h : (((7/10:ℚ):ℝ)≤(s.R:ℝ)) := Rat.cast_le.mpr hR0
    norm_num at h ⊢; exact h
  have hR1r : (s.R:ℝ)≤311/400 := by
    have h : ((s.R:ℝ)≤((311/400:ℚ):ℝ)) := Rat.cast_le.mpr hR1
    norm_num at h ⊢; exact h
  have hleftr : (1467/2000:ℝ)≤s.left := by
    have h : (((1467/2000:ℚ):ℝ)≤(s.left:ℝ)) := Rat.cast_le.mpr hleft
    norm_num at h ⊢; exact h
  have hltr : (s.left:ℝ)<s.R := by exact_mod_cast hlt
  have hk0r : (45457/125000:ℝ)≤s.cut := by
    have h : (((45457/125000:ℚ):ℝ)≤(s.cut:ℝ)) := Rat.cast_le.mpr hk0
    norm_num at h ⊢; exact h
  have hk1r : (s.cut:ℝ)<1/2 := by
    have h : ((s.cut:ℝ)<((1/2:ℚ):ℝ)) := Rat.cast_lt.mpr hk1
    norm_num at h ⊢; exact h
  have hzr : (0:ℝ)≤s.gain := by exact_mod_cast hz
  have huLr : fu (s.R:ℝ) s.left≤1/10000 := by
    have h : ((fu s.R s.left:ℚ):ℝ)≤((1/10000:ℚ):ℝ) := Rat.cast_le.mpr huL
    simpa only [fu,Rat.cast_div,Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat] using h
  have hRp : (0:ℝ)<s.R := by linarith
  have hle := div_le_div_of_nonneg_right hlo hRp.le
  have hur : fu (s.R:ℝ) r≤1/10000 := by dsimp only [fu] at huLr ⊢; linarith
  obtain ⟨h2L,h4L,h6L⟩ := ordinary_endpoint s s.left hL
  obtain ⟨h2R,h4R,h6R⟩ := ordinary_endpoint s s.R hR
  have h2Req : fS (s.R:ℝ) s.gain s.cut s.R=(1-(s.R:ℝ))/2+s.gain := by
    unfold fS fY fu
    rw [div_self hRp.ne']
    ring
  have hSR : (1-(s.R:ℝ))/2+s.gain≤137/1000 := by rw [h2Req] at h2R; linarith
  obtain ⟨g2,g4,g6⟩ := Qrh.TwoSlot.AnchorContinuum.ordinary_gates_between hltr hlo hhi
    h2L h2R h4L h4R h6L h6R
  exact ⟨⟨hR0r,by linarith⟩,⟨hleftr.trans hlo,hhi⟩,⟨hk0r,hk1r⟩,hzr,hSR,hur,g2,g4,g6⟩

end Qrh.TwoSlot.AnchorZeroLoss.Certificate
#print axioms Qrh.TwoSlot.AnchorZeroLoss.Certificate.ordinary_hyp
