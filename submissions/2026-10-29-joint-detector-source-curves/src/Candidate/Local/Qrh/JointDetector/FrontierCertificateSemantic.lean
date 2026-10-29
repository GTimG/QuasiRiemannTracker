/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCertificateSemantic
import Candidate.Local.Qrh.JointDetector.FrontierSourceCurveTheorem
namespace Qrh.JointDetector.FrontierSourceCurveCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open RepeatedMarks.SourceCurveCertificate FrontierRepeatedMarks.SourceCurve

/-- Only the selected-cutoff gate changes; all other polynomial gates retain
exactly their existing integer certificate representation. -/
def combined (p : State) (i : Fin 10) : ℝ :=
 if i=3 then p.a*p.n-(500000001/1000000000:ℝ)*p.q else p.combined i

private theorem budget_identity (p : State) (hq : p.q ≠ 0) (hy : p.y ≠ 0)
 (hk : p.k ≠ 0) : p.B-p.L*p.s=1/p.D := by
 dsimp [State.B,State.L,State.s,State.S,State.D]
 field_simp [hq,hy,hk] <;> ring

private theorem derivative_identity (p : State) (ν : ℝ) (hq : p.q ≠ 0)
 (hd : p.D ≠ 0) (hb : p.B-p.L*p.s=1/p.D) :
 p.derivative ν=(p.D*p.q)*derivativeRay (p.B-p.L*p.s) p.s p.r ν := by
 rw [hb]; dsimp [State.derivative,State.s,State.r,derivativeRay]
 field_simp [hq,hd] <;> ring
private theorem repeated_identity (p : State) (ν : ℝ) (hq : p.q ≠ 0)
 (hd : p.D ≠ 0) (hb : p.B-p.L*p.s=1/p.D) :
 p.repeated ν=(p.D*p.q^2)*repeatedRay (p.B-p.L*p.s) p.s p.r ν := by
 rw [hb]; dsimp [State.repeated,State.s,State.r,repeatedRay]
 field_simp [hq,hd] <;> ring
private theorem selected_identity (p : State) (ν : ℝ) (hq : p.q ≠ 0)
 (hd : p.D ≠ 0) (hb : p.B-p.L*p.s=1/p.D) :
 p.selected ν=(p.D*p.q^2)*selectedRay (p.B-p.L*p.s) p.s p.r ν := by
 rw [hb]; dsimp [State.selected,State.s,State.r,selectedRay]
 field_simp [hq,hd] <;> ring

theorem ray_crossing (p : State) (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (hc : ∀ i, 0 < p.common i) (h : ∀ i, 0 < combined p i) :
 RayCrossing p.B p.L p.s p.n p.r := by
 have f := common_facts p heps hcap hc
 have hk : p.k ≠ 0 := by have hh := hc 4; simpa [State.common] using hh.ne'
 have hb := budget_identity p f.q_pos.ne' f.y_pos.ne' hk
 have hdq : 0 < p.D*p.q := mul_pos f.D_pos f.q_pos
 have hdqq : 0 < p.D*p.q^2 := mul_pos f.D_pos (sq_pos_of_pos f.q_pos)
 have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
 have h4 := h 4; have h5 := h 5; have h6 := h 6
 have h7 := h 7; have h8 := h 8; have h9 := h 9
 norm_num [combined,State.combined] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
 refine ⟨f.B_pos,f.B_max.le,f.L_min,f.s_pos,f.s_cap,f.n_pos,f.n_upper,
   div_pos h1 f.q_pos,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · dsimp [State.r]; exact (div_le_one f.q_pos).2 (by linarith)
 · dsimp [State.r]
   rw [div_mul_eq_mul_div]
   have hi : (500000001/1000000000:ℝ)*p.q < p.a*p.n := by linarith
   exact (lt_div_iff₀ f.q_pos).2 hi
 · rw [derivative_identity p p.n f.q_pos.ne' f.D_pos.ne' hb] at h4
   nlinarith
 · rw [derivative_identity p (3/4) f.q_pos.ne' f.D_pos.ne' hb] at h7
   nlinarith
 · rw [repeated_identity p p.n f.q_pos.ne' f.D_pos.ne' hb] at h5
   exact (mul_pos_iff_of_pos_left hdqq).mp h5
 · rw [repeated_identity p (3/4) f.q_pos.ne' f.D_pos.ne' hb] at h8
   exact (mul_pos_iff_of_pos_left hdqq).mp h8
 · rw [selected_identity p p.n f.q_pos.ne' f.D_pos.ne' hb] at h6
   exact (mul_pos_iff_of_pos_left hdqq).mp h6
 · rw [selected_identity p (3/4) f.q_pos.ne' f.D_pos.ne' hb] at h9
   exact (mul_pos_iff_of_pos_left hdqq).mp h9

end
end Qrh.JointDetector.FrontierSourceCurveCertificate
#print axioms Qrh.JointDetector.FrontierSourceCurveCertificate.ray_crossing
