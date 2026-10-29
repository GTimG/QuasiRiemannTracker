/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCertificateState

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open SourceCurve

structure CommonFacts (p : State) : Prop where
 q_pos : 0 < p.q
 y_pos : 0 < p.y
 D_pos : 0 < p.D
 B_pos : 0 < p.B
 B_min : 9/10 ≤ p.B
 B_max : p.B < 1
 L_min : 3/2 ≤ p.L
 s_pos : 0 < p.s
 s_cap : p.s < 1/10
 n_pos : 0 < p.n
 n_upper : p.n < 3/4
 C_nonneg : 0 ≤ 6*p.B-p.L
 low_gap : 0 < p.L-p.n*(6*p.B-p.L)
 gates : ∀ i, 0 < SourceCurveOpenGeometry.gate p.B p.L p.s 0 (1/10) i

theorem common_facts (p : State) (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (h : ∀ i, 0 < p.common i) : CommonFacts p := by
 have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
 have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
 have h8 := h 8; have h9 := h 9; have h10 := h 10; have h11 := h 11
 have h12 := h 12; have h13 := h 13; have h14 := h 14; have h15 := h 15
 have h16 := h 16; have h17 := h 17; have h18 := h 18; have h19 := h 19
 norm_num [State.common,hcap] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
 have hq : 0 < p.q := by dsimp [State.n] at h0; linarith
 have hd : 0 < p.D := h5
 have hden : 0 < 6*p.q*p.y := by positivity
 have hb : 0 < p.B := by dsimp [State.B]; positivity
 have hs : 0 < p.s := div_pos h7 hd
 have hscap : p.s < 1/10 := (div_lt_iff₀ hd).2 (by linarith)
 have hbase : p.B-p.L*p.s=1/p.D := by
  dsimp [State.B,State.L,State.s,State.S,State.D]
  field_simp; ring
 have hC : 6*p.B-p.L=1/(p.q*p.y) := by
  dsimp [State.B,State.L]; field_simp; ring
 have hgap : p.L-p.n*(6*p.B-p.L)=p.eps/(p.q*p.y) := by
  rw [hC]; dsimp [State.L,State.n]; field_simp; ring
 refine ⟨hq,h2,hd,hb,?_,?_,?_,hs,hscap,by linarith,by dsimp [State.n]; linarith,?_,?_,?_⟩
 · dsimp [State.B]; apply (le_div_iff₀ hden).2; linarith
 · dsimp [State.B]; apply (div_lt_one hden).2; linarith
 · dsimp [State.L]; apply (le_div_iff₀ h2).2; linarith
 · rw [hC]; positivity
 · rw [hgap]; positivity
 · intro i
   fin_cases i <;> norm_num [SourceCurveOpenGeometry.gate]
   · have hi : 1-p.B+(p.L-2)*p.s=(p.D-1-2*p.S)/p.D := by
      calc
       _ = 1-(p.B-p.L*p.s)-2*p.s := by ring
       _ = _ := by rw [hbase]; dsimp [State.s]; field_simp [hd.ne'] <;> ring
     rw [hi]; exact div_pos (by linarith) hd
   · have hi : 1-p.B+(p.L-2)*(1/10)=
       (6*p.q*p.y*(1-2*(1/10))-(1+p.q)+6*p.q*(1/10))/(6*p.q*p.y) := by
      dsimp [State.B,State.L]; field_simp; ring
     rw [hi]; exact div_pos (by linarith) hden
   · have hi : 1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*p.s=
       (31/20*p.D-3/2-5/2*p.S)/p.D := by
      calc
       _ = 31/20-3/2*(p.B-p.L*p.s)-5/2*p.s := by ring
       _ = _ := by rw [hbase]; dsimp [State.s]; field_simp [hd.ne'] <;> ring
     rw [hi]; exact div_pos (by linarith) hd
   · have hi : 1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*(1/10)=
       (6*p.q*p.y*(31/20-5/2*(1/10))-3/2*(1+p.q-6*p.q*(1/10)))/(6*p.q*p.y) := by
      dsimp [State.B,State.L]; field_simp; ring
     rw [hi]; exact div_pos (by linarith) hden
   · have hi : 1-p.B+(p.L-1)*p.s=(p.D-1-p.S)/p.D := by
      calc
       _ = 1-(p.B-p.L*p.s)-p.s := by ring
       _ = _ := by rw [hbase]; dsimp [State.s]; field_simp [hd.ne'] <;> ring
     rw [hi]; exact div_pos (by linarith) hd
   · have hi : 1-p.B+(p.L-1)*(1/10)=
       (6*p.q*p.y*(1-(1/10))-(1+p.q)+6*p.q*(1/10))/(6*p.q*p.y) := by
      dsimp [State.B,State.L]; field_simp; ring
     rw [hi]; exact div_pos (by linarith) hden
   · linarith
   · exact hs
   · linarith
   · dsimp [State.L]; apply (one_lt_div h2).2; linarith
   · exact hb

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
 (hc : ∀ i, 0 < p.common i) (h : ∀ i, 0 < p.combined i) :
 RayCrossing p.B p.L p.s p.n p.r := by
 have f := common_facts p heps hcap hc
 have hk : p.k ≠ 0 := by have hh := hc 4; simpa [State.common] using hh.ne'
 have hb := budget_identity p f.q_pos.ne' f.y_pos.ne' hk
 have hdq : 0 < p.D*p.q := mul_pos f.D_pos f.q_pos
 have hdqq : 0 < p.D*p.q^2 := mul_pos f.D_pos (sq_pos_of_pos f.q_pos)
 have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
 have h4 := h 4; have h5 := h 5; have h6 := h 6
 have h7 := h 7; have h8 := h 8; have h9 := h 9
 norm_num [State.combined] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
 refine ⟨f.B_pos,f.B_max.le,f.L_min,f.s_pos,f.s_cap,f.n_pos,f.n_upper,
   div_pos h1 f.q_pos,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · dsimp [State.r]; exact (div_le_one f.q_pos).2 (by linarith)
 · dsimp [State.r]
   rw [div_mul_eq_mul_div]
   have hi : (500001/1000000:ℝ)*p.q < p.a*p.n := by linarith
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

private theorem pure_derivative_identity (p : State) (ν : ℝ)
 (hd : p.D ≠ 0) (hb : p.B-p.L*p.s=1/p.D) :
 p.pureDerivative ν=p.D*derivativeRay (p.B-p.L*p.s) p.s 1 ν := by
 rw [hb]; dsimp [State.pureDerivative,State.s,derivativeRay]
 field_simp [hd] <;> ring
private theorem pure_repeated_identity (p : State) (ν : ℝ)
 (hd : p.D ≠ 0) (hb : p.B-p.L*p.s=1/p.D) :
 p.pureRepeated ν=p.D*repeatedRay (p.B-p.L*p.s) p.s 1 ν := by
 rw [hb]; dsimp [State.pureRepeated,State.s,repeatedRay]
 field_simp [hd] <;> ring

theorem pure_crossing (p : State) (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (hc : ∀ i, 0 < p.common i) (h : ∀ i, 0 < p.pure i) :
 PureCrossing p.B p.L p.s p.n := by
 have f := common_facts p heps hcap hc
 have hk : p.k ≠ 0 := by have hh := hc 4; simpa [State.common] using hh.ne'
 have hb := budget_identity p f.q_pos.ne' f.y_pos.ne' hk
 have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
 norm_num [State.pure] at h0 h1 h2 h3
 refine ⟨f.B_pos,f.B_max.le,f.L_min,f.s_pos,f.s_cap,f.n_pos,f.n_upper,?_,?_,?_,?_⟩
 · rw [pure_derivative_identity p p.n f.D_pos.ne' hb] at h0
   nlinarith [f.D_pos]
 · rw [pure_derivative_identity p (3/4) f.D_pos.ne' hb] at h2
   nlinarith [f.D_pos]
 · rw [pure_repeated_identity p p.n f.D_pos.ne' hb] at h1
   exact (mul_pos_iff_of_pos_left f.D_pos).mp h1
 · rw [pure_repeated_identity p (3/4) f.D_pos.ne' hb] at h3
   exact (mul_pos_iff_of_pos_left f.D_pos).mp h3

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveCertificate
