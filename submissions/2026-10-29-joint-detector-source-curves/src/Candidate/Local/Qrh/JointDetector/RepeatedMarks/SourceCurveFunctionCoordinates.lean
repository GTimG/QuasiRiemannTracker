/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveCertificateSemantic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionCoordinates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set SourceCurveCertificate

/-- Function coordinates permit arbitrary fixed polynomial degrees. -/
structure Path where
 q0 : ℝ
 y : ℝ → ℝ
 k : ℝ → ℝ
 a : ℝ → ℝ
 eps : ℝ
 cap : ℝ

def Path.state (p : Path) (u : ℝ) : State :=
 ⟨p.q0+u,p.y u,p.k u,p.a u,p.eps,p.cap⟩
def Path.dB (p : Path) (u : ℝ) : ℝ :=
 (p.state u).S/(6*(p.state u).q^2*(p.state u).y^2)
def Path.dL (p : Path) (u : ℝ) : ℝ := p.k u/(p.y u)^2

theorem slope_derivative (p : Path) {u : ℝ}
 (hy : HasDerivAt p.y (-p.k u) u) (hy0 : p.y u ≠ 0) :
 HasDerivAt (fun x => (p.state x).L) (p.dL u) u :=
 SourceCurveCoordinates.hasDerivAt_slope hy hy0

theorem intercept_derivative (p : Path) {u : ℝ}
 (hy : HasDerivAt p.y (-p.k u) u)
 (hq : p.q0+u ≠ 0) (hy0 : p.y u ≠ 0) :
 HasDerivAt (fun x => (p.state x).B) (p.dB u) u := by
 have dq := (hasDerivAt_id u).const_add p.q0
 have hd := (dq.const_add 1).div ((dq.const_mul 6).mul hy)
   (mul_ne_zero (mul_ne_zero (by norm_num) hq) hy0)
 convert hd using 1
 · rfl
 · dsimp [Path.dB,Path.state,State.S]
   field_simp <;> ring

structure Data (p : Path) (lo hi : ℝ) : Prop where
 B_derivative : ∀ u∈Icc lo hi, HasDerivAt (fun x => (p.state x).B) (p.dB u) u
 L_derivative : ∀ u∈Icc lo hi, HasDerivAt (fun x => (p.state x).L) (p.dL u) u
 L_derivative_pos : ∀ u∈Icc lo hi, 0 < p.dL u
 s_continuous : ContinuousOn (fun u => (p.state u).s) (Icc lo hi)
 n_continuous : ContinuousOn (fun u => (p.state u).n) (Icc lo hi)
 r_continuous : ContinuousOn (fun u => (p.state u).r) (Icc lo hi)
 tangent_ratio : ∀ u∈Icc lo hi, p.dB u/p.dL u=(p.state u).s

/-- This calculus adapter depends on no degree bound or count theorem. The
strict source geometry may be supplied by either selected-cutoff instance. -/
theorem coordinate_data (p : Path) {lo hi : ℝ}
 (hy : ∀ u∈Icc lo hi, HasDerivAt p.y (-p.k u) u)
 (hk : ContinuousOn p.k (Icc lo hi)) (ha : ContinuousOn p.a (Icc lo hi))
 (hf : ∀ u∈Icc lo hi, CommonFacts (p.state u))
 (hkpos : ∀ u∈Icc lo hi, 0 < p.k u) : Data p lo hi := by
 have cq : ContinuousOn (fun u => (p.state u).q) (Icc lo hi) := by
   dsimp [Path.state]; fun_prop
 have cy : ContinuousOn p.y (Icc lo hi) := fun u hu =>
   (hy u hu).continuousAt.continuousWithinAt
 have cS : ContinuousOn (fun u => (p.state u).S) (Icc lo hi) := by
   dsimp [State.S,Path.state]; fun_prop
 have cD : ContinuousOn (fun u => (p.state u).D) (Icc lo hi) := by
   dsimp [State.D,Path.state]; fun_prop
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · intro u hu; exact intercept_derivative p (hy u hu) (hf u hu).q_pos.ne' (hf u hu).y_pos.ne'
 · intro u hu; exact slope_derivative p (hy u hu) (hf u hu).y_pos.ne'
 · intro u hu; exact div_pos (hkpos u hu) (sq_pos_of_pos (hf u hu).y_pos)
 · exact cS.div cD (fun u hu => (hf u hu).D_pos.ne')
 · dsimp [State.n,Path.state]; fun_prop
 · exact ha.div cq (fun u hu => (hf u hu).q_pos.ne')
 · intro u hu
   exact SourceCurveCoordinates.tangent_ratio (hf u hu).q_pos.ne'
     (hf u hu).y_pos.ne' (hkpos u hu).ne'

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionCoordinates
