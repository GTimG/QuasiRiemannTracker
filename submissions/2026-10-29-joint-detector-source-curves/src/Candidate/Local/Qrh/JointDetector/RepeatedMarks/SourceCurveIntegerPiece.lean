/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerState

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set SourceCurve SourceCurveCertificate

private theorem y_derivative (p : RealParams) (u : ℝ) :
 HasDerivAt (fun x => (p.state x).y) (-(p.state u).k) u := by
 convert (((hasDerivAt_const u p.y0).add ((hasDerivAt_id u).const_mul p.y1)).add
   (((hasDerivAt_id u).pow 2).const_mul p.y2)).add
   (((hasDerivAt_id u).pow 3).const_mul p.y3) using 1 <;>
   (try funext x) <;> simp [RealParams.state,Pi.add_apply] <;> ring

private theorem L_derivative (p : RealParams) (u : ℝ) (hy : (p.state u).y ≠ 0) :
 HasDerivAt (fun x => (p.state x).L) ((p.state u).k/(p.state u).y^2) u := by
 exact SourceCurveCoordinates.hasDerivAt_slope (y_derivative p u) hy

private theorem B_derivative (p : RealParams) (u : ℝ)
 (hq : (p.state u).q ≠ 0) (hy : (p.state u).y ≠ 0) :
 HasDerivAt (fun x => (p.state x).B)
   ((p.state u).S/(6*(p.state u).q^2*(p.state u).y^2)) u := by
 have dq := (hasDerivAt_id u).const_add p.q0
 have hd := (dq.const_add 1).div ((dq.const_mul 6).mul (y_derivative p u))
   (mul_ne_zero (mul_ne_zero (by norm_num) hq) hy)
 convert hd using 1
 · rfl
 · dsimp [State.S,RealParams.state]
   field_simp <;> ring

/-- A whole-interval certificate for one cubic piece gives an actual finite
source construction. The source at the right endpoint is the only source premise. -/
theorem combined_source (p : RealParams) {lo hi : ℝ} (hab : lo ≤ hi)
 (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (hc : ∀ u∈Icc lo hi, ∀ i, 0 < commonGate p i u)
 (hr : ∀ u∈Icc lo hi, ∀ i, 0 < combinedGate p i u)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource (p.state hi).B (p.state hi).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource (p.state lo).B (p.state lo).L (1/10) := by
 have common (u) (hu : u∈Icc lo hi) : ∀ i,0 < (p.state u).common i := by
   intro i; rw [←commonGate_state]; exact hc u hu i
 have facts (u) (hu : u∈Icc lo hi) : CommonFacts (p.state u) :=
   common_facts (p.state u) heps hcap (common u hu)
 have cert (u) (hu : u∈Icc lo hi) :
   RayCrossing (p.state u).B (p.state u).L (p.state u).s (p.state u).n (p.state u).r := by
   apply ray_crossing (p.state u) heps hcap (common u hu)
   intro i; rw [←combinedGate_state]; exact hr u hu i
 have cq : Continuous (fun u => (p.state u).q) := by dsimp [RealParams.state]; fun_prop
 have cy : Continuous (fun u => (p.state u).y) := by dsimp [RealParams.state]; fun_prop
 have ck : Continuous (fun u => (p.state u).k) := by dsimp [RealParams.state]; fun_prop
 have ca : Continuous (fun u => (p.state u).a) := by dsimp [RealParams.state]; fun_prop
 have cS : Continuous (fun u => (p.state u).S) := by dsimp [State.S]; fun_prop
 have cD : Continuous (fun u => (p.state u).D) := by dsimp [State.D]; fun_prop
 apply combined_curve_source (floor:=(50001/100000:ℝ)) hab
   (fun u => (p.state u).B) (fun u => (p.state u).L)
   (fun u => (p.state u).S/(6*(p.state u).q^2*(p.state u).y^2))
   (fun u => (p.state u).k/(p.state u).y^2)
   (fun u => (p.state u).s) (fun u => (p.state u).n) (fun u => (p.state u).r)
 · intro u hu; exact B_derivative p u (facts u hu).q_pos.ne' (facts u hu).y_pos.ne'
 · intro u hu; exact L_derivative p u (facts u hu).y_pos.ne'
 · intro u hu
   have hk := common u hu 4
   norm_num [State.common] at hk
   exact div_pos hk (sq_pos_of_pos (facts u hu).y_pos)
 · exact cS.continuousOn.div cD.continuousOn (fun u hu => (facts u hu).D_pos.ne')
 · dsimp [State.n]; fun_prop
 · exact ca.continuousOn.div cq.continuousOn (fun u hu => (facts u hu).q_pos.ne')
 · intro u hu
   have hk := common u hu 4
   norm_num [State.common] at hk
   exact SourceCurveCoordinates.tangent_ratio (facts u hu).q_pos.ne' (facts u hu).y_pos.ne' hk.ne'
 · exact cert
 · intro u hu; exact (facts u hu).B_min
 · intro u hu; exact (facts u hu).B_max
 · intro u hu; exact (facts u hu).C_nonneg
 · intro u hu; exact (facts u hu).low_gap
 · exact le_rfl
 · intro u hu
   have hh := hr u hu 0
   rw [combinedGate_state] at hh
   norm_num [State.combined] at hh
   exact hh.le
 · intro u hu; exact (facts u hu).gates
 · exact hβ
 · exact seed

/-- Pure repeated-count analogue, with the same exact cubic coordinates. -/
theorem pure_source (p : RealParams) {lo hi : ℝ} (hab : lo ≤ hi)
 (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (hc : ∀ u∈Icc lo hi, ∀ i, 0 < commonGate p i u)
 (hr : ∀ u∈Icc lo hi, ∀ i, 0 < pureGate p i u)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource (p.state hi).B (p.state hi).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource (p.state lo).B (p.state lo).L (1/10) := by
 have common (u) (hu : u∈Icc lo hi) : ∀ i,0 < (p.state u).common i := by
   intro i; rw [←commonGate_state]; exact hc u hu i
 have facts (u) (hu : u∈Icc lo hi) : CommonFacts (p.state u) :=
   common_facts (p.state u) heps hcap (common u hu)
 have cert (u) (hu : u∈Icc lo hi) :
   PureCrossing (p.state u).B (p.state u).L (p.state u).s (p.state u).n := by
   apply pure_crossing (p.state u) heps hcap (common u hu)
   intro i; rw [←pureGate_state]; exact hr u hu i
 have cq : Continuous (fun u => (p.state u).q) := by dsimp [RealParams.state]; fun_prop
 have cy : Continuous (fun u => (p.state u).y) := by dsimp [RealParams.state]; fun_prop
 have ck : Continuous (fun u => (p.state u).k) := by dsimp [RealParams.state]; fun_prop
 have ca : Continuous (fun u => (p.state u).a) := by dsimp [RealParams.state]; fun_prop
 have cS : Continuous (fun u => (p.state u).S) := by dsimp [State.S]; fun_prop
 have cD : Continuous (fun u => (p.state u).D) := by dsimp [State.D]; fun_prop
 apply pure_curve_source (floor:=(2/5:ℝ)) hab
   (fun u => (p.state u).B) (fun u => (p.state u).L)
   (fun u => (p.state u).S/(6*(p.state u).q^2*(p.state u).y^2))
   (fun u => (p.state u).k/(p.state u).y^2)
   (fun u => (p.state u).s) (fun u => (p.state u).n)
 · intro u hu; exact B_derivative p u (facts u hu).q_pos.ne' (facts u hu).y_pos.ne'
 · intro u hu; exact L_derivative p u (facts u hu).y_pos.ne'
 · intro u hu
   have hk := common u hu 4
   norm_num [State.common] at hk
   exact div_pos hk (sq_pos_of_pos (facts u hu).y_pos)
 · exact cS.continuousOn.div cD.continuousOn (fun u hu => (facts u hu).D_pos.ne')
 · dsimp [State.n]; fun_prop
 · intro u hu
   have hk := common u hu 4
   norm_num [State.common] at hk
   exact SourceCurveCoordinates.tangent_ratio (facts u hu).q_pos.ne' (facts u hu).y_pos.ne' hk.ne'
 · exact cert
 · intro u hu; exact (facts u hu).B_min
 · intro u hu; exact (facts u hu).B_max
 · intro u hu; exact (facts u hu).C_nonneg
 · intro u hu; exact (facts u hu).low_gap
 · exact le_rfl
 · intro u hu
   have hh := common u hu 0
   norm_num [State.common] at hh
   exact hh.le
 · intro u hu; exact (facts u hu).gates
 · exact hβ
 · exact seed

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveInteger
