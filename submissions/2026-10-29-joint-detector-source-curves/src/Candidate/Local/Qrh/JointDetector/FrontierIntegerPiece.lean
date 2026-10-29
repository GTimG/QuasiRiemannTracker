/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveIntegerState
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveFunctionTransfer
import Candidate.Local.Qrh.JointDetector.FrontierCertificateSemantic

namespace Qrh.JointDetector.FrontierIntegerPiece
noncomputable section
set_option autoImplicit false
open Set RepeatedMarks SourceCurveInteger SourceCurveCertificate

/-- The cubic backend is merely one degree-independent function path. -/
def path (p : RealParams) : SourceCurveFunctionCoordinates.Path :=
 ⟨p.q0,fun u => (p.state u).y,fun u => (p.state u).k,
   fun u => (p.state u).a,p.eps,p.cap⟩

theorem path_state (p : RealParams) (u : ℝ) : (path p).state u=p.state u := rfl

private theorem y_derivative (p : RealParams) (u : ℝ) :
 HasDerivAt (fun x => (p.state x).y) (-(p.state u).k) u := by
 convert (((hasDerivAt_const u p.y0).add ((hasDerivAt_id u).const_mul p.y1)).add
   (((hasDerivAt_id u).pow 2).const_mul p.y2)).add
   (((hasDerivAt_id u).pow 3).const_mul p.y3) using 1 <;>
   (try funext x) <;> simp [RealParams.state,Pi.add_apply] <;> ring

/-- The smaller fixed cutoff changes only one scalar gate. -/
theorem combined_source (p : RealParams) {lo hi : ℝ} (hab : lo ≤ hi)
 (heps : 0 < p.eps) (hcap : p.cap=1/10)
 (hc : ∀ u∈Icc lo hi, ∀ i, 0 < commonGate p i u)
 (hr : ∀ u∈Icc lo hi, ∀ i, 0 < FrontierSourceCurveCertificate.combined (p.state u) i)
 (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
 (seed : QRH.Record1252270103Source.GlobalSource (p.state hi).B (p.state hi).L (1/10)) :
 QRH.Record1252270103Source.GlobalSource (p.state lo).B (p.state lo).L (1/10) := by
 have common (u) (hu : u∈Icc lo hi) : ∀ i,0 < (p.state u).common i := by
   intro i; rw [←commonGate_state]; exact hc u hu i
 have facts (u) (hu : u∈Icc lo hi) : CommonFacts (p.state u) :=
   common_facts (p.state u) heps hcap (common u hu)
 have hd : SourceCurveFunctionCoordinates.Data (path p) lo hi := by
   apply SourceCurveFunctionCoordinates.coordinate_data
   · intro u hu; exact y_derivative p u
   · dsimp [path,RealParams.state]; fun_prop
   · dsimp [path,RealParams.state]; fun_prop
   · exact facts
   · intro u hu
     have hh := common u hu 4
     simpa [State.common,path] using hh
 apply SourceCurveFunctionCoordinates.frontier_source (path p) hab hd facts
   (floor:=(50001/100000:ℝ))
 · intro u hu
   exact FrontierSourceCurveCertificate.ray_crossing (p.state u) heps hcap (common u hu) (hr u hu)
 · exact le_rfl
 · intro u hu
   have hh := hr u hu 0
   norm_num [FrontierSourceCurveCertificate.combined,State.combined] at hh
   exact hh.le
 · exact hβ
 · exact seed
end
end Qrh.JointDetector.FrontierIntegerPiece
