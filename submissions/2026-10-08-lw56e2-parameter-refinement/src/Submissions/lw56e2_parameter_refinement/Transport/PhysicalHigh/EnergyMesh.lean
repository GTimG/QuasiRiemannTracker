/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/EnergyMesh.lean
Original SHA-256: d96c577d8423fbbed6f6233906b8670fb08147fb696c70d924fc6efb713dcf0e
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.WidthRanges

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open OAI OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

def plainMesh (εm:ℝ):ℝ:=fineMesh 2 0 1 (3/4) (εm/4)

lemma plainMesh_pos {εm:ℝ}(hεm:0<εm):0<plainMesh εm:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (εm/4)) (3/4) (εm/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)).2.2.2.2.1

end
end LW56e2.Transport.PhysicalHigh
