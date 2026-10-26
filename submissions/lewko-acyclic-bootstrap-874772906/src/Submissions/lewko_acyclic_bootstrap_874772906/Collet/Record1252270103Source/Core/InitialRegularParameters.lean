/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularMesh
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalReserve
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularLowPointData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.InitialRegularToTruncated
noncomputable section
open Record1252270103Finite Record1252270103StepScalar QRH.Record1252270103Graph
open PhysicalAnalytic PhysicalScalar High.GlobalPhysical

theorem actual_gaps_mono {n low:Source}{high:Option Source}{b ν σ reserve:ℝ}
    (hσ:σ≤reserve)(h:ActualGaps n low high b ν reserve) : ActualGaps n low high b ν σ :=
  ⟨hσ.trans h.1,fun j=>hσ.trans (h.2 j)⟩

theorem scalar_of_regular_mesh (K:ℚ)(n low:Source)(b σ θ mesh ξ width:ℝ)
    (hg:RealGeometry K n low b)(hn:ParentGood n)(hlow:ParentGood low)
    (ha:0<(n.allowance:ℝ))(hf:FixedBudget σ 100 100 1 θ)
    (hσ:σ≤(n.allowance:ℝ))(hθ:θ≤PhysicalLowGuard.step n)
    (hx:0<ξ)(hxθ:ξ≤θ)(hm:0≤mesh)(hmn:mesh≤(n.allowance:ℝ)/4)
    (hw:0≤width)(hwθ:width≤θ) :
    Admission.SelectedRegularLowPoint.Scalar K n low b θ mesh ξ width := by
  refine ⟨hg,hn,hlow,ha,hf.positive,?_,hθ,hx,hxθ,hm,hmn,hw,hwθ.trans hθ⟩
  linarith only [hf.tiny,hf.positive,hσ]
end
end QRH.Record1252270103Source.InitialRegularToTruncated
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.actual_gaps_mono
#print axioms QRH.Record1252270103Source.InitialRegularToTruncated.scalar_of_regular_mesh
