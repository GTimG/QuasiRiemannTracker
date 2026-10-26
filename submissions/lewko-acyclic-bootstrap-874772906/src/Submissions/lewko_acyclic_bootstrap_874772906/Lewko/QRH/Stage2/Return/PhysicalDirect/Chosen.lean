/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Chosen physical/count data at the new geometry. Apache-2.0.
The established incumbent beta cap remains an explicit input until Bootstrap integration. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.PhysicalDirect.MomentGates
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Transport.FinalHeight
set_option autoImplicit false
open QRH.LewkoStage2Return

namespace QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
noncomputable section
set_option maxHeartbeats 200000
open scoped Classical BigOperators ContDiff
open QRH.LewkoStage2Return.GenericArithmetic OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count
open QRH.LewkoStage2Return.GenericCount
open QRH.LewkoStage2Return.GenericPhysical (baselineSource)
open QRH.LewkoStage2Return.GenericPhysical.Assembly

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  kappa_incumbent : D.momentKappa≤scheme.naturalκ
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  sourceMesh : ℝ
  sourceMesh_pos : 0<sourceMesh
  source_fine : ∀j,D.length j≤sourceMesh/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : CountParameters (baselineSource D F).modulus ⊤ D.t

theorem fresh_count_parameters (D : BaselineData)
    (F : QRH.LewkoStage2Return.GenericPhysical.SourceData) :
    Nonempty (CountParameters F.modulus ⊤ D.t) :=
  exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun y=>(F.bounded y).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2) D.t D.t_pos

theorem exists_chosen_data_with_mesh (hgap : theta<HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤scheme.naturalκ)
    (mesh : ℝ→ℝ) (hmesh : ∀t : ℝ,0<t→0<mesh t) :
    ∃A : ChosenData,A.sourceMesh=mesh A.D.t := by
  have hk : (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 := by
    have ht : (85/100:ℝ)<theta := by linarith [Geometry.Bounds.theta_bounds.1]
    linarith
  have hkhi : 2*HeckeZeroSupremum.beta-1≤3/4 :=
    hκbeta.trans scheme.natural_hi
  obtain ⟨D,hκ,hbudget,hfine,_hcommon,hextra,⟨P⟩⟩ :=
    exists_compatible_data_with_mesh hk hkhi
      (show 0<(HeckeZeroSupremum.beta-theta)/10000 by positivity) mesh hmesh
  obtain ⟨F⟩ := QRH.LewkoStage2Return.GenericPhysical.exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D (baselineSource D F)
  exact ⟨⟨D,hκ,hκ.symm ▸ hκbeta,hbudget,hfine,mesh D.t,hmesh D.t D.t_pos,hextra,P,F,counts⟩,rfl⟩
end
end QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect
#print axioms QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.fresh_count_parameters
#print axioms QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.exists_chosen_data_with_mesh
