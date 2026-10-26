/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Actual physical numerator source/normalizer closure, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.PhysicalDirect.Helpers
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Transport.Normalizer
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Source
variable [Geometry.Parameters] [Geometry.Bounds] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect QRH.LewkoStage1Return.GenericPhysical
open OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      LewkoStage1Return.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(LewkoStage1Return.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact LewkoStage1LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)


end QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Source
#print axioms QRH.LewkoStage1Return.GenericPhysical.PhysicalDirect.Source.source_normalizer_bound
