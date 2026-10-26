/- Repeated marks: fork of Collet's generic return module PhysicalDirect.NormalizerHelpers (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual physical numerator source/normalizer closure, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Schedule
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.Helpers
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Normalizer
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect QRH.Record1252270103Return.GenericPhysical
open OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      RepeatedMarksReturn.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(RepeatedMarksReturn.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Record1252270103LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)


end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.Source
