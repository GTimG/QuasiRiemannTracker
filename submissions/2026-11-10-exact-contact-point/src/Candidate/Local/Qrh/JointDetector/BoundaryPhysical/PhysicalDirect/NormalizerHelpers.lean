import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.Helpers
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Transport.Normalizer
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.Record12518109Count
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect QRH.Record1252270103Return.GenericPhysical
open OAI.SevenEighths Cycle25ProbeFinalAssembly HeckeFamily ProbeHighRowFamily ProbePhysical
open PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      BoundaryDensitySplitReturn.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(BoundaryDensitySplitReturn.TransportHighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Record1252270103LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)
end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
