/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.PhysicalDirect.Finite.Summation
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.PhysicalDirect.SourceFullW
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Schedule
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.GenericScalar

set_option autoImplicit false
namespace QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.FiniteNumerator
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.LewkoStage2Return.Geometry.Parameters] [QRH.LewkoStage2Return.Geometry.Bounds]
variable [scheme : QRH.LewkoStage2Return.CountScheme] [QRH.LewkoStage2Return.GenericArithmetic.PhysicalSchedule]
open QRH.LewkoStage2Return.GenericArithmetic QRH.LewkoStage2Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.LewkoStage2Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect QRH.LewkoStage2Return.GenericPhysical.FinalAssembly LewkoStage2Return.TransportHighTransport
open QRH.LewkoStage2Return.GenericPhysical.Assembly Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : QRH.LewkoStage2Return.GenericArithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ActualFullWCellInput A J := by
  obtain ⟨J,hJ,hcells⟩:=Source.actual_fullW_cells hgap A hAffine
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨C,hC,hcells⟩:=hcells τ hheight n η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcells,actual_cell_geometry A η τ n] with Z hc hg
  intro C0 hC0 hmom idx grid hsel k hk i hi j hj hne
  have hf:=hg idx grid hsel k i j hne
  have hrow : ∀u∈cellRows A.D A.F Z idx grid k i j,
      (rowCharacter A.F.S A.F.exclusions.prime u).residue≠1 := by
    intro u hu
    exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
      u (hf.source_rows u hu).1 (hf.source_rows u hu).2.2.1
  have hb:=hc C0 hC0 hmom (cellRows A.D A.F Z idx grid k i j)
    (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i hf.d_lower hf.d_upper hf.a_lower hf.a_upper
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hf.source_rows hf.moment_rows hrow
    hf.frequency_lower hf.next_maximum hf.current_maximum
  convert hb using 1 <;> rfl
end
end QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.FiniteNumerator

#print axioms QRH.LewkoStage2Return.GenericPhysical.PhysicalDirect.FiniteNumerator.actual_cells_of_affine
