/- REVIEW STATUS: The incumbent supplier below is replaced by the ORIGINAL, separate Sil endpoint; historical C30 descriptions no longer describe this supplier. -/
/- Copyright (c) 2026 Sil, Hailey Collet and predecessors. Apache-2.0.
Intermediate nonvanishing bound from the established prior and the
ordinary source. Uses PR69 chosen-source, physical-numerator, and Mellin
estimates to derive beta <= 0.8747759 from these inputs.
-/
import Candidate.SilPrior.FourthPower.RepairedUnconditionalEndpoint
import Candidate.Feedback.FourthPower.ReturnSourceFaces
import Submissions.hailey_collet_1252270103.Record1252270103Return.IntermediateCount.Schedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.PhysicalDirect.ChosenSource
import Candidate.Feedback.FourthPower.OlderIncumbentContract

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Candidate.Feedback.FourthPower.ReturnIntermediateBound
noncomputable section
open OAI.SevenEighths QRH.Record12518109Existence
open QRH.Record1252270103Return ReturnSourceFaces OlderIncumbentContract

local instance : Geometry.Parameters := Geometry.intermediateParameters
local instance : Geometry.Bounds := Geometry.intermediateBounds
local instance : CountScheme := IntermediateCount.countScheme
local instance : GenericArithmetic.PhysicalSchedule := IntermediateCount.physicalSchedule

/-- The established prior bound supplies the natural cost used in the
intermediate return. -/
theorem older_natural_cap (hPrior : OlderIncumbentInput) :
    2*HeckeZeroSupremum.beta-1 ≤ Record1252270103Return.C30.naturalK/6 := by
  have hi := OlderIncumbentContract.natural_cost hPrior
  norm_num [Record1252270103Return.C30.naturalK]
  linarith

/-- Definitional identification with the actual C30 global source interfaces.
In particular the intermediate cap is 54998999999/10^12 on both faces. -/
theorem intermediate_suppliers_from_full_source
    (hsource : UniformUnitFaceSource fullSourceFace) :
    UniformUnitFaceSource IntermediateCount.countGlobal ∧
      UniformUnitFaceSource IntermediateCount.physicalGlobal := by
  obtain ⟨hC,hP⟩ := intermediate_sources_of_full_source hsource
  exact ⟨hC,hP⟩

/-- Actual label moments and physical initial energy on one chosen mesh.
Copied intermediate assembly, with the two suppliers discharged by our source.
No arbitrary count, numerator, physical-energy or common-probe premise appears. -/
theorem initial_source_from_full_source (hPrior : OlderIncumbentInput)
    (hsource : UniformUnitFaceSource fullSourceFace) :
    GenericPhysical.PhysicalDirect.ChosenInitialSourceInput := by
  obtain ⟨hC,hP⟩ := intermediate_suppliers_from_full_source hsource
  have hc : ∀ ε : ℝ, 0<ε → ∃ mesh : ℝ, 0 < mesh ∧
      ∀ w∈IntermediateCount.countScheme.windows, UnitFaceSource w.face mesh ε := by
    intro ε hε
    obtain ⟨mesh,hm,_,hw⟩ := IntermediateCount.windows_common_mesh hC hP hε
    exact ⟨mesh,hm,hw⟩
  have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
    change UniformUnitFaceSource IntermediateCount.physicalWindow
    intro ε hε
    obtain ⟨mesh,hm,hs⟩ := hP ε hε
    exact ⟨mesh,hm,unit_source_restrict IntermediateCount.physical_restricts hs⟩
  exact GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces
    (older_natural_cap hPrior) hc hp

/-- Acyclic feedback: the ORIGINAL Sil endpoint is used as a proved prior.
The source and prior parameters are retained for compatibility with the caller. -/
theorem incumbent_from_full_source (_hPrior : OlderIncumbentInput)
    (_hsource : UniformUnitFaceSource fullSourceFace) :
    HeckeZeroSupremum.beta ≤ incumbent := by
  have hi := Candidate.SilPrior.FourthPower.RepairedUnconditionalEndpoint.actual_beta_bound
  simpa only [Candidate.SilPrior.FourthPower.theta, incumbent] using hi

end
end Candidate.Feedback.FourthPower.ReturnIntermediateBound
