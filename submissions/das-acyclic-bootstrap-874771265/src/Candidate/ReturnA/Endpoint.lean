/- Subhanjan Das; MIT for new endpoint assembly; AI-assisted with OpenAI Codex.
Analytic finite-numerator and common-probe theorems: Hailey Collet, within the
admitted Mark Lewko dependency, retaining original Apache-2.0 notices. -/
import Candidate.ReturnA.FinalSchedule
import Candidate.ReturnA.FinalScheme
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.PhysicalDirect.ChosenSource
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.Transport.FinalCommonProbe
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.ReturnA
noncomputable section
open QRH.LewkoStage2Return
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths
local instance : Geometry.Parameters := parameters
local instance : Geometry.Bounds := bounds
local instance : CountScheme := finalCountScheme
local instance : GenericArithmetic.PhysicalSchedule := finalPhysicalSchedule

theorem literal_numerator_of_global_sources
 (hC : UniformUnitFaceSource countGlobal) (hP : UniformUnitFaceSource physicalGlobal)
 (hcap : 2*HeckeZeroSupremum.beta-1 ≤ DasStageAFinite.naturalK/6) :
 GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput := by
 have hc : ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
   ∀ w ∈ finalCountScheme.windows, UnitFaceSource w.face mesh ε := by
  intro ε hε
  obtain ⟨mesh,hm,_,hw⟩ := final_windows_common_mesh hC hP hε
  exact ⟨mesh,hm,hw⟩
 have hr : physicalWindow.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalWindow.Restricts
    ⟨DasStageAFinite.physicalB,DasStageAFinite.physicalLambda,2/5,11/25,17/500,1/25⟩
  constructor <;> norm_num [physicalWindow]
 have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hP ε hε
  exact ⟨mesh,hm,unit_source_restrict hr (unit_source_restrict physical_restricts hs)⟩
 exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
  (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc hp)

theorem beta_of_global_sources
 (hC : UniformUnitFaceSource countGlobal) (hP : UniformUnitFaceSource physicalGlobal)
 (hcap : 2*HeckeZeroSupremum.beta-1 ≤ DasStageAFinite.naturalK/6) :
 HeckeZeroSupremum.beta ≤ DasStageAFinite.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator
  (literal_numerator_of_global_sources hC hP hcap)
end
end Das.QRH.ReturnA
#print axioms Das.QRH.ReturnA.beta_of_global_sources
