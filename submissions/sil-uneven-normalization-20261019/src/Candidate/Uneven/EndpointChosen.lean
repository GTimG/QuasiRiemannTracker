/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Fresh fixed source data, before all moving rows/heights. Apache-2.0. -/
import Candidate.Uneven.EndpointFinalHeight
import Candidate.Uneven.EndpointTransportParameters
import Candidate.Target836.Target836Unconditional

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
variable [config : Configuration]
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.UnevenEndpoint.Physical OAI.SevenEighths.UnevenEndpoint.Physical.Assembly

theorem baseline_beta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  Target836.FinalAssembly.baseline_beta

theorem moment_parameter_gates (hβ : theta< HeckeZeroSupremum.beta)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1≤ kappa0 ∧ (51/100:ℝ)≤ HeckeZeroSupremum.beta := by
  have htheta := parameter_gates.1
  have hkhi : 2*incumbent-1 ≤ kappa0 := parameter_gates.2.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · linarith only [htheta,hβ]
  constructor <;> linarith only [hinc,hkhi,htheta,hβ]

structure ChosenData where
  D : BaselineData
  beta_incumbent : HeckeZeroSupremum.beta ≤ incumbent
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  kappa_incumbent : D.momentKappa≤ kappa0
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-theta)/10000
  fine : ∀j,D.length j≤ Cycle25.sourceMesh D.t/200
  detector_fine : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200
  sourceMesh : ℝ
  sourceMesh_pos : 0< sourceMesh
  source_fine : ∀j,D.length j≤ sourceMesh/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : DetectorCount.CountParameters (baselineSource D F).modulus ⊤ D.t

/-- The source-mesh function is fixed before the fresh slots and source profiles. -/
theorem exists_chosen_data_with_mesh (hβ : theta< HeckeZeroSupremum.beta)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (mesh : ℝ→ℝ) (hmesh : ∀t : ℝ,0< t→0< mesh t) :
    ∃A : ChosenData,A.sourceMesh=mesh A.D.t := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ hinc
  have hk75 : 2*HeckeZeroSupremum.beta-1≤3/4 := by
    have hh : kappa0≤(3/4:ℝ) := by norm_num [kappa0]
    exact hk1.trans hh
  obtain ⟨D,hκ,hbudget,hfine,hcommon,hextra,⟨P⟩⟩ :=
    exists_compatible_data_with_mesh hk hk75
      (show 0<(HeckeZeroSupremum.beta-theta)/10000 by positivity) mesh hmesh
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := DetectorCount.fresh_count_parameters D.toDetectorData (baselineSource D F)
  have hdet : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  refine ⟨⟨D,hinc,hκ,?_,hbudget,hfine,hdet,mesh D.t,hmesh D.t D.t_pos,hextra,P,F,counts⟩,rfl⟩
  rw [hκ]
  exact hk1
end
end OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
