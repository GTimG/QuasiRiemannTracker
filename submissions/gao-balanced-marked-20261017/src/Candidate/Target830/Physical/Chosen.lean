/- Fresh fixed source data, before all moving rows/heights. Apache-2.0. -/
import Candidate.Target830.Physical.FinalHeight
import Candidate.Target830.Physical.TransportParameters
import Candidate.Target836.Target836Unconditional

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.Target830.Physical OAI.SevenEighths.Target830.Physical.Assembly

theorem baseline_beta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  Target836.FinalAssembly.baseline_beta

theorem moment_parameter_gates (hβ : theta< HeckeZeroSupremum.beta) :
    (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 ∧
    2*HeckeZeroSupremum.beta-1≤ kappa0 ∧ (51/100:ℝ)≤ HeckeZeroSupremum.beta := by
  have hi := Target836.FinalAssembly.beta_le_rational
  norm_num [kappa0] at ⊢
  have ht : (85/100:ℝ)< theta := by norm_num [theta]
  constructor
  · linarith
  constructor <;> linarith

structure ChosenData where
  D : BaselineData
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
    (mesh : ℝ→ℝ) (hmesh : ∀t : ℝ,0< t→0< mesh t) :
    ∃A : ChosenData,A.sourceMesh=mesh A.D.t := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
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
  refine ⟨⟨D,hκ,?_,hbudget,hfine,hdet,mesh D.t,hmesh D.t D.t_pos,hextra,P,F,counts⟩,rfl⟩
  rw [hκ]
  exact hk1
end
end OAI.SevenEighths.Target830.Physical.FinalAssembly
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.exists_chosen_data_with_mesh
