/- The .874830 endpoint from the actual source and physical count graph.
Predecessor OpenAI, Hailey Collet, DaysSky and Zhongpai Gao attribution is
retained. Apache-2.0. -/
import Candidate.Target830.Source.RecordMesh
import Candidate.Target830.Source.RecordPrincipal
import Candidate.Target830.Source.Assembly.Public
import Candidate.Target830.Physical.FinalCommonProbe
import Candidate.Target830.Physical.AffineFamily

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Target830.Source.RecordEndpoint
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.Target830.Physical
open OAI.SevenEighths.Target830.Physical.FinalAssembly
open ProbePhysical CenteredMomentDetectorDictionary

/-- All five affine fields and the physical reflected numerator use the
same freshly chosen data. Both new source fields are genuine theorems. -/
theorem actual_chosen_source_input : Physical.FinalAssembly.ChosenSourceInput := by
  intro hβ
  let ε : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hε : 0<ε := by dsimp only [ε]; positivity
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hβ (commonSourceMesh ε)
    (fun _ ht=>common_source_mesh_pos hε ht)
  have hmD : A.sourceMesh≤Assembly.sourceMesh A.D.t := by
    rw [hA]
    exact min_le_left _ _
  have hmε : A.sourceMesh≤Assembly.sourceMesh ε := by
    rw [hA]
    exact min_le_right _ _
  have hβlo := (moment_parameter_gates hβ).2.2
  have hlabels : ∀P : SourcePlane,
      Physical.InitialTransport.LabelInitialMoments P A.F A.sourceMesh :=
    fun P=>Assembly.actual_label_initial_moments P A.F hβlo baseline_beta
      A.sourceMesh A.sourceMesh_pos hmD
  have hfields := Physical.InitialTransport.actual_five_plane_fields A.F
    hβlo baseline_beta A.detector_fine A.sourceMesh A.sourceMesh_pos A.source_fine hlabels
  obtain ⟨b,_hb,hsupport⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bΦ : ℝ := max 2 b
  have hbΦ : 2≤bΦ := le_max_left _ _
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  obtain ⟨degree,control,C,hC,hsource⟩ :=
    Assembly.detector_label_initial_affine .A A.F η (Sum.inl true)
      hβlo baseline_beta ε hε A.sourceMesh A.sourceMesh_pos hmε bΦ hbΦ
  refine ⟨A,hfields,bΦ,ε,hε,le_rfl,?_,degree,control,C,hC,?_⟩
  · intro x hx
    exact (show x≤b from hsupport hx).trans (le_max_right _ _)
  · simpa only [Physical.AffineAt,principal_detector_label] using hsource

/-- The unconditional new record follows through the actual common probe. -/
theorem beta_le_theta : HeckeZeroSupremum.beta≤theta :=
  Physical.FinalAssembly.beta_le_theta_of_chosen_source actual_chosen_source_input

theorem beta_le_rational : HeckeZeroSupremum.beta≤(87483/100000:ℝ) :=
  beta_le_theta

end
end OAI.SevenEighths.Target830.Source.RecordEndpoint
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.actual_chosen_source_input
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.beta_le_theta
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.beta_le_rational
