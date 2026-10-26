import Candidate.Target830.Source.Assembly.SourceMesh
import Candidate.Target830.Physical.Chosen
import Candidate.Target830.Source.Assembly.InitialSupplier
import Candidate.Target830.Physical.Finite.Bridge
import Candidate.Cycle25.Assembly.Continuation
import Candidate.Target830.Source.RecordPrincipal
import Candidate.Target830.Physical.AffineFamily

/- Original module: Candidate.Target830.Source.RecordMesh. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.RecordEndpoint
noncomputable section
/-- This single positive mesh is fixed before choosing the detector, slots,
profiles or finite dictionary. It serves both source uses of the same data. -/
def commonSourceMesh (ε t : ℝ) : ℝ :=
  min (Assembly.sourceMesh t) (Assembly.sourceMesh ε)

theorem common_source_mesh_pos {ε t : ℝ} (hε : 0<ε) (ht : 0< t) :
    0< commonSourceMesh ε t :=
  lt_min (Assembly.source_mesh_pos ht) (Assembly.source_mesh_pos hε)

end
end OAI.SevenEighths.Target830.Source.RecordEndpoint
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.common_source_mesh_pos
end

/- Original module: Candidate.Target830.Source.Assembly.Public. -/
section

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open HeckeFamily Cycle25ProbeFinalAssembly

/-- The actual original batch/fiber moment for each new plane, from the
complete source theorem and its common pre-dictionary source mesh. -/
theorem actual_detector_affine_input (plane : SourcePlane)
    {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (mesh : ℝ) (hmesh0 : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t)
    (hfine : ∀j,D.ell j ≤ mesh/200) :
    Physical.InitialTransport.weighted_AffineFineInputAt
      (Physical.InitialTransport.countPlane plane) S := by
  exact Physical.InitialTransport.actual_detector_affine_input_of_initial plane S mesh hmesh0 hfine
    (actual_label_initial_moments plane S hβlo hβhi mesh hmesh0 hmesh)
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.actual_detector_affine_input
end

/- Original module: Candidate.Target830.Physical.FinalCommonProbe. -/
section
/- Final actual physical probe consumer; new A/C analytic estimates remain explicit.
Original OpenAI/Hailey Collet/DaysSky attribution retained; Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Physical.FinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.Target830.Physical OAI.SevenEighths.Target830.Physical.Assembly

/-- Genuine source moments for one fixed fresh geometry. This contract is
proved by the source assembly, not by the numerical row certificate. -/
def ChosenSourceInput : Prop :=
  theta< HeckeZeroSupremum.beta → ∃A : ChosenData,
    (∀P : Count.Plane,InitialTransport.weighted_AffineFineInputAt P A.F) ∧
    Source.ActualAffineInput A

/-- All finite numerator cells, original masks, profiles, dyadic bands,
principal replacement and infinite tails feed the SAME common probe. -/
theorem common_probe_of_chosen_source (hinput : ChosenSourceInput) :
    Cycle25.UniformCommonProbe theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,hfields,hAffine⟩ := hinput hβ
  obtain ⟨J,hJ,hfinite⟩ := FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 A.kappa_exact.ge A.fine
    hfields J hJ
  let loss := (HeckeZeroSupremum.beta-theta)/2
  have hloss : 0< loss := by dsimp [loss]; linarith
  have hgap : loss< HeckeZeroSupremum.beta-theta := by dsimp [loss]; linarith
  refine ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,?_⟩
  apply fixed_source_contract A.D A.F loss A.P.sigma hloss
  intro η
  obtain ⟨τ,hheight,hcount⟩ := hjoint η
  exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
    (hfinite τ hheight η hcount)

theorem beta_le_theta_of_chosen_source (hinput : ChosenSourceInput) :
    HeckeZeroSupremum.beta≤ theta := by
  exact Cycle25.beta_le_of_common_probe
    (show (1/2:ℝ)≤ theta by norm_num [theta])
    (show theta≤(7/8:ℝ) by norm_num [theta])
    (common_probe_of_chosen_source hinput)
end
end OAI.SevenEighths.Target830.Physical.FinalAssembly
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.common_probe_of_chosen_source
#print axioms OAI.SevenEighths.Target830.Physical.FinalAssembly.beta_le_theta_of_chosen_source
end

/- Original module: Candidate.Target830.Source.RecordEndpoint. -/
section
/- The .874830 endpoint from the actual source and physical count graph.
Predecessor OpenAI, Hailey Collet, DaysSky and Zhongpai Gao attribution is
retained. Apache-2.0. -/

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
    (fun _ ht=> common_source_mesh_pos hε ht)
  have hmD : A.sourceMesh≤ Assembly.sourceMesh A.D.t := by
    rw [hA]
    exact min_le_left _ _
  have hmε : A.sourceMesh≤ Assembly.sourceMesh ε := by
    rw [hA]
    exact min_le_right _ _
  have hβlo := (moment_parameter_gates hβ).2.2
  have hlabels : ∀P : SourcePlane,
      Physical.InitialTransport.LabelInitialMoments P A.F A.sourceMesh :=
    fun P=> Assembly.actual_label_initial_moments P A.F hβlo baseline_beta
      A.sourceMesh A.sourceMesh_pos hmD
  have hfields := Physical.InitialTransport.actual_five_plane_fields A.F
    hβlo baseline_beta A.detector_fine A.sourceMesh A.sourceMesh_pos A.source_fine hlabels
  obtain ⟨b,_hb,hsupport⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bΦ : ℝ := max 2 b
  have hbΦ : 2≤ bΦ := le_max_left _ _
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  obtain ⟨degree,control,C,hC,hsource⟩ :=
    Assembly.detector_label_initial_affine .A A.F η (Sum.inl true)
      hβlo baseline_beta ε hε A.sourceMesh A.sourceMesh_pos hmε bΦ hbΦ
  refine ⟨A,hfields,bΦ,ε,hε,le_rfl,?_,degree,control,C,hC,?_⟩
  · intro x hx
    exact (show x≤ b from hsupport hx).trans (le_max_right _ _)
  · simpa only [Physical.AffineAt,principal_detector_label] using hsource

/-- The unconditional new record follows through the actual common probe. -/
theorem beta_le_theta : HeckeZeroSupremum.beta≤ theta :=
  Physical.FinalAssembly.beta_le_theta_of_chosen_source actual_chosen_source_input

theorem beta_le_rational : HeckeZeroSupremum.beta≤(87483/100000:ℝ) :=
  beta_le_theta

end
end OAI.SevenEighths.Target830.Source.RecordEndpoint
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.actual_chosen_source_input
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.beta_le_theta
#print axioms OAI.SevenEighths.Target830.Source.RecordEndpoint.beta_le_rational
end
