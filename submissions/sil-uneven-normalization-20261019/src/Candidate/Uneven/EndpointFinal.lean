import Candidate.Uneven.EndpointStageParameters
import Candidate.Uneven.MainActualLabelMoments
import Candidate.Uneven.MainNinePlaneFields
import Candidate.Target830.Source.Assembly.InitialSupplier
import Candidate.Uneven.EndpointFiniteBridge
import Candidate.Cycle25.Assembly.Continuation
import Candidate.Uneven.EndpointContract
import Candidate.Target830.Source.RecordPrincipal
import Candidate.Target830.Source.RecordEndpoint

/- Original module: Candidate.Uneven.EndpointInitialLabels. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.UnevenEndpoint
noncomputable section
variable [config : Configuration]
open HeckeFamily Cycle25ProbeFinalAssembly

def sourceMesh (ε : ℝ) : ℝ :=
  min (Target830.Source.Assembly.sourceMesh ε) (MainAssembly.sourceMesh ε)

theorem source_mesh_pos {ε : ℝ} (hε : 0 < ε) : 0 < sourceMesh ε :=
  lt_min (Target830.Source.Assembly.source_mesh_pos hε) (MainAssembly.source_mesh_pos hε)

theorem main_source_incumbent (P : SourcePlane)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    2*HeckeZeroSupremum.beta-1 ≤ P.mainPlane.incumbent := by
  rw [SourcePlane.mainPlane_incumbent]
  unfold frozenKappa
  linarith only [hinc]

/-- Each stage uses exactly its two newly proved source estimates. -/
theorem actual_stage_fields {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (hinc : HeckeZeroSupremum.beta ≤ incumbent)
    (hdetector : ∀ j, D.ell j ≤ DetectorAffine.detectorMesh D.t/200)
    (mesh : ℝ) (hm : 0 < mesh) (hmesh : mesh ≤ sourceMesh D.t)
    (hfine : ∀ j, D.ell j ≤ mesh/200) :
    ∀ P : MainCount.Plane, config.stage.Supports P →
      MainInitialTransport.weighted_AffineFineInputAt P S := by
  have hmold : mesh ≤ Target830.Source.Assembly.sourceMesh D.t :=
    hmesh.trans (min_le_left _ _)
  have hmnew : mesh ≤ MainAssembly.sourceMesh D.t := hmesh.trans (min_le_right _ _)
  have holdlabels : ∀ P : Target830.SourcePlane,
      Target830.Physical.InitialTransport.LabelInitialMoments P S mesh :=
    fun P => Target830.Source.Assembly.actual_label_initial_moments P S hβlo hβhi
      mesh hm hmold
  have hold := Target830.Physical.InitialTransport.actual_five_plane_fields S hβlo hβhi
    hdetector mesh hm hfine holdlabels
  have hnew (P : SourcePlane) :
      MainInitialTransport.weighted_AffineFineInputAt
        (MainInitialTransport.countPlane P.mainPlane) S :=
    MainInitialTransport.actual_detector_affine_input_of_initial P.mainPlane S mesh hm hfine
      (MainAssembly.actual_label_initial_moments P.mainPlane S hβlo hβhi
        (main_source_incumbent P hinc) mesh hm hmnew)
  apply MainInitialTransport.stage_plane_fields S config.stage hold
  · have hh := hnew .A
    have he : MainInitialTransport.countPlane SourcePlane.A.mainPlane=config.stage.aPlane := by
      cases config with
      | mk stage => cases stage <;> rfl
    simpa only [he] using hh
  · have hh := hnew .C
    have he : MainInitialTransport.countPlane SourcePlane.C.mainPlane=config.stage.cPlane := by
      cases config with
      | mk stage => cases stage <;> rfl
    simpa only [he] using hh

end
end OAI.SevenEighths.UnevenEndpoint
end

/- Original module: Candidate.Uneven.EndpointFinalCommonProbe. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Final actual physical probe consumer; new A/C analytic estimates remain explicit.
Original OpenAI/Hailey Collet/DaysSky attribution retained; Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open scoped Classical
open Filter HeckeFamily
open OAI.SevenEighths.UnevenEndpoint.Physical OAI.SevenEighths.UnevenEndpoint.Physical.Assembly

/-- Genuine source moments for one fixed fresh geometry. This contract is
proved by the source assembly, not by the numerical row certificate. -/
def ChosenSourceInput : Prop :=
  theta< HeckeZeroSupremum.beta → ∃A : ChosenData,
    (∀P : MainCount.Plane,config.stage.Supports P → MainInitialTransport.weighted_AffineFineInputAt P A.F) ∧
    Source.ActualAffineInput A

/-- All finite numerator cells, original masks, profiles, dyadic bands,
principal replacement and infinite tails feed the SAME common probe. -/
theorem common_probe_of_chosen_source (hinput : ChosenSourceInput) :
    Cycle25.UniformCommonProbe theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,hfields,hAffine⟩ := hinput hβ
  obtain ⟨J,hJ,hfinite⟩ := FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  have hβ51 := (moment_parameter_gates hβ A.beta_incumbent).2.2
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
    (show (1/2:ℝ)≤ theta by have hh := parameter_gates.1; linarith only [hh])
    (show theta≤(7/8:ℝ) from parameter_gates.2.1.le.trans parameter_gates.2.2.1)
    (common_probe_of_chosen_source hinput)
end
end OAI.SevenEighths.UnevenEndpoint.Physical.FinalAssembly
end

/- Original module: Candidate.Uneven.EndpointRecord. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0.
Two-stage endpoint assembly with explicit incumbent bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
noncomputable section
variable [config : Configuration]
open scoped Classical
open Filter HeckeFamily
open Physical Physical.FinalAssembly
open ProbePhysical CenteredMomentDetectorDictionary

def commonSourceMesh (ε t : ℝ) : ℝ :=
  min (UnevenEndpoint.sourceMesh t) (MainAssembly.sourceMesh ε)

theorem common_source_mesh_pos {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    0 < commonSourceMesh ε t :=
  lt_min (UnevenEndpoint.source_mesh_pos ht) (MainAssembly.source_mesh_pos hε)

/-- The explicit incumbent will be discharged first by PR63, then by the warmup. -/
theorem actual_chosen_source_input (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    Physical.FinalAssembly.ChosenSourceInput := by
  intro hβ
  let ε : ℝ := (HeckeZeroSupremum.beta-theta)/10000
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨A,hA⟩ := exists_chosen_data_with_mesh hβ hinc (commonSourceMesh ε)
    (fun _ ht => common_source_mesh_pos hε ht)
  have hmD : A.sourceMesh ≤ UnevenEndpoint.sourceMesh A.D.t := by
    rw [hA]
    exact min_le_left _ _
  have hmε : A.sourceMesh ≤ MainAssembly.sourceMesh ε := by
    rw [hA]
    exact min_le_right _ _
  have hβlo := (moment_parameter_gates hβ hinc).2.2
  have hfields := actual_stage_fields A.F hβlo baseline_beta hinc
    A.detector_fine A.sourceMesh A.sourceMesh_pos hmD A.source_fine
  obtain ⟨b,_hb,hsupport⟩ :=
    CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bΦ : ℝ := max 2 b
  have hbΦ : 2 ≤ bΦ := le_max_left _ _
  let η := fixedSourcePrincipal A.F.S A.F.exclusions.prime
  obtain ⟨degree,control,C,hC,hsource⟩ :=
    MainAssembly.detector_label_initial_affine SourcePlane.A.mainPlane A.F η (Sum.inl true)
      hβlo baseline_beta (main_source_incumbent .A hinc) ε hε
      A.sourceMesh A.sourceMesh_pos hmε bΦ hbΦ
  refine ⟨A,hfields,bΦ,ε,hε,le_rfl,?_,degree,control,C,hC,?_⟩
  · intro x hx
    exact (show x ≤ b from hsupport hx).trans (le_max_right _ _)
  · simpa only [Physical.AffineAt, Physical.InitialAffineAt, MainInitial.InitialAffineAt,
      MainInitial.plainLower, MainInitial.plainUpper, plainLower, plainUpper,
      Sil.Uneven.MainSource.widthLo, Sil.Uneven.MainSource.widthHi, widthLower, widthUpper,
      SourcePlane.B, SourcePlane.lambda,
      Target830.Source.RecordEndpoint.principal_detector_label]
      using hsource

theorem beta_le_theta (hinc : HeckeZeroSupremum.beta ≤ incumbent) :
    HeckeZeroSupremum.beta ≤ theta :=
  Physical.FinalAssembly.beta_le_theta_of_chosen_source (actual_chosen_source_input hinc)

end
end OAI.SevenEighths.UnevenEndpoint.RecordEndpoint

namespace OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
noncomputable section

theorem beta_le_warmup : HeckeZeroSupremum.beta ≤ (4374143/5000000:ℝ) := by
  exact beta_le_theta (config := ⟨.warmup⟩)
    Target830.Source.RecordEndpoint.beta_le_rational

theorem beta_le_rational :
    HeckeZeroSupremum.beta ≤ (874828524351/1000000000000:ℝ) := by
  exact beta_le_theta (config := ⟨.final⟩) beta_le_warmup

end
end OAI.SevenEighths.UnevenEndpoint.RecordEndpoint
end

/- Original module: Candidate.Uneven.EndpointFinal. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0.
All-moduli Dirichlet export from the two-stage endpoint theorem. -/

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Final
noncomputable section
open scoped _root_.DirichletCharacter

theorem hecke_nonzero (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (874828524351/1000000000000:ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (RecordEndpoint.beta_le_rational.trans_lt hs) hpole

theorem allDirichlet {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874828524351/1000000000000:ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle25.dirichlet_of_hecke (by norm_num) hecke_nonzero χ s hs hpole

end
end OAI.SevenEighths.UnevenEndpoint.Final
end
