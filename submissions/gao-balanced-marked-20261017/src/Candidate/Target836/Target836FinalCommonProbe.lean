/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Candidate.Target836.Target836FinalFixedHigh

                                       

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Target836DetectorCount

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤ Cycle25.sourceMesh D.t/200
  detector_fine : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Target836Count.CountParameters (baselineSource D F).modulus ⊤ D.t

theorem exists_chosen_data (hβ : Arithmetic.theta< HeckeZeroSupremum.beta) : Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  obtain ⟨D,hκ,hbudget,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1
    (show 0<(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 by positivity)
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  exact ⟨⟨D,hκ,hbudget,hfine,hdet,P,F,counts⟩⟩

/-- Honest intermediate source obligation. Fixed data and polynomial degree precede
height; actual baseline source moments at that height are supplied by the assembly. -/
def FiniteNumeratorAssemblyInput : Prop :=
  Arithmetic.theta< HeckeZeroSupremum.beta →
  ∀A : ChosenData,∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_finite_numerator
    (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : FiniteNumeratorAssemblyInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A⟩ := exists_chosen_data hβ
  obtain ⟨J,hJ,hfinite⟩ := hinput hβ A
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤ A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0< loss := by dsimp [loss];linarith
  have hgap : loss< HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=>by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Target836.FinalAssembly


#print axioms Target836.FinalAssembly.exists_chosen_data
#print axioms Target836.FinalAssembly.common_probe_of_finite_numerator
