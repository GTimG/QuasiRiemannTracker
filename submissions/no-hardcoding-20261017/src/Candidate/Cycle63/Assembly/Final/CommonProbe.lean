import Candidate.Cycle63.Assembly.Final.FixedHigh

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics OAI.SevenEighths
open HeckeFamily Cycle63DetectorCount PrincipalSignalComparison

structure ChosenData where
  D : BaselineData
  kappa_exact : D.momentKappa=2*HeckeZeroSupremum.beta-1
  count_budget : 159*D.ε+609*D.t≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000
  fine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200
  fineA : ∀j,D.length j≤Cycle63.CountAffine.detectorMesh D.t/200
  P : TransportParameters D
  F : BaselineSourceData D
  counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t

theorem exists_chosen_data (hβ : Arithmetic.theta<HeckeZeroSupremum.beta) : Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  obtain ⟨D,hκ,hbudget,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1
    (show 0<(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 by positivity)
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hfineA : ∀j,D.length j≤Cycle63.CountAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (by have := (commonMesh_le_detector (t:=D.t)); linarith)
  exact ⟨⟨D,hκ,hbudget,hfine,hfineA,P,F,counts⟩⟩

/-- Honest intermediate source obligation. Fixed data and polynomial degree precede
height; actual baseline source moments at that height are supplied by the assembly. -/
def FiniteNumeratorAssemblyInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∀A : ChosenData,∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : FiniteNumeratorAssemblyInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A⟩ := exists_chosen_data hβ
  obtain ⟨J,hJ,hfinite⟩ := hinput hβ A
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  have herror : ∀η : Character,
      (fun Z=>sourceProbe A.D A.F η Z-HeckeSignal.signal
        (η.excludePrimes A.F.S A.F.exclusions.prime) (sourceCorrection η A.F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)) := by
    intro η
    obtain ⟨τ,hheight,hcount⟩ := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
      Cycle63.CountAffine.detectorMesh hdet baseline_beta A.fineA J hJ η
    exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
      (hfinite τ hheight η hcount)
  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss herror⟩
end
end Cycle63.FinalAssembly
