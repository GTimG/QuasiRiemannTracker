import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Final.CommonProbe
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths HeckeFamily Cycle63DetectorCount PrincipalSignalComparison

/-- Choose the slot data after a positive analytic mesh cap has been fixed.
The cap precedes the slot count, source profiles, exclusions and ray modulus. -/
theorem exists_chosen_data_with_mesh
    (hβ : Arithmetic.theta<HeckeZeroSupremum.beta)
    {meshCap : ℝ} (hmesh : 0< meshCap) :
    ∃ A : ChosenData, A.P.mesh≤ meshCap := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  have hbudget : 0< min ((HeckeZeroSupremum.beta-Arithmetic.theta)/10000) meshCap :=
    lt_min (by positivity) hmesh
  obtain ⟨D,hκ,hbound,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1 hbudget
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hcount := hbound.trans (min_le_left _ _)
  have ht : D.t≤ meshCap := by
    have hsmall := hbound.trans (min_le_right _ _)
    have he := D.epsilon_pos
    have ht := D.t_pos
    linarith
  have hfineA : ∀j,D.length j≤Cycle63.CountAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (by have := (commonMesh_le_detector (t:=D.t)); linarith)
  exact ⟨⟨D,hκ,hcount,hfine,hfineA,P,F,counts⟩,P.mesh_small.trans ht⟩

/-- The actual numerator is needed for one suitably chosen set of data.
This avoids requiring a moment theorem for every otherwise admissible mesh. -/
def ChosenFiniteNumeratorInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∃ A : ChosenData, ∃ J : ℝ, 0≤J ∧
    ∀ τ : ℝ, HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_chosen_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt Cycle63.CountAffine.detectorMesh)
    (hinput : ChosenFiniteNumeratorInput) :
    WeightedQRH.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,J,hJ,hfinite⟩ := hinput hβ
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

end Record1252270103Bootstrap.PR67
