/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Assembly.Final.CommonProbe

set_option autoImplicit false
namespace Cycle62.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths HeckeFamily Cycle62DetectorCount

/-- Choose the slot data after a positive analytic mesh cap has been fixed.
The cap precedes the slot count, source profiles, exclusions and ray modulus. -/
theorem exists_chosen_data_with_mesh
    (hβ : Arithmetic.theta<HeckeZeroSupremum.beta)
    {meshCap : ℝ} (hmesh : 0<meshCap) :
    ∃ A : ChosenData, A.P.mesh≤meshCap := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  have hbudget : 0<min ((HeckeZeroSupremum.beta-Arithmetic.theta)/10000) meshCap :=
    lt_min (by positivity) hmesh
  obtain ⟨D,hκ,hbound,hfine,_,⟨P⟩⟩ := exists_compatible_data hk hk1 hbudget
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hcount := hbound.trans (min_le_left _ _)
  have ht : D.t≤meshCap := by
    have hsmall := hbound.trans (min_le_right _ _)
    have he := D.epsilon_pos
    have ht := D.t_pos
    linarith
  exact ⟨⟨D,hκ,hcount,hfine,P,F,counts⟩,P.mesh_small.trans ht⟩

/-- The actual numerator is needed for one suitably chosen set of data.
This avoids requiring a moment theorem for every otherwise admissible mesh. -/
def ChosenFiniteNumeratorInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∃ A : ChosenData, ∃ J : ℝ, 0≤J ∧
    ∀ τ : ℝ, HeightAdmissible A.D A.P J τ →
    (∀η : Character,∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInput A.D A.F A.P τ

theorem common_probe_of_chosen_finite_numerator
    (hinput : ChosenFiniteNumeratorInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,J,hJ,hfinite⟩ := hinput hβ
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  obtain ⟨τ,hheight,hcount⟩ := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine J hJ
  have herror := sourceProbe_high_of_finite_numerator A.D A.F A.P J τ hheight hβ.le
    (hfinite τ hheight hcount)
  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss herror⟩
end
end Cycle62.FinalAssembly

#print axioms Cycle62.FinalAssembly.exists_chosen_data_with_mesh
#print axioms Cycle62.FinalAssembly.common_probe_of_chosen_finite_numerator
