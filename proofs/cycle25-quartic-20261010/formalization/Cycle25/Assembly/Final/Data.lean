import Cycle25.Assembly.Final.Baseline
import Cycle25.Assembly.Final.Height

/-! Actual fixed source data and both certified count families are chosen
before the contour height.  Apache-2.0 attribution: weighted upstream
HighRows/ConditionalFinal, revision 2fd60c0926b66ea18d7436f5ed55250fd006ab5d. -/
namespace Cycle25.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.Cycle25ProbeFinalAssembly

structure ChosenData where
  D : HighParameters.HighData (HeckeZeroSupremum.beta-theta)
  fine : ∀j,D.ell j ≤ sourceMesh D.t/200
  F : WeightedSourceData D.toMomentData
  counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t
  oldcounts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t
  J : ℝ
  Jo : ℝ
  J_nonneg : 0 ≤ J
  Jo_nonneg : 0 ≤ Jo
  moments : ∀η : Character,∃C : ℝ,0 < C ∧
    ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
      weighted_SourceMomentBound F D.momentKappa counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ))
  old_moments : ∀η : Character,∃C : ℝ,0 < C ∧
    ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
      old_sourceMomentBound F oldcounts η Z τ
        (C*(1+Z^(2*τ))^Jo) (Z^(2*τ))

theorem exists_chosen_data (hβ : theta < HeckeZeroSupremum.beta) :
    Nonempty ChosenData := by
  obtain ⟨hk,hk1,hbeta51⟩ := moment_parameter_gates hβ
  obtain ⟨D,hfine⟩ := HighParameters.exists_high_data_fine
    (HeckeZeroSupremum.beta-theta) (sub_pos.mpr hβ)
    (2*HeckeZeroSupremum.beta-1) hk hk1 le_rfl rfl sourceMesh
    (fun _ ht=>sourceMesh_pos ht)
  obtain ⟨F⟩ := weighted_exists_source_data D.toMomentData
  obtain ⟨counts⟩ := weighted_fresh_count_parameters F
  obtain ⟨oldcounts⟩ := weighted_source_count_parameters F
  obtain ⟨J,hJ,hmom⟩ := weighted_actual_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hbeta51 D.momentKappa_beta counts hfine
  obtain ⟨Jo,hJo,hmomOld⟩ := weighted_actual_old_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hbeta51 D.momentKappa_beta oldcounts hfine
  exact ⟨⟨D,hfine,F,counts,oldcounts,J,Jo,hJ,hJo,hmom,hmomOld⟩⟩
end
end Cycle25.FinalAssembly
