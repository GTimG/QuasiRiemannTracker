import Cycle25.Assembly.HighDataFine
import Cycle25.Assembly.Count.ActualMoments
import Cycle25.Assembly.Count.OriginalActualMoments

/-! The height is chosen after both source-moment degrees and the weighted
cell degree.  One character-dependent constant then controls both moment
families at that height.  Adapted from weighted upstream HighRows/ConditionalFinal,
revision 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
noncomputable section
open scoped Classical
open Filter HeckeFamily Cycle25ProbeFinalAssembly

theorem chosen_data_height {Δ : ℝ} (D : Cycle25.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t)
    (oldcounts : ProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)
    (J Jo Jw : ℝ) (hJ : 0 ≤ J) (hJo : 0 ≤ Jo) (hJw : 0 ≤ Jw)
    (hbound : ∀η : Character,∃C : ℝ,0 < C ∧
      ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F D.momentKappa counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)))
    (hboundOld : ∀η : Character,∃C : ℝ,0 < C ∧
      ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
        old_sourceMomentBound F oldcounts η Z τ
          (C*(1+Z^(2*τ))^Jo) (Z^(2*τ))) :
    ∃τ : ℝ,0 < τ ∧ τ < (1/200:ℝ)/2 ∧ 4*τ < (1/200)*D.cost ∧ τ < D.t ∧
      2*τ ≤ D.t ∧ τ*(2+4*D.eps) < D.t ∧ 2*τ*(1+Jw) ≤ D.t ∧
      ∀η : Character,∃C : ℝ,1 ≤ C ∧ ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F D.momentKappa counts η Z τ (C*Z^D.t) (Z^(2*τ)) ∧
        old_sourceMomentBound F oldcounts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJtotal,hτeps⟩ :=
    D.height_choice (J+Jo+Jw) (by positivity)
  have hτJ : 2*τ*(1+J) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJo,mul_nonneg hτ.le hJw]
  have hτJo : 2*τ*(1+Jo) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJ,mul_nonneg hτ.le hJw]
  have hτJw : 2*τ*(1+Jw) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJ,mul_nonneg hτ.le hJo]
  have htau1 : τ ≤ 1 := by linarith only [hτd]
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith only [hτJ,mul_nonneg hτ.le hJ],
    hτeps,hτJw,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  obtain ⟨Co,hCo,hboundOld⟩ := hboundOld η
  have hP : 0 ≤ C*2^J := by positivity
  have hPo : 0 ≤ Co*2^Jo := by positivity
  refine ⟨C*2^J+Co*2^Jo+1,by linarith,?_⟩
  filter_upwards [hbound τ hτ htau1,hboundOld τ hτ htau1,
    eventually_ge_atTop (1:ℝ)] with Z hb hbo hZ
  have habs := ProbeFinalAssembly.polynomial_height_absorption C Z τ J D.t
    hC.le hZ hτ.le hJ (by linarith only [hτJ])
  have habso := ProbeFinalAssembly.polynomial_height_absorption Co Z τ Jo D.t
    hCo.le hZ hτ.le hJo (by linarith only [hτJo])
  constructor
  · apply weighted_SourceMomentBound.mono_constant (by linarith only [hZ]) hb
    exact habs.trans (mul_le_mul_of_nonneg_right
      (by linarith : C*2^J ≤ C*2^J+Co*2^Jo+1) (by positivity))
  · apply old_sourceMomentBound.mono_constant (by linarith only [hZ]) hbo
    exact habso.trans (mul_le_mul_of_nonneg_right
      (by linarith : Co*2^Jo ≤ C*2^J+Co*2^Jo+1) (by positivity))
end
end OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
