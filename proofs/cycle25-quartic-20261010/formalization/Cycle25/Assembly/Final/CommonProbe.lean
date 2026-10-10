import Cycle25.Assembly.Final.Data
import Cycle25.Assembly.Final.FixedHigh
import Cycle25.Numerator.ActualSource

/-! Actual common-probe assembly with both source moment families. Adapted
from weighted upstream HighRows/ConditionalFinal, revision
2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
namespace OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
noncomputable section
open scoped Classical
open Filter Asymptotics HeckeFamily ProbePhysical PrincipalSignalComparison
open Cycle25ProbeFinalAssembly Cycle25.FinalAssembly

theorem common_probe_of_fullW_input (hinput : FullWAnalyticInput) :
    Cycle25.UniformCommonProbe Cycle25.theta signalShift := by
  intro hβ
  obtain ⟨P⟩ := exists_chosen_data hβ
  obtain ⟨Jw,hJw,hinput⟩ := hinput hβ P.D P.fine P.F P.counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hτJw,hsource⟩ :=
    chosen_data_height P.D P.F P.counts P.oldcounts P.J P.Jo Jw
      P.J_nonneg P.Jo_nonneg hJw P.moments P.old_moments
  obtain ⟨n,hn,C,hC,hhigh⟩ := fixed_high_bound_of_fullW hβ baseline_beta
    P.D P.F P.oldcounts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-Cycle25.theta)/2
  have hloss : 0 < loss := by dsimp [loss];linarith only [hβ]
  have hlossgap : loss < HeckeZeroSupremum.beta-Cycle25.theta := by
    dsimp [loss];linarith only [hβ]
  refine ⟨loss,P.D.sigma,hloss,hlossgap,P.D.sigma_pos,?_⟩
  apply source_contract P.D P.F loss hloss
  intro η
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  obtain ⟨Cw,hCw,hcells⟩ := hinput τ hτ hτd hτcost hτt hτ2 hτeps hτJw n η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*(2+Cw)*Cm*(η.modulus.absNorm:ℝ)^(2*P.D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource,hcells] with Z hh hs hc
  simpa only [signalShift,sub_eq_add_neg,neg_div] using
    hh Cm hCm Cw hCw hs.2 (hc Cm hCm hs.1)

theorem actual_common_probe : Cycle25.UniformCommonProbe Cycle25.theta signalShift :=
  common_probe_of_fullW_input Cycle25.Numerator.actual_fullW_input
end
end OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
