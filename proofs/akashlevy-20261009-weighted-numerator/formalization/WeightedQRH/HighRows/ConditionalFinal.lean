import WeightedQRH.HighRows.FixedHigh
import WeightedQRH.Continuation

/-!
Conditional completion with actual parameter choices, actual source data, and certified
source moments. The sole unproved analytic input is FullWAnalyticInput below.
This module does NOT establish that input and does NOT assert an unconditional QRH bound.
-/
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
namespace SevenEighths.WeightedHighFinalAssembly
open HeckeFamily ProbePhysical ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open PrincipalSignalComparison

/-- Uniform literal full-w cell estimates at the chosen physical geometry. -/
def FullWAnalyticInput : Prop :=
  ∀_hβ : WeightedQRH.theta < HeckeZeroSupremum.beta,
  ∀D : WeightedQRH.HighParameters.HighData (HeckeZeroSupremum.beta-WeightedQRH.theta),
  (∀j,D.ell j ≤ weighted_detectorMesh D.t/200) →
  ∀F : WeightedSourceData D.toMomentData,
  ∀counts : CountParameters F.modulus ⊤ D.t,
  ∃Jw : ℝ,0 ≤ Jw ∧
  ∀τ : ℝ,0 < τ → τ < (1/200:ℝ)/2 → 4*τ < (1/200)*D.cost →
    τ < D.t → 2*τ ≤ D.t → τ*(2+4*D.eps) < D.t → 2*τ*(1+Jw) ≤ D.t →
  ∀n : ℕ,∀η : Character,∃Cw : ℝ,0 ≤ Cw ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1 ≤ C0 →
    weighted_SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
    FullWCellsAt D F η Z τ n Cw C0

theorem chosen_data_height {Δ : ℝ} (D : WeightedQRH.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (counts : CountParameters F.modulus ⊤ D.t)
    (J : ℝ) (hJ : 0 ≤ J) (Jw : ℝ) (hJw : 0 ≤ Jw)
    (hbound : ∀η : Character,∃C : ℝ,0 < C ∧
      ∀τ : ℝ,0 < τ → τ ≤ 1 → ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))) :
    ∃τ : ℝ,0 < τ ∧ τ < (1/200:ℝ)/2 ∧ 4*τ < (1/200)*D.cost ∧ τ < D.t ∧
      2*τ ≤ D.t ∧ τ*(2+4*D.eps) < D.t ∧ 2*τ*(1+Jw) ≤ D.t ∧
      ∀η : Character,∃C : ℝ,1 ≤ C ∧ ∀ᶠZ : ℝ in atTop,
        weighted_SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJtotal,hτeps⟩ := D.height_choice (J+Jw) (add_nonneg hJ hJw)
  have hτJ : 2*τ*(1+J) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJw]
  have hτJw : 2*τ*(1+Jw) ≤ D.t := by
    nlinarith only [hτJtotal,mul_nonneg hτ.le hJ]
  have htau1 : τ ≤ 1 := by linarith only [hτd]
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith only [hτJ,mul_nonneg hτ.le hJ],hτeps,hτJw,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  have hCone : 1 ≤ C*2^J+1 := by
    have hp : 0 ≤ C*2^J := by positivity
    linarith only [hp]
  refine ⟨C*2^J+1,hCone,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  apply weighted_SourceMomentBound.mono_constant (by linarith only [hZ]) hb
  have habs := polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith only [hτJ])
  exact habs.trans (mul_le_mul_of_nonneg_right (by linarith : C*2^J ≤ C*2^J+1) (by positivity))

/-- All probe and moment hypotheses are constructed; only the literal weighted
full-w estimate named in the hypothesis remains to be proved. -/
theorem common_probe_of_fullW_input (hinput : FullWAnalyticInput) :
    WeightedQRH.UniformCommonProbe WeightedQRH.theta (-681/1000) := by
  intro hβ
  obtain ⟨D,hfine⟩ := WeightedQRH.HighParameters.exists_high_data_fine
    (HeckeZeroSupremum.beta-WeightedQRH.theta) (sub_pos.mpr hβ)
    weighted_detectorMesh (fun _ ht=>weighted_detectorMesh_pos ht)
  obtain ⟨F⟩ := weighted_exists_source_data D.toMomentData
  obtain ⟨counts⟩ := weighted_source_count_parameters F
  have hbeta51 : (51/100:ℝ) ≤ HeckeZeroSupremum.beta := by
    have hh : (51/100:ℝ) < WeightedQRH.theta := by norm_num [WeightedQRH.theta]
    exact hh.le.trans hβ.le
  obtain ⟨J,hJ,hmom⟩ := weighted_actual_source_moments F hbeta51 counts hfine
  obtain ⟨Jw,hJw,hinput⟩ := hinput hβ D hfine F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hτJw,hsource⟩ :=
    chosen_data_height D F counts J hJ Jw hJw hmom
  obtain ⟨n,hn,C,hC,hhigh⟩ := fixed_high_bound_of_fullW hβ weighted_background_beta
    D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-WeightedQRH.theta)/2
  have hloss : 0 < loss := by dsimp [loss];linarith only [hβ]
  have hlossgap : loss < HeckeZeroSupremum.beta-WeightedQRH.theta := by dsimp [loss];linarith only [hβ]
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,sourceProbe D F η,
    hmask,hH,hHbound,?_,?_⟩
  · convert sourceProbe_low D F loss hloss η using 1
    congr 1
    funext Z
    congr 1
    norm_num [WeightedQRH.signal,WeightedQRH.b]
    ring
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    obtain ⟨Cw,hCw,hcells⟩ := hinput τ hτ hτd hτcost hτt hτ2 hτeps hτJw n η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*(2+Cw)*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource,hcells] with Z hh hs hc
    simpa only [sub_eq_add_neg,neg_div] using hh Cm hCm Cw hCw hs (hc Cm hCm hs)

/-- Conditional QRH endpoint: requires the unproved FullWAnalyticInput explicitly. -/
theorem beta_le_theta_of_fullW_input (hinput : FullWAnalyticInput) :
    HeckeZeroSupremum.beta ≤ WeightedQRH.theta :=
  WeightedQRH.beta_le_of_common_probe WeightedQRH.theta_gt_half.le
    WeightedQRH.theta_lt_seven_eighths.le (common_probe_of_fullW_input hinput)

theorem hecke_of_fullW_input (hinput : FullWAnalyticInput) (χ : Character) (s : ℂ)
    (hs : WeightedQRH.theta < s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_fullW_input hinput).trans_lt hs) hpole

theorem dirichlet_of_fullW_input (hinput : FullWAnalyticInput) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : WeightedQRH.theta < s.re)
    (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  WeightedQRH.dirichlet_of_hecke WeightedQRH.theta_pos (hecke_of_fullW_input hinput) χ s hs hexc

theorem zeta_of_fullW_input (hinput : FullWAnalyticInput) (s : ℂ)
    (hs : WeightedQRH.theta < s.re) : riemannZeta s≠0 :=
  WeightedQRH.zeta_of_hecke WeightedQRH.theta_pos (hecke_of_fullW_input hinput) s hs

end SevenEighths.WeightedHighFinalAssembly
end
end OAI
