import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.AssemblyExtension.FinalAssemblyFixedHigh
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.AnalyticBridge

/- Conditional analytic assembly for the same concrete physical probe.
   The character-uniform polynomial moment bound is an explicit hypothesis. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Parameters
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly
open PrincipalExtension PrincipalSignalComparison

theorem rational_contract_of_source_moments {recordMesh : ℝ}
    (hβ : sigmaRat<HeckeZeroSupremum.beta)
    (D : RetunedHighData (HeckeZeroSupremum.beta-sigmaRat) ellRat (1/1000000000000000) recordMesh)
    (F : RetunedSourceData D)
    (counts : FiberExtension.RetunedCountParameters F.modulus ⊤ D.t)
    (hmom : ∃J : ℝ,0≤J ∧ ∀η : Character,∃C : ℝ,0<C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound_retuned F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))) :
    ∃lossParam epsParam shift : ℝ,0<lossParam ∧ lossParam<HeckeZeroSupremum.beta-sigmaRat ∧ 0<epsParam ∧
      RetunedPrimitiveContract sigmaRat lossParam epsParam shift := by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_source_height_retuned D F counts hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound_retuned hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-sigmaRat)/2
  have hloss : 0<loss := by dsimp [loss]; linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-sigmaRat := by dsimp [loss]; linarith
  have hsigma : 0<D.sigma/2 := div_pos D.sigma_pos (by norm_num)
  refine ⟨loss,D.sigma/2,sourceShift lxRat ellRat,hloss,hlossgap,hsigma,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := retuned_source_analytic F sigmaRat (by norm_num [sigmaRat]) η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe lxRat lyRat η,
    hmask,hH,hHbound,F.rational_probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

#print axioms rational_contract_of_source_moments
end
end BelowSevenEighthsTight.Parameters
