import QRH.NumericFacts
import QRH.Detector.ActualOptimizedLow
import QRH.Detector.OptimizedContinuation

/-! The supremum contradiction with actual, unconditionally constructed probes.
No moment estimate, common-probe contract, or analytic saving is assumed. -/
namespace OAI
noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.QRHFinalAssembly
open HeckeFamily HeckeZeroSupremum ProbeFinalAssembly PrincipalSignalComparison

theorem beta_le_tightTheta : beta≤QRH.tightTheta := by
  by_contra hn
  have hβ:QRH.tightTheta<beta:=lt_of_not_ge hn
  obtain ⟨D,S,hhigh⟩:=exists_actual_optimized_high hβ
  let ω:ℝ:=(beta-QRH.tightTheta)/2
  let σ:ℝ:=D.sigma/8
  have hω0:0<ω:=by dsimp [ω];linarith
  have hω:ω<beta-QRH.tightTheta:=by dsimp [ω];linarith
  have hσ:0<σ:=by dsimp [σ];exact div_pos D.sigma_pos (by norm_num)
  obtain ⟨hε,hboundary,_,_⟩:=QRH.continuation_parameters hω0 hω hσ
  have hθhalf:(1/2:ℝ)<QRH.tightTheta:=by linarith [QRH.NumericFacts.theta_lower]
  obtain ⟨η,ρ,_,hhalf,_,hpole,hz,hnear⟩:=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hε (by linarith)
  let χ:=η.excludePrimes S.S S.exclusions.prime
  have hmask:=excludePrimes_mask η S.S S.exclusions.prime
  have hχpole:ρ≠1∨χ.residue≠1:=by
    rcases hpole with h1|hη
    · exact Or.inl h1
    · exact Or.inr (fun hc=>hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hc))
  have hzχ:LFunction χ ρ=0:=by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask (by linarith) hχpole,hz,zero_mul]
  have hlow:=actual_optimized_low S ω hω0 η
  have herr:=isBigO_rpow_of_eventual_norm_bound _ _ (hhigh η)
  have hH:AnalyticOnNhd ℂ (sourceCorrection η S.S) {s:ℂ|87/100<s.re}:=
    (QRHPrincipalSignal.sourceCorrection_differentiable η S.S S.exclusions).analyticOnNhd
      (Complex.isOpen_re_gt _)
  apply (QRHContinuation.nonzero_of_probe_bounds χ (sourceCorrection η S.S)
    (optimizedNormalizedProbe S η) beta ω σ (QRH.C 0) beta_le_one hω0 hω hσ hH
    (QRHPrincipalSignal.sourceCorrection_bound η S.S S.exclusions) ?_ ?_ hnear hχpole) hzχ
  · convert hlow using 1;unfold QRH.C;ring_nf
  · convert herr using 1;dsimp [σ];unfold QRH.C;ring_nf

theorem beta_le_theta : beta ≤ QRH.theta :=
  beta_le_tightTheta.trans QRH.tightTheta_le_theta

end SevenEighths.QRHFinalAssembly
end
end OAI
