import QRH.Continuation
import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity

namespace OAI
noncomputable section
open Filter Asymptotics
namespace SevenEighths.QRHContinuation
open HeckeFamily HeckeSignal Continuation

theorem nonzero_of_probe_bounds (χ:Character) (H:ℂ→ℂ) (J:ℝ→ℂ)
    (β ω σ c:ℝ) (hβ:β≤1) (hω0:0<ω) (hω:ω<β-QRH.tightTheta) (hσ:0<σ)
    (hH:AnalyticOnNhd ℂ H {s:ℂ|87/100<s.re})
    (hb:∀s:ℂ,87/100<s.re→‖H s-1‖≤1/2)
    (hJ:J=O[atTop](fun x:ℝ=>x^(QRH.tightTheta+c+ω)))
    (herror:(fun x=>J x-signal χ H c x)=O[atTop](fun x:ℝ=>x^(β+c-σ)))
    {ρ:ℂ} (hρ:β-min (β-QRH.tightTheta-ω) σ<ρ.re)
    (hpole:ρ≠1∨χ.residue≠1):LFunction χ ρ≠0 := by
  let ε:=min (β-QRH.tightTheta-ω) σ
  let a:=β-ε
  obtain ⟨hε,hboundary,_,hexp⟩:=QRH.continuation_parameters hω0 hω hσ
  have hθ:(87/100:ℝ)<QRH.tightTheta:=by norm_num [QRH.tightTheta]
  have ha2:a<2:=by dsimp [a,ε];linarith
  have hH7:AnalyticOnNhd ℂ H {s:ℂ|7/8<s.re}:=
    hH.mono (fun s hs=>by change 7/8<s.re at hs;change 87/100<s.re;linarith)
  have hb7:∀s:ℂ,7/8<s.re→‖H s-1‖≤1/2:=fun s hs=>hb s (by linarith)
  have htop:signal χ H c=O[atTop](fun x:ℝ=>x^(a+c)):=by
    have hh:=common_signal_bound J (signal χ H c) _ _ hJ herror
    rw [hexp c] at hh
    convert hh using 1;dsimp [a,ε];ring_nf
  have hHa:AnalyticOnNhd ℂ H {s:ℂ|a<s.re}:=
    hH.mono (fun s hs=>hθ.trans (hboundary.trans hs))
  apply nonzero_of_regularized_signal a 1 c (LFunction χ) (regularL χ)
    (targetRegularizer χ) (gaussianMultiplier H) (signal χ H c)
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire χ)).mono (Set.subset_univ _))
    ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (targetRegularizer_entire χ)).mono (Set.subset_univ _))
    (gaussianMultiplier_analytic hHa) (signal_locallyIntegrable χ H hH7.differentiableOn hb7 c)
    htop (signal_rapidDecayAtZero χ H hH7.differentiableOn hb7 c) _ hρ _
    (targetRegularizer_ne_zero χ hpole)
    (gaussianMultiplier_ne_zero (hb ρ (hθ.trans (hboundary.trans hρ))))
  · intro s hs
    have hs1:1<s.re:=(le_max_right a 1).trans_lt hs
    have h0:s≠0:=by intro h;norm_num [h] at hs1
    have h1:s≠1:=by intro h;norm_num [h] at hs1
    rw [regularL_eq χ h0 (Or.inl h1),signalMellin_eq_amplitude χ H hH7.differentiableOn hb7 c a ha2 htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
    have hn:=LFunction_ne_zero_of_one_lt_re χ hs1
    field_simp
  · apply regularL_eq χ _ hpole
    intro h
    rw [h] at hρ
    norm_num at hρ
    have hpos:0<QRH.tightTheta:=by norm_num [QRH.tightTheta]
    linarith

end SevenEighths.QRHContinuation
end
end OAI
