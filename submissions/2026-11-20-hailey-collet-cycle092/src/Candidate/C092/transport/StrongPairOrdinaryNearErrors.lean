/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Positive errors also paying the downward radius bank and forward cap collar. -/
import Candidate.C092.transport.StrongPairOrdinaryNearPrice
import Candidate.C092.transport.StrongPairOrdinaryErrors

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

theorem near_early_errors {M : ℝ} (hM : 0 ≤ M) :
    ∃ conductor gap ε εsource : ℝ,
      0 < conductor ∧ 0 < gap ∧ 0 < ε ∧ ε ≤ 1/7500 ∧
      0 < εsource ∧ εsource ≤ 1 ∧
      3*conductor ≤ (rho:ℝ)/128 ∧
      (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) ≤ (rho:ℝ)/128 ∧
      (15/4:ℝ)*M*ε ≤ (rho:ℝ)/128 ∧ M*εsource ≤ (rho:ℝ)/128 := by
  obtain ⟨c,g,ε,es,hc,hg,he,he1,hs,hs1,hc1,hgap,hwit,hsrc⟩ :=
    ordinary_early_errors (show 0 ≤ 4*(M+1) by linarith)
  have hE : (0:ℝ) ≤ (responseUpper:ℝ) := by norm_num [responseUpper]
  refine ⟨c,g,ε,es,hc,hg,he,he1,hs,hs1,hc1,?_,?_,?_⟩
  · have hh : M*(2*g)+M*g+g ≤ 4*(M+1)*((3/4:ℝ)*g)+4*(M+1)*g+g := by nlinarith
    exact (mul_le_mul_of_nonneg_left hh hE).trans hgap
  · nlinarith
  · nlinarith

theorem near_fee_bound {M conductor gap ε εsource buffer τ d e B mbar radiusGap dec rounding collar : ℝ}
    {K degree : ℕ}
    (hM : 0 ≤ M) (hd0 : 0 ≤ d) (hd : d ≤ M)
    (he : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hg : 0 ≤ gap) (hgap0 : 0 ≤ B-mbar) (hgap : B-mbar ≤ gap)
    (hRad0 : 0 ≤ radiusGap) (hRad : radiusGap ≤ gap)
    (hdec0 : 0 ≤ dec) (hdec : dec ≤ gap) (hr0 : 0 ≤ rounding) (hr : rounding ≤ gap)
    (hε : 0 ≤ ε) (hs : 0 ≤ εsource)
    (hcollar : collar ≤ 3*conductor) (hc : 3*conductor ≤ (rho:ℝ)/128)
    (hcap : (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) ≤ (rho:ℝ)/128)
    (hwit : (15/4:ℝ)*M*ε ≤ (rho:ℝ)/128) (hsource : M*εsource ≤ (rho:ℝ)/128)
    (hbuffer : buffer*(K:ℝ) ≤ (rho:ℝ)/128) (hheight : τ*(degree:ℝ) ≤ (rho:ℝ)/128) :
    collar+(15/4:ℝ)*d*ε+e*(d*((5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar))+d*dec+rounding)+
      (d*εsource+buffer*(K:ℝ)+τ*(degree:ℝ)) ≤ (3/4:ℝ)*(rho:ℝ) := by
  have hE : (0:ℝ) ≤ (responseUpper:ℝ) := by norm_num [responseUpper]
  have hcap' : e*(d*((5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar))+d*dec+rounding) ≤
      (responseUpper:ℝ)*(M*(2*gap)+M*gap+gap) := by
    apply mul_le_mul he1 _ (by positivity) hE
    have hdelta : (5/4:ℝ)*radiusGap+(3/4:ℝ)*(B-mbar) ≤ 2*gap := by linarith
    have h1 := mul_le_mul hd hdelta (by positivity) hM
    have h2 := mul_le_mul hd hdec hdec0 hM
    linarith
  have hwit' : (15/4:ℝ)*d*ε ≤ (15/4:ℝ)*M*ε := by gcongr
  have hsource' : d*εsource ≤ M*εsource := by gcongr
  have hrho : (0:ℝ) ≤ (rho:ℝ) := by norm_num [rho]
  linarith

#print axioms near_early_errors
#print axioms near_fee_bound
end
end QRH.Cycle092.StrongPair
