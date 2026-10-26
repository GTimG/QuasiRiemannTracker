/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.InitialRegularCallbacks
import Submissions.hailey_collet_1252270103.Record1252270103Graph.Endpoint
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Endpoint
noncomputable section
open OAI.SevenEighths HeckeFamily QRH.Record1252270103Graph
open InitialTruncated InitialRegularToTruncated

theorem seed_step : SeedStep := seed_step_of_truncated seed_truncated

theorem nf_step : NFStep := nf_step_of_truncated nf_truncated

theorem beta_bound : HeckeZeroSupremum.beta≤(8747729897/10000000000:ℝ) := by
  convert beta_of_steps seed_step nf_step using 1 <;>
    norm_num [Record1252270103Finite.theta,Record1252270103Finite.c]

theorem hecke_nonvanishing (χ:Character)(s:ℂ)
    (hs:(8747729897/10000000000:ℝ)<s.re)(hpole:s≠1 ∨ χ.residue≠1) :
    LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (beta_bound.trans_lt hs) hpole

theorem dirichlet_nonvanishing {q:ℕ}[NeZero q](χ:DirichletCharacter ℂ q)(s:ℂ)
    (hs:(8747729897/10000000000:ℝ)<s.re)(hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 := by
  apply dirichlet_of_steps seed_step nf_step χ s _ hpole
  convert hs using 1 <;> norm_num [Record1252270103Finite.theta,Record1252270103Finite.c]

theorem zeta_nonvanishing (s:ℂ)(hs:(8747729897/10000000000:ℝ)<s.re) : riemannZeta s≠0 := by
  apply zeta_of_steps seed_step nf_step s
  convert hs using 1 <;> norm_num [Record1252270103Finite.theta,Record1252270103Finite.c]
end
end QRH.Record1252270103Source.Endpoint
#print axioms QRH.Record1252270103Source.Endpoint.seed_step
#print axioms QRH.Record1252270103Source.Endpoint.nf_step
#print axioms QRH.Record1252270103Source.Endpoint.beta_bound
#print axioms QRH.Record1252270103Source.Endpoint.hecke_nonvanishing
#print axioms QRH.Record1252270103Source.Endpoint.dirichlet_nonvanishing
#print axioms QRH.Record1252270103Source.Endpoint.zeta_nonvanishing
