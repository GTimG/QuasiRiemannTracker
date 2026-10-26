/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two analytic source-step suppliers remain explicit until proved. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.FinalSources
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record12518109Existence

theorem four_global_suppliers (seed:SeedStep) (step:NFStep)
 (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
 (UniformUnitFaceSource Record1252270103Return.IntermediateCount.countGlobal ∧
  UniformUnitFaceSource Record1252270103Return.IntermediateCount.physicalGlobal) ∧
 (UniformUnitFaceSource Record1252270103Return.countGlobal ∧
  UniformUnitFaceSource Record1252270103Return.physicalGlobal) :=
 ⟨seed_global_suppliers seed hbeta,final_global_suppliers seed step hbeta⟩

theorem beta_of_steps (seed:SeedStep) (step:NFStep) :
 HeckeZeroSupremum.beta ≤ Record1252270103Finite.theta := by
 by_cases hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta
 · obtain ⟨⟨hC29C,hC29P⟩,⟨hC,hP⟩⟩ := four_global_suppliers seed step hbeta
   exact Record1252270103Return.beta_of_four_global_sources hC29C hC29P hC hP
 · have ht:(51/100:ℝ) ≤ Record1252270103Finite.theta := by norm_num [theta,c]
   exact (not_le.mp hbeta).le.trans ht

theorem hecke_of_steps (seed:SeedStep) (step:NFStep)
 (χ:Character) (s:ℂ) (hs:Record1252270103Finite.theta < s.re)
 (hpole:s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
 HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ ((beta_of_steps seed step).trans_lt hs) hpole

theorem dirichlet_of_steps (seed:SeedStep) (step:NFStep)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:Record1252270103Finite.theta < s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [theta,c]) (hecke_of_steps seed step) χ s hs hpole

theorem zeta_of_steps (seed:SeedStep) (step:NFStep)
 (s:ℂ) (hs:Record1252270103Finite.theta < s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [theta,c]) (hecke_of_steps seed step) s hs
end
end QRH.Record1252270103Graph
#print axioms QRH.Record1252270103Graph.four_global_suppliers
#print axioms QRH.Record1252270103Graph.beta_of_steps
#print axioms QRH.Record1252270103Graph.hecke_of_steps
#print axioms QRH.Record1252270103Graph.dirichlet_of_steps
#print axioms QRH.Record1252270103Graph.zeta_of_steps
