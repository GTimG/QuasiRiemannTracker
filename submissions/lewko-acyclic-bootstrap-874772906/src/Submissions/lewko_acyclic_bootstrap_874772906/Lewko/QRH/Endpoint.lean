/- Private Mark Lewko parameter instance, 2026-10-22.
Analytic/source interfaces: Hailey Collet, Apache-2.0; retained notices in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Sources
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Sources
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.EndpointFromSources
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.EndpointFromSources
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Lewko.QRH.Endpoint
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Graph

theorem first_family_beta : HeckeZeroSupremum.beta ≤ (87477291/100000000:ℝ) := by
 by_cases hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
 · have hk := final_natural_cap QRH.Record1252270103Source.Endpoint.seed_step hb
   have hk' : 6*(2*HeckeZeroSupremum.beta-1) ≤ (11243277/2500000:ℝ) := by
    simpa [finalK] using hk
   obtain ⟨hC,hP⟩ := Lewko.QRH.Stage1.global_suppliers hb hk' hk
   have hcap : 2*HeckeZeroSupremum.beta-1 ≤ LewkoStage1Finite.naturalK/6 := by
    norm_num [LewkoStage1Finite.naturalK]; linarith
   have h := QRH.LewkoStage1Return.Final.beta_of_global_sources hC hP hcap
   convert h using 1 <;> norm_num [LewkoStage1Finite.theta,LewkoStage1Finite.c]
 · have h := (not_le.mp hb).le
   linarith

theorem first_hecke_nonvanishing (χ : Character) (s : ℂ)
 (hs : (87477291/100000000:ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
 LFunction χ s ≠ 0 :=
 HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (first_family_beta.trans_lt hs) hpole

/-- The first endpoint is the full relevant Hecke supremum premise. -/
theorem new_natural_cost :
 6*(2*HeckeZeroSupremum.beta-1) ≤ (112431873/25000000:ℝ) := by
 have h := first_family_beta
 linarith

theorem family_beta : HeckeZeroSupremum.beta ≤ (437386453/500000000:ℝ) := by
 by_cases hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
 · have hk := final_natural_cap QRH.Record1252270103Source.Endpoint.seed_step hb
   obtain ⟨hC,hP⟩ := Lewko.QRH.Stage2.global_suppliers hb new_natural_cost hk
   have hcap : 2*HeckeZeroSupremum.beta-1 ≤ LewkoStage2Finite.naturalK/6 := by
    norm_num [LewkoStage2Finite.naturalK]
    have h := first_family_beta
    linarith
   have h := QRH.LewkoStage2Return.Final.beta_of_global_sources hC hP hcap
   convert h using 1 <;> norm_num [LewkoStage2Finite.theta,LewkoStage2Finite.c]
 · have h := (not_le.mp hb).le
   linarith

theorem hecke_nonvanishing (χ : Character) (s : ℂ)
 (hs : (437386453/500000000:ℝ) < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
 LFunction χ s ≠ 0 :=
 HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (family_beta.trans_lt hs) hpole

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
 (hs : (437386453/500000000:ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
 _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
 Cycle25.dirichlet_of_hecke (by norm_num) hecke_nonvanishing χ s hs hpole
end
end Lewko.QRH.Endpoint
#print axioms Lewko.QRH.Endpoint.first_family_beta
#print axioms Lewko.QRH.Endpoint.first_hecke_nonvanishing
#print axioms Lewko.QRH.Endpoint.new_natural_cost
#print axioms Lewko.QRH.Endpoint.family_beta
#print axioms Lewko.QRH.Endpoint.hecke_nonvanishing
#print axioms Lewko.QRH.Endpoint.dirichlet_nonvanishing
