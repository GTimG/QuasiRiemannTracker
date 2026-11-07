/- Subhanjan Das; MIT for new assembly; AI-assisted with OpenAI Codex.
Retains the admitted Collet/Lewko/OpenAI analytic framework and its notices. -/
import Candidate.SuppliersA
import Candidate.SuppliersB
import Candidate.ReturnA.Endpoint
import Candidate.ReturnB.Endpoint
import Candidate.FamilyTransfer
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.Endpoint
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

theorem first_family_beta (input:Das.QRH.TrackerRebuild.Inputs) : HeckeZeroSupremum.beta ≤ DasStageAFinite.theta := by
 by_cases hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
 · obtain ⟨hc,hp⟩ := Das.QRH.SuppliersA.global_suppliers input hb
   apply Das.QRH.ReturnA.beta_of_global_sources hc hp
   have h := Das.QRH.TrackerRebuild.root_cap input
   norm_num [Das.QRH.TrackerRebuild.rootK,DasStageAFinite.naturalK] at *
   linarith
 · have ht : (51/100:ℝ) < DasStageAFinite.theta := by
    norm_num [DasStageAFinite.theta,DasStageAFinite.c]
   exact (not_le.mp hb).le.trans ht.le

theorem family_beta (input:Das.QRH.TrackerRebuild.Inputs) : HeckeZeroSupremum.beta ≤ DasStageBFinite.theta := by
 by_cases hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
 · have prior : HeckeZeroSupremum.beta ≤ Das.QRH.TrackerGeometry.thetaA := by
    convert first_family_beta input using 1 <;>
     norm_num [DasStageAFinite.theta,DasStageAFinite.c,Das.QRH.TrackerGeometry.thetaA]
   obtain ⟨hc,hp⟩ := Das.QRH.SuppliersB.global_suppliers input hb prior
   apply Das.QRH.ReturnB.beta_of_global_sources hc hp
   have h := first_family_beta input
   norm_num [DasStageAFinite.theta,DasStageAFinite.c,DasStageBFinite.naturalK] at *
   linarith
 · have ht : (51/100:ℝ) < DasStageBFinite.theta := by
    norm_num [DasStageBFinite.theta,DasStageBFinite.c]
   exact (not_le.mp hb).le.trans ht.le

theorem hecke_nonvanishing (input:Das.QRH.TrackerRebuild.Inputs) (χ:Character) (s:ℂ)
 (hs:DasStageBFinite.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 :=
 HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ ((family_beta input).trans_lt hs) hpole

theorem dirichlet_nonvanishing (input:Das.QRH.TrackerRebuild.Inputs) {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:(174954253/200000000:ℝ)<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 := by
 apply Das.QRH.FamilyTransfer.dirichlet_of_family_beta
   (θ:=(174954253/200000000:ℝ)) (by norm_num) _ χ s hs hpole
 convert family_beta input using 1 <;> norm_num [DasStageBFinite.theta,DasStageBFinite.c]
end
end Das.QRH.Endpoint
#print axioms Das.QRH.Endpoint.first_family_beta
#print axioms Das.QRH.Endpoint.family_beta
#print axioms Das.QRH.Endpoint.dirichlet_nonvanishing
