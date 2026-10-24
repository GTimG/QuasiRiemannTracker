/- Candidate assembled 2026-10-23.
Uses only the accepted PR69 endpoint/source step and newly certified finite data.
Full analytic endpoint compilation is pending; no axiom or sorry is introduced.
Return interfaces: Hailey Collet and Mark Lewko, Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.Recost.Accounted
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.EndpointFromSources
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Endpoint
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace QRH.RH20261023.Endpoint
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open QRH.Record1252270103Graph QRH.Record12518109Existence

theorem accepted_natural_cost :
  6*(2*HeckeZeroSupremum.beta-1) ≤ (11243189691/2500000000:ℝ) := by
  have hb := QRH.Record1252270103Source.Endpoint.beta_bound
  linarith

theorem internal_cost : 6*(2*HeckeZeroSupremum.beta-1) ≤ finalK := by
  have hb := accepted_natural_cost
  norm_num [finalK]
  linarith

theorem final_moment_cap :
  2*HeckeZeroSupremum.beta-1 ≤ RH20261023Finite.naturalK/6 := by
  have hb := accepted_natural_cost
  norm_num [RH20261023Finite.naturalK]
  linarith

theorem global_suppliers (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
  UniformUnitFaceSource QRH.RH20261023Return.countGlobal ∧
  UniformUnitFaceSource QRH.RH20261023Return.physicalGlobal := by
  have hn : P AcceptedRecost.source000 := by
    simpa [P,AcceptedRecost.source000] using
      natural_global_source (11243189691/2500000000:ℝ)
        (by norm_num) (by norm_num) hbeta accepted_natural_cost
  have hg : ParentGood AcceptedRecost.source000 := by
    norm_num [ParentGood,AcceptedRecost.source000]
  have h := AcceptedRecost.selected_sources_from_accounted_rules
    (fun s => ParentGood s ∧ P s) ⟨hg,hn⟩
    (fun n low high hv ha hl hh => ⟨parent_good_of_source_valid hv,
      QRH.Record1252270103Source.Endpoint.nf_step n low high hbeta internal_cost
        hv hl.1 (Or.inr ha) hl.2 (fun h hh' => (hh h hh').2)⟩)
  have hC := h.1.2
  have hP := h.2.2
  change UniformUnitFaceSource _ at hC hP
  constructor
  · convert hC using 1 <;>
      norm_num [QRH.Record1252270103Source.globalFace,AcceptedRecost.source300,
        QRH.RH20261023Return.countGlobal,QRH.RH20261023Return.globalFace,
        RH20261023Finite.countCB,RH20261023Finite.countCL]
  · convert hP using 1 <;>
      norm_num [QRH.Record1252270103Source.globalFace,AcceptedRecost.source301,
        QRH.RH20261023Return.physicalGlobal,QRH.RH20261023Return.globalFace,
        RH20261023Finite.physicalB,RH20261023Finite.physicalLambda]

theorem family_beta :
  HeckeZeroSupremum.beta ≤ (21869322649/25000000000:ℝ) := by
  by_cases hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta
  · obtain ⟨hC,hP⟩ := global_suppliers hb
    have h := QRH.RH20261023Return.Final.beta_of_global_sources hC hP final_moment_cap
    convert h using 1 <;> norm_num [RH20261023Finite.theta,RH20261023Finite.c]
  · have h := (not_le.mp hb).le
    linarith

theorem hecke_nonvanishing (χ : Character) (s : ℂ)
  (hs : (21869322649/25000000000:ℝ) < s.re)
  (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (family_beta.trans_lt hs) hpole

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
  (χ : DirichletCharacter ℂ q) {s : ℂ}
  (hs : (21869322649/25000000000:ℝ) < s.re)
  (hpole : ¬ (χ = 1 ∧ s = 1)) :
  _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  Cycle25.dirichlet_of_hecke (by norm_num) hecke_nonvanishing χ s hs hpole

theorem zeta_nonvanishing (s : ℂ)
  (hs : (21869322649/25000000000:ℝ) < s.re) (_hpole : s ≠ 1) :
  riemannZeta s ≠ 0 :=
  Cycle25.zeta_of_hecke (by norm_num) hecke_nonvanishing s hs

end
end QRH.RH20261023.Endpoint
#print axioms QRH.RH20261023.Endpoint.accepted_natural_cost
#print axioms QRH.RH20261023.Endpoint.internal_cost
#print axioms QRH.RH20261023.Endpoint.final_moment_cap
#print axioms QRH.RH20261023.Endpoint.global_suppliers
#print axioms QRH.RH20261023.Endpoint.family_beta
#print axioms QRH.RH20261023.Endpoint.hecke_nonvanishing
#print axioms QRH.RH20261023.Endpoint.dirichlet_nonvanishing
#print axioms QRH.RH20261023.Endpoint.zeta_nonvanishing
