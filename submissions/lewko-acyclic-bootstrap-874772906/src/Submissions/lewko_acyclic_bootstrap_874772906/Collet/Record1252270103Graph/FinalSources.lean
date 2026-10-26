/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.FiniteInduction
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.SeedSources
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record12518109Existence

theorem final_natural_cap (seed:SeedStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) :
 6*(2*HeckeZeroSupremum.beta-1)≤ finalK := by
 have hi := beta_intermediate_of_seed_step seed hbeta
 norm_num [finalK]
 linarith

theorem final_selected_sources (seed:SeedStep) (step:NFStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) : P source300 ∧ P source301 := by
 have hk := final_natural_cap seed hbeta
 have hn:P natural := by
  simpa [P,natural,finalK] using natural_global_source finalK
   (by norm_num [finalK]) (by norm_num [finalK]) hbeta hk
 have hg:ParentGood natural := by norm_num [ParentGood,natural]
 have h := selected_sources_from_accounted_rules (fun s=>ParentGood s ∧ P s) ⟨hg,hn⟩
  (fun n low high hv ha hl hh=>⟨parent_good_of_source_valid hv,
   step n low high hbeta hk hv hl.1 ha hl.2 (fun h hh'=> (hh h hh').2)⟩)
 exact ⟨h.1.2,h.2.2⟩

lemma final_C_face :
 Record1252270103Source.globalFace (source300.B:ℝ) (source300.L:ℝ) (source300.cap:ℝ)=
 Record1252270103Return.countGlobal := by
 norm_num [Record1252270103Source.globalFace,source300,
  Record1252270103Return.countGlobal,Record1252270103Return.globalFace,countCB,countCL]
lemma final_P_face :
 Record1252270103Source.globalFace (source301.B:ℝ) (source301.L:ℝ) (source301.cap:ℝ)=
 Record1252270103Return.physicalGlobal := by
 norm_num [Record1252270103Source.globalFace,source301,
  Record1252270103Return.physicalGlobal,Record1252270103Return.globalFace,physicalB,physicalLambda]

theorem final_global_suppliers (seed:SeedStep) (step:NFStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) :
 UniformUnitFaceSource Record1252270103Return.countGlobal ∧
 UniformUnitFaceSource Record1252270103Return.physicalGlobal := by
 obtain ⟨hC,hP⟩ := final_selected_sources seed step hbeta
 change UniformUnitFaceSource _ at hC hP
 rw [final_C_face] at hC
 rw [final_P_face] at hP
 exact ⟨hC,hP⟩
end
end QRH.Record1252270103Graph
#print axioms QRH.Record1252270103Graph.final_selected_sources
#print axioms QRH.Record1252270103Graph.final_global_suppliers
