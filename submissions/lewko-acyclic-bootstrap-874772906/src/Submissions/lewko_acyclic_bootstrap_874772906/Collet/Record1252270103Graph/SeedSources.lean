/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Graph.Natural
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedConnections
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Return.EndpointFromGlobalSources
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record12518109Existence

lemma seed_natural_cap : 6*(2*HeckeZeroSupremum.beta-1)≤ seedK := by
 have h := Record1252270103Return.initial_natural_cap
 norm_num [seedK,Record1252270103Return.C30.naturalK] at *
 linarith

theorem seed_selected_sources (step:SeedStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) : P seedSource64 ∧ P seedSource63 := by
 have hn:P seedNatural := by
  simpa [P,seedNatural,seedK] using natural_global_source seedK
   (by norm_num [seedK]) (by norm_num [seedK]) hbeta seed_natural_cap
 have hg:ParentGood seedNatural := by norm_num [ParentGood,seedNatural]
 have h := selected_seed_sources_from_finite_rules (fun s=>ParentGood s ∧ P s) ⟨hg,hn⟩
  (fun n low hv hl=>⟨parent_good_of_seed_valid hv,step n low hbeta seed_natural_cap hv hl.1 hl.2⟩)
 exact ⟨h.1.2,h.2.2⟩

lemma seed_C_face :
 Record1252270103Source.globalFace (seedSource64.B:ℝ) (seedSource64.L:ℝ) (seedSource64.cap:ℝ)=
 Record1252270103Return.IntermediateCount.countGlobal := by
 norm_num [Record1252270103Source.globalFace,seedSource64,
  Record1252270103Return.IntermediateCount.countGlobal,Record1252270103Return.globalFace,
  Record1252270103Return.C30.countCB,Record1252270103Return.C30.countCL]
lemma seed_P_face :
 Record1252270103Source.globalFace (seedSource63.B:ℝ) (seedSource63.L:ℝ) (seedSource63.cap:ℝ)=
 Record1252270103Return.IntermediateCount.physicalGlobal := by
 norm_num [Record1252270103Source.globalFace,seedSource63,
  Record1252270103Return.IntermediateCount.physicalGlobal,Record1252270103Return.globalFace,
  Record1252270103Return.C30.physicalB,Record1252270103Return.C30.physicalLambda]

theorem seed_global_suppliers (step:SeedStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) :
 UniformUnitFaceSource Record1252270103Return.IntermediateCount.countGlobal ∧
 UniformUnitFaceSource Record1252270103Return.IntermediateCount.physicalGlobal := by
 obtain ⟨hC,hP⟩ := seed_selected_sources step hbeta
 change UniformUnitFaceSource _ at hC hP
 rw [seed_C_face] at hC
 rw [seed_P_face] at hP
 exact ⟨hC,hP⟩

theorem beta_intermediate_of_seed_step (step:SeedStep)
 (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta) :
 HeckeZeroSupremum.beta≤(8747759/10000000:ℝ) := by
 obtain ⟨hC,hP⟩ := seed_global_suppliers step hbeta
 exact Record1252270103Return.Intermediate.beta_of_global_sources hC hP
  Record1252270103Return.initial_natural_cap
end
end QRH.Record1252270103Graph
#print axioms QRH.Record1252270103Graph.seed_selected_sources
#print axioms QRH.Record1252270103Graph.beta_intermediate_of_seed_step
