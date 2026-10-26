/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine global energy suppliers remain explicit. The intermediate return
supplies the independent natural moment cap used by the final return. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.FinalSchedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.IntermediateCount.Schedule
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.PhysicalDirect.ChosenSource
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.EndpointFromNumerator
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.Bounds := Geometry.finalBounds
local instance : CountScheme := finalCountScheme
local instance : GenericArithmetic.PhysicalSchedule := finalPhysicalSchedule

theorem literal_numerator_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Finite.naturalK/6) : LiteralNumeratorInput := by
 have hc : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧
   ∀w∈finalCountScheme.windows,UnitFaceSource w.face mesh ε := by
  intro ε hε
  obtain ⟨mesh,hm,_,hw⟩ := final_windows_common_mesh hC hP hε
  exact ⟨mesh,hm,hw⟩
 have hr : physicalWindow.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalWindow.Restricts
   ⟨RH20261023Finite.physicalB,RH20261023Finite.physicalLambda,2/5,11/25,17/500,1/25⟩
  constructor <;> norm_num [physicalWindow]
 have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hP ε hε
  exact ⟨mesh,hm,unit_source_restrict hr (unit_source_restrict physical_restricts hs)⟩
 exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
  (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc hp)

theorem beta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Finite.naturalK/6) :
 HeckeZeroSupremum.beta≤RH20261023Finite.theta :=
 beta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap)

theorem hecke_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Finite.naturalK/6)
 (χ:Character) (s:ℂ) (hs:RH20261023Finite.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 :=
 hecke_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem dirichlet_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Finite.naturalK/6)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:RH20261023Finite.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 dirichlet_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem zeta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Finite.naturalK/6)
 (s:ℂ) (hs:RH20261023Finite.theta<s.re) : riemannZeta s≠0 :=
 zeta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) s hs
end Final
namespace Intermediate
local instance : Geometry.Parameters := Geometry.intermediateParameters
local instance : Geometry.Bounds := Geometry.intermediateBounds
local instance : CountScheme := IntermediateCount.countScheme
local instance : GenericArithmetic.PhysicalSchedule := IntermediateCount.physicalSchedule

theorem literal_numerator_of_global_sources
 (hC:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hP:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6) : LiteralNumeratorInput := by
 have hc : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧
   ∀w∈IntermediateCount.countScheme.windows,UnitFaceSource w.face mesh ε := by
  intro ε hε
  obtain ⟨mesh,hm,_,hw⟩ := IntermediateCount.windows_common_mesh hC hP hε
  exact ⟨mesh,hm,hw⟩
 have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
  change UniformUnitFaceSource IntermediateCount.physicalWindow
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hP ε hε
  exact ⟨mesh,hm,unit_source_restrict IntermediateCount.physical_restricts hs⟩
 exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
  (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc hp)

theorem beta_of_global_sources
 (hC:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hP:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6) :
 HeckeZeroSupremum.beta≤(8747759/10000000:ℝ) :=
 beta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap)
end Intermediate

theorem beta_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6) :
 HeckeZeroSupremum.beta≤RH20261023Finite.theta := by
 have hi := Intermediate.beta_of_global_sources hC29C hC29P hbootstrap
 apply Final.beta_of_global_sources hC hP
 norm_num [RH20261023Finite.naturalK]
 linarith

theorem hecke_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6)
 (χ:Character) (s:ℂ) (hs:RH20261023Finite.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap).trans_lt hs) hpole

theorem dirichlet_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:RH20261023Finite.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [RH20261023Finite.theta,RH20261023Finite.c])
 (hecke_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap) χ s hs hpole

theorem zeta_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤RH20261023Return.C30.naturalK/6)
 (s:ℂ) (hs:RH20261023Finite.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [RH20261023Finite.theta,RH20261023Finite.c])
 (hecke_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap) s hs
end
end QRH.RH20261023Return
#print axioms QRH.RH20261023Return.Final.literal_numerator_of_global_sources
#print axioms QRH.RH20261023Return.Intermediate.literal_numerator_of_global_sources
#print axioms QRH.RH20261023Return.beta_from_two_stage_global_sources
#print axioms QRH.RH20261023Return.Final.hecke_of_global_sources
#print axioms QRH.RH20261023Return.Final.dirichlet_of_global_sources
#print axioms QRH.RH20261023Return.Final.zeta_of_global_sources

#print axioms QRH.RH20261023Return.hecke_from_two_stage_global_sources

#print axioms QRH.RH20261023Return.dirichlet_from_two_stage_global_sources

#print axioms QRH.RH20261023Return.zeta_from_two_stage_global_sources
