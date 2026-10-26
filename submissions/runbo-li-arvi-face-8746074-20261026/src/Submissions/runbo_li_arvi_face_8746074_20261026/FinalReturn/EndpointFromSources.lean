/- Repeated marks: fork of Collet's final-stage module EndpointFromSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.FinalSchedule
import Submissions.hailey_collet_1252270103.Record1252270103Return.IntermediateCount.Schedule
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.PhysicalDirect.ChosenSource
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.EndpointFromNumerator
import Submissions.hailey_collet_1252270103.Record1252270103Return.EndpointFromSources
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsR := Geometry.finalBounds
local instance : CountScheme := finalCountScheme
local instance : GenericArithmetic.PhysicalSchedule := finalPhysicalSchedule

theorem literal_numerator_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6) : LiteralNumeratorInput := by
 have hc : ∀ε:ℝ,0<ε → ∃mesh:ℝ,0< mesh ∧
   ∀w∈finalCountScheme.windows,UnitFaceSource w.face mesh ε := by
  intro ε hε
  obtain ⟨mesh,hm,_,hw⟩ := final_windows_common_mesh hC hP hε
  exact ⟨mesh,hm,hw⟩
 have hr : physicalGlobal.Restricts GenericPhysical.PhysicalDirect.physicalFace := by
  change physicalGlobal.Restricts
   ⟨QRH.RepeatedMarks.Return.physicalB,QRH.RepeatedMarks.Return.physicalLambda,0,1/2,0,9/200⟩
  constructor <;> norm_num [physicalGlobal,QRH.Record1252270103Return.globalFace,
   QRH.RepeatedMarks.Return.physicalB]
 have hp : UniformUnitFaceSource GenericPhysical.PhysicalDirect.physicalFace := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := hP ε hε
  exact ⟨mesh,hm,unit_source_restrict hr hs⟩
 exact GenericPhysical.PhysicalDirect.chosen_finite_numerator_of_initial_source
  (GenericPhysical.PhysicalDirect.chosen_initial_source_of_uniform_faces hcap hc hp)

theorem beta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta :=
 beta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap)

theorem hecke_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6)
 (χ:Character) (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 :=
 hecke_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem dirichlet_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 dirichlet_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) χ s hs hpole

theorem zeta_of_global_sources
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hcap:2*HeckeZeroSupremum.beta-1≤QRH.RepeatedMarks.Return.naturalK/6)
 (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) : riemannZeta s≠0 :=
 zeta_of_literal_numerator (literal_numerator_of_global_sources hC hP hcap) s hs
end Final

theorem beta_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤Record1252270103Return.C30.naturalK/6) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta := by
 have hi := Intermediate.beta_of_global_sources hC29C hC29P hbootstrap
 apply Final.beta_of_global_sources hC hP
 norm_num [QRH.RepeatedMarks.Return.naturalK]
 linarith

theorem hecke_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤Record1252270103Return.C30.naturalK/6)
 (χ:Character) (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap).trans_lt hs) hpole

theorem dirichlet_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤Record1252270103Return.C30.naturalK/6)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
 (hecke_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap) χ s hs hpole

theorem zeta_from_two_stage_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (hbootstrap:2*HeckeZeroSupremum.beta-1≤Record1252270103Return.C30.naturalK/6)
 (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [QRH.RepeatedMarks.Return.theta,QRH.RepeatedMarks.Return.c])
 (hecke_from_two_stage_global_sources hC29C hC29P hC hP hbootstrap) s hs
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.Final.literal_numerator_of_global_sources
#print axioms QRH.RepeatedMarks.Return.beta_from_two_stage_global_sources
#print axioms QRH.RepeatedMarks.Return.Final.hecke_of_global_sources
#print axioms QRH.RepeatedMarks.Return.Final.dirichlet_of_global_sources
#print axioms QRH.RepeatedMarks.Return.Final.zeta_of_global_sources

#print axioms QRH.RepeatedMarks.Return.hecke_from_two_stage_global_sources

#print axioms QRH.RepeatedMarks.Return.dirichlet_from_two_stage_global_sources

#print axioms QRH.RepeatedMarks.Return.zeta_from_two_stage_global_sources
