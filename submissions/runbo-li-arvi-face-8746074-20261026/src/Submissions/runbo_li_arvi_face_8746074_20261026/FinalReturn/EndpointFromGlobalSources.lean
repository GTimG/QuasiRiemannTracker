/- Repeated marks: fork of Collet's final-stage module EndpointFromGlobalSources (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FinalReturn.EndpointFromSources
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.Incumbent
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Existence
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

lemma initial_natural_cap :
 2*HeckeZeroSupremum.beta-1≤Record1252270103Return.C30.naturalK/6 := by
 have hi := QRH.Record1252270103Bootstrap.incumbent_beta
 norm_num [Record1252270103Return.C30.naturalK]
 linarith

theorem beta_of_four_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal) :
 HeckeZeroSupremum.beta≤QRH.RepeatedMarks.Return.theta :=
 beta_from_two_stage_global_sources hC29C hC29P hC hP initial_natural_cap

theorem hecke_of_four_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (χ:Character) (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 :=
 hecke_from_two_stage_global_sources hC29C hC29P hC hP initial_natural_cap χ s hs hpole

theorem dirichlet_of_four_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 {q:ℕ} [NeZero q] (χ:DirichletCharacter ℂ q) (s:ℂ)
 (hs:QRH.RepeatedMarks.Return.theta<s.re) (hpole:¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 dirichlet_from_two_stage_global_sources hC29C hC29P hC hP initial_natural_cap χ s hs hpole

theorem zeta_of_four_global_sources
 (hC29C:UniformUnitFaceSource IntermediateCount.countGlobal)
 (hC29P:UniformUnitFaceSource IntermediateCount.physicalGlobal)
 (hC:UniformUnitFaceSource countGlobal) (hP:UniformUnitFaceSource physicalGlobal)
 (s:ℂ) (hs:QRH.RepeatedMarks.Return.theta<s.re) : riemannZeta s≠0 :=
 zeta_from_two_stage_global_sources hC29C hC29P hC hP initial_natural_cap s hs
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.initial_natural_cap
#print axioms QRH.RepeatedMarks.Return.beta_of_four_global_sources
#print axioms QRH.RepeatedMarks.Return.hecke_of_four_global_sources
#print axioms QRH.RepeatedMarks.Return.dirichlet_of_four_global_sources
#print axioms QRH.RepeatedMarks.Return.zeta_of_four_global_sources
