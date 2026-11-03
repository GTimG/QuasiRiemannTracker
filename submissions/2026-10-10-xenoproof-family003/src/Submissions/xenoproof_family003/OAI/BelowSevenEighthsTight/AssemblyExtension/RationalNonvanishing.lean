import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.AssemblyExtension.CommonProbeFromMoments
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedHighDataFine
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.FinalAssemblyCertifiedMoments

/- Prepared final assembly. This file is NOT a verified result until its
   capacity/moment dependencies and this file have compiled and been replayed. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.Results
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily
open BelowSevenEighthsTight.Parameters BelowSevenEighthsTight.FiberExtension
open ProbeFinalAssemblyCertifiedBands

theorem rational_uniform_common_probe : RetunedUniformCommonProbe sigmaRat := by
  intro hβ
  have hΔ : 0<HeckeZeroSupremum.beta-sigmaRat := sub_pos.mpr hβ
  obtain ⟨D,hfine,_⟩ := exists_retuned_high_data_fine
    (HeckeZeroSupremum.beta-sigmaRat) ellRat (1/1000000000000000) (1/32)
    hΔ (by norm_num [ellRat]) (by norm_num) (by norm_num) (by norm_num [ellRat])
    (detectorMesh_retuned (HeckeZeroSupremum.beta-sigmaRat))
    (fun t ht=>detectorMesh_pos_retuned hΔ ht)
  obtain ⟨F⟩ := exists_retuned_source_data D
  obtain ⟨counts⟩ := exists_retuned_count_parameters F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2) D.t D.t_pos
  exact rational_contract_of_source_moments hβ D F counts
    (source_moments_from_capacity_retuned hβ D F counts hfine)

theorem beta_le_rational_boundary : HeckeZeroSupremum.beta≤sigmaRat :=
  beta_le_of_retuned_contract sigmaRat (by norm_num [sigmaRat])
    (by norm_num [sigmaRat]) rational_uniform_common_probe

theorem hecke_nonvanishing (χ : Character) (s : ℂ) (hs : sigmaRat<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  rational_hecke_nonzero_of_contract rational_uniform_common_probe χ s hs hpole

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : sigmaRat<s.re) (hpole : ¬(χ=1 ∧ s=1)) :
    _root_.DirichletCharacter.LFunction χ s≠0 :=
  rational_dirichlet_nonzero_of_contract rational_uniform_common_probe χ s hs hpole

theorem zeta_nonvanishing (s : ℂ) (hs : sigmaRat<s.re) : riemannZeta s≠0 :=
  rational_zeta_nonzero_of_contract rational_uniform_common_probe s hs

#print axioms rational_uniform_common_probe
#print axioms beta_le_rational_boundary
#print axioms hecke_nonvanishing
#print axioms dirichlet_nonvanishing
#print axioms zeta_nonvanishing
end
end BelowSevenEighthsTight.Results
