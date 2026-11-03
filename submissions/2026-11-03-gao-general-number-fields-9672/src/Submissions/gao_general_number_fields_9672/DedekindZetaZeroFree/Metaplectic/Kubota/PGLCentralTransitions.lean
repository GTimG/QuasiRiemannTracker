/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Kubota/PGLCentralTransitions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules

@[expose] public section

namespace DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ClopenGluing

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

theorem ordinaryPGLMap_injective
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F v) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr v)
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr v)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr v))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr v))
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  induction g using QuotientGroup.induction_on with
  | _ a =>
    apply (QuotientGroup.eq_one_iff _).mpr
    have ha : a ∈ Subgroup.center (KPLocalCover.LocalGL2 F (Sum.inr v)) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at ha
    exact ha

end
end DedekindZetaZeroFree.KPWildCompactProjectorKirillov.ClopenGluing
