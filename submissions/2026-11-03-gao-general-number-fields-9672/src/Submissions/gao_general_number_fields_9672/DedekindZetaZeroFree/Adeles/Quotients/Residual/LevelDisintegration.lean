/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/Residual/LevelDisintegration.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.ScalarFiniteLevelTransport

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualNativeLevel
universe u v

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem atlasLevel_eq (S : KPMsAngularSourceRecipe.OffsetSourceRecipe F ζ hζ R P H)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    S.atlasLevel U = EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U := by
  have hm := S.level_matching U
  rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U] at hm
  have hopen := OpenSubgroup.toSubgroup_injective
    (Subgroup.map_injective (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype_injective hm.symm)
  generalize h₁ : S.atlasLevel U = X at hopen ⊢
  generalize h₂ : EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U = Y at hopen ⊢
  cases X
  cases Y
  congr

end DedekindZetaZeroFree.FourierContinuation.ResidualNativeLevel

end
