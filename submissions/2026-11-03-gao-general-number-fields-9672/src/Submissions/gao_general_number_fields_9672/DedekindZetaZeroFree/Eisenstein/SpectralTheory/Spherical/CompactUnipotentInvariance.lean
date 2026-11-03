/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/Spherical/CompactUnipotentInvariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarRealization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem originalScalar_KU_fixed (Z : smoothSections F ζ hζ V R P H)
    (k : K_U F ζ hζ V) (x : KPSmoothActualFlowData.X F ζ hζ) :
    originalScalar F ζ hζ V R P H Z
      (KPSmoothActualFlowData.rightTranslate F ζ hζ k.val x) =
      originalScalar F ζ hζ V R P H Z x := by
  induction x using Quotient.inductionOn with
  | h g =>
    change ((smoothS F ζ hζ V R P H).symm Z).val.val
      (KPContSectorQuotientRelationsComparison.e F ζ hζ V
        (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ V) (g*k.val))) =
      ((smoothS F ζ hζ V R P H).symm Z).val.val
        (KPContSectorQuotientRelationsComparison.e F ζ hζ V
          (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ V) g))
    rw [DoubleCoset.mk_mul_mem k g]

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalGeometry

end
