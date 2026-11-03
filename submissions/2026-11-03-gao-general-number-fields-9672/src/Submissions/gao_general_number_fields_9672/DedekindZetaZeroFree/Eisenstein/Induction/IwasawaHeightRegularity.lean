/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/IwasawaHeightRegularity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.Height.ContinuityAndSmoothness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem iwasawa_log_height_regular (R : PrincipalMellin.ActualRecipe S η) :
    Continuous (iwasawaLogHeight R) ∧
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => iwasawaLogHeight R (g * KPGlobalResidualConstruction.archChart
        F R.A.zeta12 R.A.primitive_zeta12 x))
      (KPGlobalResidualConstruction.archDomain F) := by
  exact ⟨HeightGeometry.height_continuous R,
    HeightGeometry.height_right_chart_smooth R⟩

end DedekindZetaZeroFree.ThetaExpansion

end
