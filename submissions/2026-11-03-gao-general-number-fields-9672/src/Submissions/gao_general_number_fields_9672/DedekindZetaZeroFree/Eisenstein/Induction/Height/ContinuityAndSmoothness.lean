/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/Height/ContinuityAndSmoothness.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.CompactIwasawaGeometry
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.Height.IwasawaRegularity

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField
namespace DedekindZetaZeroFree.HeightGeometry
open ThetaExpansion MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem height_continuous (R : PrincipalMellin.ActualRecipe S η) : Continuous (iwasawaLogHeight R) :=
  logModulus_continuous F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R)

theorem height_right_chart_smooth (R : PrincipalMellin.ActualRecipe S η) (g : Group R) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => iwasawaLogHeight R (g * KPGlobalResidualConstruction.archChart
        F R.A.zeta12 R.A.primitive_zeta12 z)) (KPGlobalResidualConstruction.archDomain F) :=
  logModulus_right_chart_smooth F R.A.zeta12 R.A.primitive_zeta12
    (fullProductIwasawaData R) (complex_compact_lift_mem_full_product_compact R) g
end DedekindZetaZeroFree.HeightGeometry

end
