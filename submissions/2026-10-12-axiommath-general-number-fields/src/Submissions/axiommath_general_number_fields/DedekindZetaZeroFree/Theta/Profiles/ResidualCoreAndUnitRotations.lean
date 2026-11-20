/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Profiles/ResidualCoreAndUnitRotations.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped NumberField Classical
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction
namespace ElementaryOutputs

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalSplitting : RationalSplitting F ζ hζ where
  lift := QuotientGroup.lift (Subgroup.center (KubotaRankTwo.GL2 F))
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)) (by
        simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar,
          KPRationalAdelicSplitting.rationalScalars] using
          KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ)
  on_matrix := by intro g; rfl

end ElementaryOutputs
end DedekindZetaZeroFree.KPGlobalResidualConstruction

end
