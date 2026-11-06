/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Moduli/FinitePrimeProduct.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ModulusIdeal

@[expose] public section

namespace DedekindZetaZeroFree.KummerConductorProduct
noncomputable section
open scoped NumberField Classical
open IsDedekindDomain

theorem modulus_eq (F : Type) [Field F] [NumberField F]
    (hc : NumberField.IsTotallyComplex F) (c : ClassFieldTheory.RayClassModulus F) :
    M F (PrimitiveRay.modulusIdeal c.finitePart)
      (PrimitiveRay.modulusIdeal_ne_bot _) = c := by
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (hc.isComplex v.val)) v.property⟩
  apply ClassFieldTheory.RayClassModulus.ext
  · exact PrimitiveRay.modulusIdeal_M _
  · exact Subsingleton.elim _ _

end
end DedekindZetaZeroFree.KummerConductorProduct
