/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Kubota/BorelAndSignedWeylLifts.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPForwardHomRepair

open scoped NumberField
open NumberField IsDedekindDomain
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem canonicalUpperRoot_eq (P : Polarization S.heisenberg)
    (x : LocalField F q) :
    (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) =
      KPRankOneOpenCellKernel.nLift F ζ hζ q x :=
  (S.openCell P).upper_eq x

theorem canonicalSignedWeyl_eq (P : Polarization S.heisenberg) :
    S.borel.liftedW = KPRankOneOpenCellKernel.signedWeyl F ζ hζ q :=
  (S.openCell P).weyl_eq

end DedekindZetaZeroFree.KPForwardHomRepair

end
