/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/ArchimedeanRootDerivatives.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.FirstRootSphericalRadialModel

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def firstRootLocalDerivative (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) (e : ℤ) (f : Functions R) : Functions R :=
  (Complex.I * (4 * Real.pi : ℂ))⁻¹ •
    (upperLieDerivative R w false f +
      (if e = 1 then -Complex.I else Complex.I) • upperLieDerivative R w true f)

def firstRootDerivatives (R : PrincipalMellin.ActualRecipe S η)
    (B : FirstRootCutoffs R) (f : Functions R) : Functions R :=
  (Finset.univ : Finset (InfinitePlace F)).toList.foldr
    (fun w h => firstRootLocalDerivative R w (B.exponent w) h) f

end DedekindZetaZeroFree.ThetaExpansion

end
