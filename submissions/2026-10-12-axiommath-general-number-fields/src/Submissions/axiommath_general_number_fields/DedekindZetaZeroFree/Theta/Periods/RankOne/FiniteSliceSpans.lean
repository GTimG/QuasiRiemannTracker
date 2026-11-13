/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/RankOne/FiniteSliceSpans.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.Sources.LocalLineExistence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorFiniteLines_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorSpherical R N)) :
    Nonempty (TensorFiniteLines R N) := by
  obtain ⟨D⟩ := FourierContinuation.LiteralSource.current_local_lines_nonempty  R hR N
  exact ⟨D.toTensorFiniteLines⟩
end DedekindZetaZeroFree.ThetaExpansion

end
