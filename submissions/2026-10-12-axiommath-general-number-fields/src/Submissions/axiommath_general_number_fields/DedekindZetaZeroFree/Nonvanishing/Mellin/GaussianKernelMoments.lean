/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Nonvanishing/Mellin/GaussianKernelMoments.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.ConstantTerms.ResidualRadialCovariance
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Profiles.GaussianSmoothing

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem mellin_gaussian (R : PrincipalMellin.ActualRecipe S η)
    (N : TraceHaarTransport R) (prior : Nonempty (JointResidualConstantTermSources R N)) : Nonempty (JointMellinGaussianSources R N) := by
  obtain ⟨C⟩ := prior
  exact ⟨{ toJointResidualConstantTermSources := C, mellin := GaussianSmoothing.mellinGaussian C.transport C.packet }⟩

end DedekindZetaZeroFree.ThetaExpansion
