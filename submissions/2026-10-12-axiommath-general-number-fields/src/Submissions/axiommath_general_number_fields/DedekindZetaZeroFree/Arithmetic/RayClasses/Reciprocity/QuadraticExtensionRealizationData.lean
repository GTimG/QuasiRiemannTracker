/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Reciprocity/QuadraticExtensionRealizationData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

namespace DedekindZetaZeroFree.LargeSieve

structure QuadraticRayExtensionData
    {F : Type} [Field F] [NumberField F] {f : Ideal (𝓞 F)}
    (η : DedekindZetaZeroFree.RayClassCharacter F f) where
  extension : ClassFieldTheory.FiniteAbelianExtension F
  character : (extension ≃ₐ[F] extension) →* ℂˣ
  degree_two : Module.finrank F extension = 2
  character_injective : Function.Injective character
  character_square : ∀ σ, character σ ^ 2 = 1
  unramified : ∀ p : HeightOneSpectrum (𝓞 F),
    p.asIdeal ⊔ f = ⊤ → Algebra.IsUnramifiedIn (𝓞 extension) p.asIdeal
  frobenius : ∀ (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal ⊔ f = ⊤)
    (Q : HeightOneSpectrum (𝓞 extension)), Q.asIdeal.LiesOver p.asIdeal →
      (character (ClassFieldTheory.arithmeticFrobeniusAt (K := F) Q) : ℂ) =
        η p.asIdeal

end DedekindZetaZeroFree.LargeSieve
