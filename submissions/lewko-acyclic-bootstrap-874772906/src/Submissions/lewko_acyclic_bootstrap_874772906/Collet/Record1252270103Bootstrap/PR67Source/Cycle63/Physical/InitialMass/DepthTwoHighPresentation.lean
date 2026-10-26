import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.DepthTwoHighWitness
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoPresented
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The data of a presentation of a state of the second step by a child multiplier, as a structure, and the units of the
dictionary of the state's own character. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentNaturalRowSource CenteredMomentEnergyState
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open IdealMobiusDivisorSum

/-- The data of a presentation of a state with character `η` and puncture `R` in the four-ray dictionary of `η₀`:
the character `η` is the second-stage character `τ₁ j₁.2` of a first-level child, whose character `χ₁` is, off its
modulus, a natural row of the child character of `η₀` at the row `w₁`; the ideals coprime to `R` are coprime to the first
common ideal `C₁`. -/
structure DepthTwoPresentation (η₀ η : Character) (R : Ideal O) where
  j₁ : RayCharacter × RayCharacter
  χ₁ : Character
  w₁ : O
  first₁ : NaturalRow (childCharacter η₀ j₁.1) w₁
  hfirst₁ : ∀ I : Ideal O, idealCoeff χ₁ I = if IsCoprime I χ₁.modulus then idealCoeff first₁.character I else 0
  C₁ : Ideal O
  D₁ : Ideal O
  hC₁ : Supported C₁
  hD₁ : Supported D₁
  hCD₁ : primeSupport C₁ = primeSupport D₁
  U₁ : Finset (CommonIndex C₁ D₁)
  τ₁ : RayCharacter → Character
  hf₁ : Family χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁
  hv : w₁*(commonFrequencyGenerator C₁ D₁*nonunitFrequencyGenerator C₁ D₁ U₁) ≠ 0
  hη : η = τ₁ j₁.2
  hcop : ∀ I : Ideal O, IsCoprime I R → IsCoprime I C₁

namespace DepthTwoPresentation
variable {η₀ η : Character} {R : Ideal O} (P : DepthTwoPresentation η₀ η R)

/-- The child multiplier of a presentation. -/
def mult : O := P.w₁*(commonFrequencyGenerator P.C₁ P.D₁*nonunitFrequencyGenerator P.C₁ P.D₁ P.U₁)

/-- The natural row of the state's character at the row `1`. -/
def selfRow : NaturalRow (P.τ₁ P.j₁.2) 1 :=
  selfNaturalRow (P.τ₁ P.j₁.2) (family_element_supported P.χ₁ P.C₁ P.D₁ P.hC₁ P.hD₁ P.U₁ P.τ₁ P.hf₁ P.j₁.2)

/-- The units of the dictionary of the state's character for the orientation `left`. -/
def unit (left : Bool) : FirstSourceLabel → O :=
  fun l => (firstDictionaryUnit left (P.τ₁ P.j₁.2) 1 P.selfRow 1 l : O)

theorem mult_ne_zero : P.mult ≠ 0 := P.hv

end DepthTwoPresentation

/-- A presented state has the data of a presentation, and its child multiplier is the multiplier of the data. -/
theorem DepthTwoPresented.presentation {τT Bmask bΦ Z T : ℝ} {η₀ : Character} {s : NaturalState Z Bmask bΦ} {v₁ : O}
    (h : DepthTwoPresented τT η₀ Z s v₁ T) :
    ∃ P : DepthTwoPresentation η₀ s.character s.puncture, v₁ = P.mult := by
  obtain ⟨-, j₁, χ₁, w₁, C₁, D₁, hC₁, hD₁, U₁, τ₁, ⟨first₁, hfirst₁⟩, hCD₁, hf₁, hv, hv0, hchar, hcop⟩ := h
  refine ⟨⟨j₁, χ₁, w₁, first₁, hfirst₁, C₁, D₁, hC₁, hD₁, hCD₁, U₁, τ₁, hf₁, hv ▸ hv0, hchar, hcop⟩, hv⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
