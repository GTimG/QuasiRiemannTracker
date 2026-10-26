/- A physical source presentation that is closed under finite LOW continuation.
Its masked-row identity is constructed by MaskedPrefixPresentation.advance. -/
import Candidate.Research.RecursiveAffine.MaskedPrefixHighWitness
import Candidate.Cycle63.Moment.DepthTwoCount
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentChildRows
open CenteredMomentEnergyState IdealMobiusDivisorSum

structure PrefixHighPresentation {Base : Type} (base : Base → Character)
    (η : Character) (R : Ideal O) where
  mult : O
  masked : MaskedPrefixPresentation base η R mult
  supported : ∀ z, elementCoeff η z ≠ 0 → Supported (Ideal.span {z})

namespace PrefixHighPresentation
variable {Base : Type} {base : Base → Character} {η : Character} {R : Ideal O}
    (P : PrefixHighPresentation base η R)
def selfRow : NaturalRow η 1 := selfNaturalRow η P.supported
theorem hv : P.mult ≠ 0 := P.masked.multiplier_ne_zero
/-- The next continuing source keeps the actual Family character and the literal
accumulated multiplier. All supported-source facts are supplied by that same Family. -/
def advance (j : RayCharacter × RayCharacter) (χ : Character) (w : O)
    (first : NaturalRow (childCharacter η j.1) w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D)
    (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character)
    (hf : CenteredMomentSecondExceptionalFamily.Family χ C D hC hD U τ)
    (hw : localSourceMultiplier w C D U ≠ 0)
    (Q : Ideal O) (hQ : Q ≠ 0) (hRQ : R ∣ χ.modulus*Q)
    (hcop : ∀ I : Ideal O, IsCoprime I Q → IsCoprime I C) :
    PrefixHighPresentation (extendFixedDictionary base) (τ j.2) Q where
  mult := P.mult*localSourceMultiplier w C D U
  masked := P.masked.advance j χ w first hfirst C D hC hD hCD U τ hf hw Q hQ hRQ hcop
  supported := family_element_supported χ C D hC hD U τ hf j.2

end PrefixHighPresentation

/-- At a normalized actual state, retain the literal masked prefix presentation and
its exact height. Continuing source rebase/widening leaves the presentation untouched. -/
def PrefixHighPresented {Base : Type} (base : Base → Character) (τT : ℝ)
    {Bmask bΦ : ℝ} (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v : O) (T : ℝ) : Prop :=
  (Z^τT ≤ T ∧ T ≤ Z^τT) ∧ ∃ P : PrefixHighPresentation base s.character s.puncture, v = P.mult

theorem PrefixHighPresented.presentation {Base : Type} {base : Base → Character}
    {τT Bmask bΦ Z T : ℝ} {s : NaturalState Z Bmask bΦ} {v : O}
    (h : PrefixHighPresented base τT Z s v T) :
    ∃ P : PrefixHighPresentation base s.character s.puncture, v = P.mult := h.2

#print axioms PrefixHighPresented.presentation
#print axioms PrefixHighPresentation.advance
end
end OAI.SevenEighths.Cycle153HighProvider
