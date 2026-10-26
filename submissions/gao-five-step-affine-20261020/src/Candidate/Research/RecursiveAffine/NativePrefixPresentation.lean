/- Initialize the recursive source presentation from the genuine first LOW child
already constructed by native PR67. No root support assumption is introduced. -/
import Candidate.Research.RecursiveAffine.PrefixHighPresentation
import Candidate.Cycle63.Physical.InitialMass.DepthTwoHighPresentation
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentChildRows CenteredMomentSecondExceptionalFamily IdealMobiusDivisorSum

/-- The native first LOW child becomes the first actual recursive prefix node.
Its finite dictionary has the two original ray choices, and its multiplier is
literally the same native child multiplier. -/
def nativePrefixPresentation {η₀ η : Character} {R : Ideal O}
    (P : DepthTwoPresentation η₀ η R) (hR : R ≠ 0) :
    PrefixHighPresentation (secondFixedDictionary η₀) η R := by
  let G : NaturalRow (secondFixedDictionary η₀ P.j₁) P.mult := naturalRow _ _ P.hv
  let F : NaturalRow (P.τ₁ P.j₁.2) 1 := selfNaturalRow _
    (family_element_supported P.χ₁ P.C₁ P.D₁ P.hC₁ P.hD₁ P.U₁ P.τ₁ P.hf₁ P.j₁.2)
  have hGV : (commonFrequencyGenerator P.C₁ P.D₁*nonunitFrequencyGenerator P.C₁ P.D₁ P.U₁)*1 ≠ 0 := by
    rw [mul_one]
    exact (mul_ne_zero_iff.mp P.hv).2
  have hfixed : P.w₁*((commonFrequencyGenerator P.C₁ P.D₁*
      nonunitFrequencyGenerator P.C₁ P.D₁ P.U₁)*1) ≠ 0 := by
    simpa only [mul_one] using P.hv
  refine { mult := P.mult
           masked := { index := P.j₁
                       row := G
                       multiplier_ne_zero := P.hv
                       puncture_ne_zero := hR
                       holes := P.χ₁.modulus*R
                       holes_ne_zero := mul_ne_zero P.χ₁.modulus_ne_bot hR
                       mask := ?_ }
           supported := ?_ }
  · intro I
    have h := actual_retained_fixed_dictionary_mask (childCharacter η₀ P.j₁.1)
      P.χ₁ P.w₁ P.first₁ P.hfirst₁ P.C₁ P.D₁ P.hC₁ P.hD₁ P.hCD₁ P.U₁ P.τ₁ P.hf₁ P.j₁.2 1 F
      (naturalRow _ _ hGV) (naturalRow _ _ hfixed) R hR P.hcop I
    have he : idealCoeff (naturalRow (childCharacter (childCharacter η₀ P.j₁.1) P.j₁.2)
        (P.w₁*((commonFrequencyGenerator P.C₁ P.D₁*nonunitFrequencyGenerator P.C₁ P.D₁ P.U₁)*1))
        hfixed).character I = idealCoeff G.character I := by
      rw [NaturalRow.ideal,G.ideal]
      simp only [G,DepthTwoPresentation.mult,secondFixedDictionary,mul_one]
    refine (congrArg (fun chi=>idealCoeff (excluded chi R) I) P.hη).trans ?_
    change idealCoeff (excluded F.character R) I = _
    refine h.trans ?_
    rw [excluded_ideal _ _ (mul_ne_zero P.χ₁.modulus_ne_bot hR),
      excluded_ideal _ _ (mul_ne_zero P.χ₁.modulus_ne_bot hR),he]
  · intro z hz
    have he : elementCoeff η z=elementCoeff (P.τ₁ P.j₁.2) z :=
      congrArg (fun chi=>elementCoeff chi z) P.hη
    exact family_element_supported P.χ₁ P.C₁ P.D₁ P.hC₁ P.hD₁ P.U₁ P.τ₁ P.hf₁ P.j₁.2 z
      (fun h0=>hz (he.trans h0))

#print axioms nativePrefixPresentation
end
end OAI.SevenEighths.Cycle153HighProvider
