/- The presentation of a natural state by a child multiplier in the four-ray dictionary: the data of a first-level
child whose second-stage character is the character of the state. Released under Apache 2.0. -/
import Candidate.Cycle63.Moment.DepthTwoDictionary
import Candidate.Cycle63.Moment.LowBranch.WidenedState

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum CenteredMomentEnergyState
local notation "O" => HeckeFamily.O

/-- The state `s` is presented by the multiplier `v₁` in the four-ray dictionary of `η₀` at the zero height `T`.
The height `T` is `Z^τT`. The character of `s` is the second-stage character `τ₁ j₁.2` of a first-level
child: the child's character `χ₁` is, off its modulus, a natural row of `childCharacter η₀ j₁.1` at the first-level
row `w₁`, and `τ₁` is a family of `χ₁` over the common ideals `(C₁, D₁)` of equal prime supports with inactive set
`U₁`. The multiplier `v₁` is the child multiplier `w₁ G V` and is not zero, and every ideal coprime to the puncture of
`s` is coprime to `C₁`. -/
def DepthTwoPresented (τT : ℝ) {Bmask bΦ : ℝ} (η₀ : Character) (Z : ℝ) (s : NaturalState Z Bmask bΦ) (v₁ : O)
    (T : ℝ) : Prop :=
  (Z^τT ≤ T ∧ T ≤ Z^τT) ∧ ∃ (j₁ : RayCharacter × RayCharacter) (χ₁ : Character) (w₁ : O) (C₁ D₁ : Ideal O)
      (hC₁ : Supported C₁) (hD₁ : Supported D₁) (U₁ : Finset (CommonIndex C₁ D₁)) (τ₁ : RayCharacter → Character),
    (∃ first₁ : NaturalRow (childCharacter η₀ j₁.1) w₁, ∀ I : Ideal O,
      idealCoeff χ₁ I = if IsCoprime I χ₁.modulus then idealCoeff first₁.character I else 0) ∧
    primeSupport C₁ = primeSupport D₁ ∧ Family χ₁ C₁ D₁ hC₁ hD₁ U₁ τ₁ ∧
    v₁ = w₁*(commonFrequencyGenerator C₁ D₁*nonunitFrequencyGenerator C₁ D₁ U₁) ∧ v₁ ≠ 0 ∧
    s.character = τ₁ j₁.2 ∧ (∀ I : Ideal O, IsCoprime I s.puncture → IsCoprime I C₁)

/-- A presented state stays presented when its character width is widened: widening changes neither the character
nor the puncture. -/
theorem DepthTwoPresented.widen {τT Bmask bΦ Z T : ℝ} {η₀ : Character} {s : NaturalState Z Bmask bΦ} {v₁ : O}
    (h : DepthTwoPresented τT η₀ Z s v₁ T) (W : ℝ) (hW : s.width ≤ W) :
    DepthTwoPresented τT η₀ Z (LowBranch.widenState s W hW) v₁ T := h

/-- An ideal coprime to an ideal `D` is coprime to every nonzero ideal `C` with the prime support of `D`. -/
theorem isCoprime_of_primeSupport_eq {I C D : Ideal O} (hC : C ≠ 0)
    (hCD : primeSupport C = primeSupport D) (h : IsCoprime I D) : IsCoprime I C := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hCP : C ≤ P := le_sup_right.trans hle
  have hIP : I ≤ P := le_sup_left.trans hle
  have hP0 : P ≠ ⊥ := by
    intro h0
    apply hC
    rw [Ideal.zero_eq_bot]
    exact le_bot_iff.mp (h0 ▸ hCP)
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hPmax.isPrime
  have hPC : P ∣ C := Ideal.dvd_iff_le.mpr hCP
  obtain ⟨Q, hQ, hPQ⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hC hPprime.irreducible hPC
  have hQP : P = Q := associated_iff_eq.mp hPQ
  have hmemC : P ∈ primeSupport C := by
    unfold primeSupport
    rw [Multiset.mem_toFinset, hQP]
    exact hQ
  have hmemD : P ∈ primeSupport D := hCD ▸ hmemC
  have hPD : P ∣ D := by
    unfold primeSupport at hmemD
    rw [Multiset.mem_toFinset] at hmemD
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmemD
  have hDP : D ≤ P := Ideal.le_of_dvd hPD
  exact hPmax.ne_top (eq_top_iff.mpr (h ▸ sup_le hIP hDP))

end
end OAI.SevenEighths.Cycle63Moment
