/- Finite physical prefix presentations. Exact native natural-row composition and self-row proofs are retained.
The constructor below advances the literal source Family and puncture; it assumes no terminal count or source estimate. -/
import Candidate.Research.RecursiveAffine.MaskedPrefixArithmetic
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153HighProvider
noncomputable section
open scoped Classical
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentSecondExceptionalFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows IdealMobiusDivisorSum Cycle63Moment CenteredMomentFixedRay
local notation "O" => HeckeFamily.O
/-- Natural rows over a character that is, off a puncture `P`, a natural row of `η` at `u` excluded by `H` are, off a
puncture `Q ⊇ P`, the natural rows of the same two-ray child of `η` at the product row, excluded by `H Q`. -/
theorem masked_natural_row_compose (η σ : Character) (u : O) (F₁ : NaturalRow η u) (P H : Ideal O)
    (hP : P ≠ 0) (hH : H ≠ 0)
    (hσ : ∀ I : Ideal O, idealCoeff (excluded σ P) I = idealCoeff (excluded F₁.character H) I)
    (j : RayCharacter × RayCharacter) (z : O) (G : NaturalRow (secondFixedDictionary σ j) z)
    (G' : NaturalRow (secondFixedDictionary η j) (u*z)) (Q : Ideal O) (hQ : Q ≠ 0) (hPQ : P ∣ Q)
    (I : Ideal O) :
    idealCoeff (excluded G.character Q) I = idealCoeff (excluded G'.character (H*Q)) I := by
  rw [excluded_ideal _ _ hQ, excluded_ideal _ _ (mul_ne_zero hH hQ), IsCoprime.mul_right_iff]
  by_cases hq : IsCoprime I Q
  swap
  · rw [ite_eq_right hq, ite_eq_right (fun h' => hq h'.2)]
  rw [ite_eq_left hq]
  by_cases hs : Supported I
  swap
  · rw [natural_row_ideal_zero_of_not_supported _ _ G I hs, natural_row_ideal_zero_of_not_supported _ _ G' I hs,
      ite_self]
  have h := hσ I
  rw [excluded_ideal _ _ hP, excluded_ideal _ _ hH, ite_eq_left (hq.of_isCoprime_of_dvd_right hPQ)] at h
  have hG : idealCoeff G.character I = idealCoeff σ I*(idealCoeff (primaryRayCharacter j.1) I*
      idealCoeff (primaryRayCharacter j.2) I)*idealRowHom z I := by
    rw [natural_row_supported_ideal _ _ G I hs]
    simp only [secondFixedDictionary, childCharacter, idealCoeff_product]
    ring
  have hG' : idealCoeff G'.character I = idealCoeff η I*idealRowHom u I*(idealCoeff (primaryRayCharacter j.1) I*
      idealCoeff (primaryRayCharacter j.2) I)*idealRowHom z I := by
    rw [natural_row_supported_ideal _ _ G' I hs, idealRowHom_argument_mul]
    simp only [secondFixedDictionary, childCharacter, idealCoeff_product]
    ring
  rw [hG, hG', h]
  by_cases hh : IsCoprime I H
  · rw [ite_eq_left hh, ite_eq_left ⟨hh, hq⟩, natural_row_supported_ideal _ _ F₁ I hs]
  · rw [ite_eq_right hh, ite_eq_right (fun h' => hh h'.1), zero_mul, zero_mul]

/-- A second-stage character has nonzero coefficients only at elements with supported ideals: its coefficients are the
row twist of a child character, whose modulus lies below `(12)`. -/
theorem family_element_supported (η : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (ξ : RayCharacter) (n : O) (hn : elementCoeff (τ ξ) n ≠ 0) : Supported (Ideal.span {n}) := by
  have hchild : elementCoeff (childCharacter η ξ) n ≠ 0 := by
    intro h0
    apply hn
    rw [hf.element_eq ξ n]
    change elementCoeff (childCharacter η ξ) n*_ = 0
    rw [h0, zero_mul]
  have hcop := old_coefficient_nonzero_coprime _ n hchild
  rw [childCharacter_modulus] at hcop
  have h12 : IsCoprime (Ideal.span {n}) (Ideal.span {(12 : O)}) :=
    hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr inf_le_right)
  have h3 : goodLambda ∣ (3 : O) := CubicEisenstein.halfPrimary_lambda_dvd_three
  exact ProbePhysical.supported_of_coprime_bad 12 n (h3.trans ⟨4, by norm_num⟩) ⟨6, by norm_num⟩
    ((Ideal.isCoprime_span_singleton_iff _ _).mp h12).symm

/-- A second-stage character vanishes at zero. -/
theorem family_element_zero (η : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (τ : RayCharacter → Character) (hf : Family η C D hC hD U τ)
    (ξ : RayCharacter) : elementCoeff (τ ξ) 0 = 0 := by
  by_contra h
  have hs := family_element_supported η C D hC hD U τ hf ξ 0 h
  exact hs.1 (by rw [Ideal.span_singleton_zero, Ideal.zero_eq_bot])

/-- A character whose nonzero coefficients sit at elements with supported ideals is a natural row of itself at the
row `1`. -/
def selfNaturalRow (σ : Character) (hσ : ∀ n : O, elementCoeff σ n ≠ 0 → Supported (Ideal.span {n})) :
    NaturalRow σ 1 where
  character := σ
  modulus_bound := by
    have hm : 1 ≤ (Ideal.span {fixedBadMask} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    have h72 : 1 ≤ (Ideal.span {(72 : O)} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    simp only [rowConductorBound, Ideal.span_singleton_one, Ideal.absNorm_top, one_pow, mul_one]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hm)).trans
      (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h72))
  element := fun n => by
    by_cases hs : Supported (Ideal.span {n})
    · have hcop : IsCoprime (Ideal.span {n}) (Ideal.span {fixedBadMask}) :=
        (Ideal.isCoprime_span_singleton_iff _ _).mpr (fixedBadMask_coprime n hs).symm
      have hrow := idealRowHom_sixth_mask fixedBadMask (Ideal.span {n}) hs
      rw [ite_eq_left hcop] at hrow
      change elementCoeff _ n = elementCoeff _ n*idealRowHom (fixedBadMask^6*1^4*1) _
      simp only [one_pow, mul_one]
      change elementCoeff _ n = elementCoeff _ n*idealRowHom (fixedBadMask^6) (Ideal.span {n})
      rw [hrow, mul_one]
    · have hz : elementCoeff σ n = 0 := by
        by_contra h
        exact hs (hσ n h)
      change elementCoeff _ n = elementCoeff _ n*idealRowHom _ _
      rw [hz, zero_mul]

/-- The natural row of a character at the row `1` built by `selfNaturalRow` has the character itself. -/
theorem selfNaturalRow_character (σ : Character) (hσ : ∀ n : O, elementCoeff σ n ≠ 0 → Supported (Ideal.span {n})) :
    (selfNaturalRow σ hσ).character = σ := rfl

/-- The original finite fixed dictionary, actual accumulated multiplier and moving Euler holes
present the current physical source character. This is a coefficient identity, not a bound. -/
structure MaskedPrefixPresentation {Base : Type} (base : Base → Character)
    (η : Character) (puncture : Ideal O) (v : O) where
  index : Base
  row : NaturalRow (base index) v
  multiplier_ne_zero : v ≠ 0
  puncture_ne_zero : puncture ≠ 0
  holes : Ideal O
  holes_ne_zero : holes ≠ 0
  mask : ∀ I : Ideal O, idealCoeff (excluded η puncture) I =
    idealCoeff (excluded row.character holes) I

/-- One more fixed two-ray transform extends a fixed finite dictionary. -/
def extendFixedDictionary {Base : Type} (base : Base → Character)
    (j : Base × (RayCharacter × RayCharacter)) : Character :=
  secondFixedDictionary (base j.1) j.2

/-- The literal local multiplier of the next physical common source. -/
def localSourceMultiplier (w : O) (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  w*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)

/-- Advance a presentation through the actual first column and actual second common family.
The child puncture and its incidence with old holes are explicit. Its new dictionary index
records the two actual ray choices; its multiplier is the old multiplier times w*G*V.
Residual allocations and whole-slot deletions keep this character and introduce no new index. -/
def MaskedPrefixPresentation.advance {Base : Type} {base : Base → Character}
    {η : Character} {P : Ideal O} {v : O} (p : MaskedPrefixPresentation base η P v)
    (j : RayCharacter × RayCharacter) (χ : Character) (w : O)
    (first : NaturalRow (childCharacter η j.1) w)
    (hfirst : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff first.character I else 0)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter → Character) (hf : Family χ C D hC hD U τ)
    (hw : localSourceMultiplier w C D U ≠ 0)
    (Q : Ideal O) (hQ : Q ≠ 0) (hPQ : P ∣ χ.modulus*Q)
    (hcop : ∀ I : Ideal O, IsCoprime I Q → IsCoprime I C) :
    MaskedPrefixPresentation (extendFixedDictionary base) (τ j.2) Q
      (v*localSourceMultiplier w C D U) := by
  let u := localSourceMultiplier w C D U
  have hu : u ≠ 0 := hw
  let F : NaturalRow (τ j.2) 1 := selfNaturalRow (τ j.2)
    (family_element_supported χ C D hC hD U τ hf j.2)
  let G : NaturalRow (secondFixedDictionary η j) u := naturalRow _ u hu
  let G' : NaturalRow (extendFixedDictionary base (p.index,j)) (v*u) :=
    naturalRow _ (v*u) (mul_ne_zero p.multiplier_ne_zero hu)
  have hGV : (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*1 ≠ 0 := by
    rw [mul_one]
    exact (mul_ne_zero_iff.mp hu).2
  have hfixed : w*((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*1) ≠ 0 := by
    simpa only [localSourceMultiplier, mul_one] using hw
  have hlocal : ∀ I : Ideal O, idealCoeff (excluded (τ j.2) Q) I =
      idealCoeff (excluded G.character (χ.modulus*Q)) I := by
    intro I
    have h := actual_retained_fixed_dictionary_mask (childCharacter η j.1) χ w first hfirst
      C D hC hD hCD U τ hf j.2 1 F
      (naturalRow _ _ hGV) (naturalRow _ _ hfixed) Q hQ hcop I
    have he : idealCoeff (naturalRow (childCharacter (childCharacter η j.1) j.2)
        (w*((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*1)) hfixed).character I =
        idealCoeff G.character I := by
      rw [NaturalRow.ideal, G.ideal]
      simp only [u, localSourceMultiplier, mul_one, secondFixedDictionary]
    change idealCoeff (excluded F.character Q) I = _
    refine h.trans ?_
    rw [excluded_ideal _ _ (mul_ne_zero χ.modulus_ne_bot hQ),
      excluded_ideal _ _ (mul_ne_zero χ.modulus_ne_bot hQ), he]
  have houter := masked_natural_row_compose (base p.index) η v p.row P p.holes
    p.puncture_ne_zero p.holes_ne_zero p.mask j u G G' (χ.modulus*Q)
      (mul_ne_zero χ.modulus_ne_bot hQ) hPQ
  refine ⟨(p.index,j),G',mul_ne_zero p.multiplier_ne_zero hu,hQ,
    p.holes*(χ.modulus*Q),mul_ne_zero p.holes_ne_zero (mul_ne_zero χ.modulus_ne_bot hQ),?_⟩
  intro I
  exact (hlocal I).trans (houter I)

#print axioms MaskedPrefixPresentation.advance
end
end OAI.SevenEighths.Cycle153HighProvider
