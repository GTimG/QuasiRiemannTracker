import Candidate.Cycle63.Density.ActualZeros

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
open Set
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open CenteredMomentNaturalRowSource HeckeFiniteDeletion
local notation "O" => HeckeFamily.O

/-- Every fixed inducing-character list has an admissible fixed ideal list. -/
def FixedUnmarkedDictionary.ofBases {Label : Type*} (base : Label → Character) :
    FixedUnmarkedDictionary Label where
  base := base
  fixedIdeal := fun j => Ideal.span {(72 : O)} ⊓ (base j).modulus
  nonzero := fun j => Ideal.inf_ne_bot_of_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0)) (base j).modulus_ne_bot
  proper := by
    intro j h
    have h72 : (Ideal.span {(72 : O)} : Ideal O) ≤ Ideal.span {(2 : O)} :=
      Ideal.span_singleton_le_span_singleton.mpr ⟨36, by norm_num⟩
    exact CanonicalQuadraticSieve.twoIdeal_maximal.isPrime.ne_top
      (top_le_iff.mp (h ▸ (inf_le_left.trans h72)))
  divides72 := fun _ => inf_le_left
  dividesBase := fun _ => inf_le_right

def naturalRawFamily {Label : Type*} (base : Label → Character) (u : NonzeroElement) :
    Label → Character := fun j => (naturalRow (base j) u.val u.property).character

theorem natural_raw_coefficients (η : Character) (u : NonzeroElement) (I : Ideal O) :
    idealCoeff (naturalRow η u.val u.property).character I =
      idealCoeff ((momentData η).character u) I := by
  rw [NaturalRow.ideal]
  have hc := HeckeRowClosure.idealCoeff_eq_row η ((momentData η).character u)
    (momentData η).m (momentData η).f u.val ((momentData η).character_spec u) I
  simp only [momentData, one_pow, mul_one] at hc
  have hm : CenteredMomentSecondHeightFamily.fixedBadMask = rowMaskElement := by
    unfold CenteredMomentSecondHeightFamily.fixedBadMask rowMaskElement
    ring
  rw [hm]
  exact hc.symm

theorem positive_zeros_eq_of_coefficients (χ ψ : Character)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    (LFunction χ s = 0 ↔ LFunction ψ s = 0) ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) := by
  have hm := coefficient_equality_mask χ ψ hcoeff
  refine ⟨?_, ?_⟩
  · rw [LFunction_eq_of_mask_nonpole χ ψ hm hs hpole, mul_eq_zero]
    exact or_iff_left (factors_ne_zero χ.modulus ψ hs)
  · rcases hpole with h | h
    · exact Or.inl h
    · exact Or.inr (fun hp => h ((principal_iff_of_mask χ ψ hm).mpr hp))

def naturalActualZeroRow {Label : Type*} (base : Label → Character)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroElement) : Prop :=
  ∃ j s, let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem natural_zero_to_literal_dictionary {Label : Type*}
    (base : Label → Character) (reverse : Label → Bool) (a T : ℝ)
    (ha : 33/40 ≤ a) (u : NonzeroElement)
    (hz : naturalActualZeroRow base reverse a T u) :
    orientedActualZeroRow (FixedUnmarkedDictionary.ofBases base).data reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  let ψ := if reverse j then ((momentData (base j)).character u).inverse else (momentData (base j)).character u
  have hc : ∀ I : Ideal O, idealCoeff χ I = idealCoeff ψ I := by
    intro I
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false, naturalRawFamily] using natural_raw_coefficients (base j) u I
    · dsimp [χ, ψ]
      simp only [hr, ite_true]
      rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj]
      dsimp only [naturalRawFamily]
      rw [natural_raw_coefficients]
  have hh := positive_zeros_eq_of_coefficients χ ψ hc (show 0 < s.re by linarith) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- Lemma 2.1, directly for the bounded-conductor natural characters with
coefficients `c_η(I) s_{m₀⁶u}(I)`, including every raw integer row and either
whole-character orientation. The dictionary is fixed before the scale. -/
theorem fixed_natural_dictionary_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ naturalActualZeroRow base reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_dictionary_actual_raw_zero_density
    (FixedUnmarkedDictionary.ofBases base) loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, natural_zero_to_literal_dictionary base reverse a T ha u (hrows u hu).2⟩)

#print axioms fixed_natural_dictionary_raw_density

theorem fixed_natural_dictionary_free_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ Y : ℝ, 1 ≤ Y → ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, rowNorm u ≤ Y ∧
        naturalActualZeroRow base reverse a T ⟨u.val, u.property.1⟩) →
        (rows.card : ℝ) ≤ C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_natural_dictionary_raw_density base loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro reverse a T ha ha' hT Y hY rows hrows
  let embedRow : FreeRow → NonzeroFrequency := fun u => ⟨u.val, u.property.1⟩
  have hinj : Function.Injective embedRow := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : NonzeroFrequency => z.val) h
  have hcard : (rows.image embedRow).card = rows.card := Finset.card_image_of_injective rows hinj
  have hr : ∀ u ∈ rows.image embedRow, rawFrequencyNorm u ≤ Y ∧ naturalActualZeroRow base reverse a T u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have hh := hb reverse a T ha ha' hT Y (zero_lt_one.trans_le hY) (rows.image embedRow) hr
  simpa only [hcard] using hh

#print axioms fixed_natural_dictionary_free_density
end SevenEighths.LocalMoment
end
end OAI
