import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeFiniteDeletion ProbePhysical
local notation "O" => HeckeFamily.O

theorem inverse_coefficient_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    ∀ I : Ideal O, idealCoeff χ.inverse I =
      if IsCoprime I χ.inverse.modulus then idealCoeff ψ.inverse I else 0 := by
  intro I
  rw [show χ.inverse.modulus = χ.modulus from rfl]
  rw [idealCoeff_inverse_conj, idealCoeff_inverse_conj, hmask]
  by_cases h : IsCoprime I χ.modulus <;> simp only [h, ite_true, ite_false, map_zero]

theorem positive_zeros_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    (LFunction χ s = 0 ↔ LFunction ψ s = 0) ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) := by
  refine ⟨?_, ?_⟩
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero]
    exact or_iff_left (factors_ne_zero χ.modulus ψ hs)
  · rcases hpole with h | h
    · exact Or.inl h
    · exact Or.inr (fun hp => h ((principal_iff_of_mask χ ψ hmask).mpr hp))

def maskedActualZeroRow {Label : Type*}
    (family : Label → NonzeroFrequency → Character)
    (reverse : Label → Bool) (a T : ℝ) (u : NonzeroFrequency) : Prop :=
  ∃ j s, let χ := if reverse j then (family j u).inverse else family j u
    LFunction χ s = 0 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧ a ≤ s.re ∧ |s.im| ≤ T

theorem masked_zero_to_natural {Label : Type*}
    (base : Label → Character) (family : Label → NonzeroFrequency → Character)
    (hmask : ∀ j u I, idealCoeff (family j u) I =
      if IsCoprime I (family j u).modulus then idealCoeff (naturalRawFamily base u j) I else 0)
    (reverse : Label → Bool) (a T : ℝ) (ha : 0 < a) (u : NonzeroFrequency)
    (hz : maskedActualZeroRow family reverse a T u) :
    naturalActualZeroRow base reverse a T u := by
  obtain ⟨j, s, hz, hpole, hs, ht⟩ := hz
  let χ := if reverse j then (family j u).inverse else family j u
  let ψ := if reverse j then (naturalRawFamily base u j).inverse else naturalRawFamily base u j
  have hm : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
    cases hr : reverse j
    · simpa only [χ, ψ, hr, Bool.false_eq_true, ite_false] using hmask j u
    · simpa only [χ, ψ, hr, ite_true] using inverse_coefficient_mask _ _ (hmask j u)
  have hh := positive_zeros_eq_of_mask_nonpole χ ψ hm (ha.trans_le hs) hpole
  exact ⟨j, s, hh.1.mp hz, hh.2, hs, ht⟩

/-- Moving finite Euler punctures are transported to the fixed natural dictionary.
The representatives may have arbitrarily large moduli. -/
theorem fixed_natural_dictionary_masked_raw_density {Label : Type*} [Fintype Label]
    (base : Label → Character) (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ family : Label → NonzeroFrequency → Character,
      (∀ j u I, idealCoeff (family j u) I =
        if IsCoprime I (family j u).modulus then idealCoeff (naturalRawFamily base u j) I else 0) →
      ∀ reverse : Label → Bool, ∀ a T : ℝ, 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ H ∧ maskedActualZeroRow family reverse a T u) →
        (rows.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J, C, hC, hb⟩ := fixed_natural_dictionary_raw_density base loss hloss
  refine ⟨J, C, hC, ?_⟩
  intro family hmask reverse a T ha ha' hT H hH rows hrows
  exact hb reverse a T ha ha' hT H hH rows (fun u hu =>
    ⟨(hrows u hu).1, masked_zero_to_natural base family hmask reverse a T
      (by linarith) u (hrows u hu).2⟩)

#print axioms fixed_natural_dictionary_masked_raw_density
end SevenEighths.LocalMoment
end
end OAI
