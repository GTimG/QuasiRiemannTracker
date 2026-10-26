import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Density.NaturalEndpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
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

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
