/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/QuadraticCharacterDescent.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField

variable {F : Type} [Field F] [NumberField F]

theorem descendedCharacter_square (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I) :
    ∀ x : ClassFieldTheory.RayClassGroup (fullModulus f hf),
      (descendedCharacter f hf η) x ^ 2 = 1 := by

  let ψ := descendedCharacter f hf η
  have hpow : ψ ^ 3 = ψ := by
    have huniq := descendedCharacter_unique f hf η (ψ ^ 3) (by
      intro I hI hcop
      have hx : ((ψ (idealClass f hf I hI hcop)) : ℂ) = η I := by
        simp [ψ]
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hx, hq I])
    rw [huniq]
  intro x
  have hx : (ψ x) ^ 3 = ψ x := by
    have := DFunLike.congr_fun hpow x
    rwa [MonoidHom.pow_apply] at this
  have hcancel : (ψ x) ^ 2 * ψ x = 1 * ψ x := by
    rw [one_mul, ← pow_succ]
    exact hx
  exact mul_right_cancel hcancel

theorem descendedCharacter_ne_one (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hn : ¬η.IsPrincipal) :
    descendedCharacter f hf η ≠ 1 := by
  intro h
  apply hn
  intro I hI hcop
  have hx := descendedCharacter_apply_idealClass f hf η I hI hcop
  rw [h] at hx
  simpa using hx.symm

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
