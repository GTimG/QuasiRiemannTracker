/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Representatives/FinitePrimeClassCompatibility.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.RayBridge

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]

theorem prime_not_mem_fullModulus_support_iff
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    p ∉ (fullModulus f hf).finitePart.support ↔ p.asIdeal ⊔ f = ⊤ := by
  rw [Finsupp.mem_support_iff, fullModulus_finitePart,
    Associates.count_ne_zero_iff_dvd hf p.irreducible, Ideal.dvd_iff_le]
  constructor
  · intro h
    apply (Ideal.isMaximal_def.mp (p.isPrime.isMaximal p.ne_bot)).lt_iff.mp
    exact lt_of_le_of_ne le_sup_left (fun he => h (he ▸ le_sup_right))
  · intro h hle
    have ht : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by
      rw [← h]
      exact sup_le le_rfl hle
    exact p.isPrime.ne_top (top_le_iff.mp ht)

theorem idealClass_eq_rayClassOfFinitePrime
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal ⊔ f = ⊤) :
    idealClass f hf p.asIdeal p.ne_bot hp =
      ClassFieldTheory.rayClassOfFinitePrime (fullModulus f hf) p
        ((prime_not_mem_fullModulus_support_iff f hf p).2 hp) := by
  unfold idealClass ClassFieldTheory.rayClassOfFinitePrime
  congr 1

@[simp] theorem descendedCharacter_apply_finitePrime
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hp : p.asIdeal ⊔ f = ⊤) :
    (descendedCharacter f hf η
      (ClassFieldTheory.rayClassOfFinitePrime (fullModulus f hf) p
        ((prime_not_mem_fullModulus_support_iff f hf p).2 hp)) : ℂ) =
      η p.asIdeal := by
  rw [← idealClass_eq_rayClassOfFinitePrime f hf p hp]
  exact descendedCharacter_apply_idealClass f hf η p.asIdeal p.ne_bot hp

end DedekindZetaZeroFree.LargeSieve.RayBridge

end
