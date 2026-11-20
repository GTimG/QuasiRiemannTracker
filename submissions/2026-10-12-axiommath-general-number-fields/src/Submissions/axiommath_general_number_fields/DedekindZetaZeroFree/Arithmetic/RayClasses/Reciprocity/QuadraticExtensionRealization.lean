/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Reciprocity/QuadraticExtensionRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterFiniteOrder
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticExtensionRealizationData
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticArtinCharacter
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.FinitePrimeClassCompatibility
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.QuadraticCharacterDescent
public import Submissions.axiommath_general_number_fields.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupExistence

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exists_quadraticRayExtensionData
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) : Nonempty (QuadraticRayExtensionData η) := by
  let m := RayBridge.fullModulus f hf
  let ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ := RayBridge.descendedCharacter f hf η
  have hsq : ∀ x, ψ x ^ 2 = 1 := RayBridge.descendedCharacter_square f hf η hq
  have hn' : ψ ≠ 1 := RayBridge.descendedCharacter_ne_one f hf η hn
  obtain ⟨R⟩ := ClassFieldTheory.rayClassSubgroup_existence F m ψ.ker
  obtain ⟨χ, hinj, hsqχ, hagree, hdeg⟩ :=
    quadraticCharacter_of_rayClassRealization m ψ hsq hn' R
  exact ⟨{
    extension := R.extension
    character := χ
    degree_two := hdeg
    character_injective := hinj
    character_square := hsqχ
    unramified := by
      intro p hp
      exact R.unramifiedOutsideModulus.1 p
        ((RayBridge.prime_not_mem_fullModulus_support_iff f hf p).2 hp)
    frobenius := by
      intro p hp Q hQ
      have hv : p ∉ m.finitePart.support :=
        (RayBridge.prime_not_mem_fullModulus_support_iff f hf p).2 hp
      have h1 := R.artin_frobenius p hv Q hQ
      rw [← h1, hagree]
      exact RayBridge.descendedCharacter_apply_finitePrime f hf η p hp }⟩

end DedekindZetaZeroFree.LargeSieve
