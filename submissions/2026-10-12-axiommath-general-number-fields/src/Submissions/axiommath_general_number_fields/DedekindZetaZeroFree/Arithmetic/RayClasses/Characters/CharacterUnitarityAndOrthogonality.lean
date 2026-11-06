/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/CharacterUnitarityAndOrthogonality.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FiniteOrderAndNormBounds

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField
open DedekindZetaZeroFree.AbelianQuotient

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

theorem rayClassCharacter_norm_eq_one
    (hm : m ≠ ⊥) (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hIm : I ⊔ m = ⊤) :
    ‖η I‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := rayCharacterFiniteOrder F m hm η
  exact Complex.norm_eq_one_of_pow_eq_one (hpow I hI hIm) hn.ne'

theorem rayClassCharacter_norm_le_one
    (hm : m ≠ ⊥) (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : ‖η I‖ ≤ 1 := by
  exact rayCharacter_norm_le_one F m hm η I

theorem rayCharacterDescent_norm_eq_one
    (hm : m ≠ ⊥) (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (ψ : RayIdealClass F m hm →* ℂ)
    (hdescent : ∀ I : Ideal (𝓞 F), η I =
      match rayIdealClass F m hm I with
      | none => 0
      | some c => ψ c)
    (c : RayIdealClass F m hm) : ‖ψ c‖ = 1 := by
  have hpow : ψ c ^ Nat.card (RayIdealClass F m hm) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'

end

end DedekindZetaZeroFree.Hecke
